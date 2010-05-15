-- | Tools for implementing primitive operations -- essentially an
--   object-language/meta-language FFI.
{-# LANGUAGE
      FlexibleInstances,
      QuasiQuotes #-}
module BasisUtils (
  -- | * Initial environment entries
  Entry,
  -- ** Entry constructors
  -- *** Values
  fun, val, binArith,
  -- *** Types
  dec, typ, primtype,
  -- *** Modules, exceptions, and arbitrary declarations
  submod, primexn,
  -- ** Sugar operators for entry construction
  (-:), (-=),
  -- ** Default location for entries
  _loc,
  module Loc,
  -- ** Environment construction
  basis2venv, basis2tenv,

  -- * Function embedding
  MkFun(..), baseMkFun, vapp,

  -- * Re-exports
  text, Uid(..),
) where

import Dynamics (E, addVal, addMod, addExn)
import Env (GenEmpty(..))
import Parser (ptd)
import Ppr (ppr, pprPrec, text, precApp)
import Quasi
import Statics (S, env0, tcDecls, addVal, addType, addExn, addMod)
import Syntax
import qualified Syntax.Notable
import qualified Syntax.Decl
import Type (TyCon)
import Loc (Loc(Loc), mkBogus, setLoc)
import Util
import Value (Valuable(..), FunName(..), funNameDocs, Value(..),
              ExnId(..))

-- | Default source location for primitives
_loc :: Loc
_loc  = mkBogus "<primitive>"

-- | An entry in the initial environment
data Entry
  -- | A value entry has a name, a types, and a value
  = ValEn {
    enName  :: Lid,
    enType  :: Type (),
    enValue :: Value
  }
  -- | A declaration entry
  | DecEn {
    enSrc   :: Decl ()
  }
  -- | A type entry associates a tycon name with information about it
  | TypEn {
    enName  :: Lid,
    enTyCon :: TyCon
  }
  -- | A module entry associates a module name with a list of entries
  | ModEn {
    enModName :: Uid,
    enEnts    :: [Entry]
  }
  -- | An exception entry associates an exception name with its unique id
  | ExnEn {
    enExnId   :: ExnId,
    enExnType :: Maybe (Type ())
  }

-- | Type class for embedding Haskell functions as object language
--   values.  Dispatches on return type @r@.
class MkFun r where
  mkFun :: Valuable v => FunName -> (v -> r) -> Value

-- | Recursive case is functions that return functions: accept
--   one argument, then look for more
instance (Valuable v, MkFun r) => MkFun (v -> r) where
  mkFun n f = VaFun n $ \v ->
    vprjM v >>! mkFun (next v) . f
    where
      next v = FNAnonymous (funNameDocs n ++ [pprPrec precApp v])

-- Base cases for various return types

-- | Base case for functions returning in the 'IO' monad
instance Valuable r => MkFun (IO r) where
  mkFun n f = VaFun n $ \v -> vprjM v >>= f >>! vinj

-- | Base case for functions that already return 'Value'
instance MkFun Value where
  mkFun n f = VaFun n $ \v -> vprjM v >>! f

instance MkFun Integer  where mkFun = baseMkFun
instance MkFun Double   where mkFun = baseMkFun
instance MkFun Char     where mkFun = baseMkFun
instance MkFun Bool     where mkFun = baseMkFun
instance MkFun ()       where mkFun = baseMkFun
instance (Valuable a, MkFun a) =>
         MkFun [a]      where mkFun = baseMkFun
instance (Valuable a, Valuable b, MkFun a, MkFun b) =>
         MkFun (a, b)   where mkFun = baseMkFun

baseMkFun :: (Valuable a, Valuable b) => FunName -> (a -> b) -> Value
baseMkFun n f = VaFun n $ \v -> vprjM v >>! vinj . f

-- | Make a value entry for a Haskell non-function.
val :: Valuable v => String -> Type () -> v -> Entry
val name t v = ValEn (Lid name) t (vinj v)

-- | Make a value entry for a Haskell function, given a names and types
--   for the sublanguages.  (Leave blank to leave the binding out of
--   that language.
fun :: (MkFun r, Valuable v) =>
       String -> Type () -> (v -> r) -> Entry
fun name t f = ValEn (Lid name) t (mkFun (FNNamed (ppr (Lid name))) f)

typ :: String -> Entry
typ s      = DecEn [$dc| type $tydec:td |] where td = ptd s

-- | Creates a declaration entry
dec :: Decl () -> Entry
dec  = DecEn

-- | Creates a module entry
submod :: String -> [Entry] -> Entry
submod  = ModEn . Uid

-- | Creates a primitve type entry, binding a name to a type tag
--   (which is usually defined in Syntax.hs)
primtype  :: String -> TyCon -> Entry
primtype   = TypEn . Lid

-- | Creates a primitve exception entry
primexn :: ExnId -> Maybe (Type ()) -> Entry
primexn ei t = ExnEn { enExnId = ei, enExnType = t }

-- | Application
(-:), (-=) :: (a -> b) -> a -> b
(-:) = ($)
(-=) = ($)
-- | Application twice, for giving the same type in C and A
infixl 5 -:
infixr 0 -=

-- | Instance of 'fun' for making binary arithmetic functions
binArith :: String -> (Integer -> Integer -> Integer) -> Entry
binArith name = fun name [$ty| int -> int -> int |]

-- | Apply an object language function (as a 'Value')
vapp :: Valuable a => Value -> a -> IO Value
vapp  = \(VaFun _ f) x -> f (vinj x)
infixr 0 `vapp`

-- | Build the dynamic environment
basis2venv :: Monad m => [Entry] -> m E
basis2venv es = foldM add genEmpty es where
  add :: Monad m => E -> Entry -> m E
  add e (ValEn { enName = n, enValue = v })
          = return (Dynamics.addVal e n v)
  add e (ModEn { enModName = n, enEnts = es' })
          = Dynamics.addMod e n `liftM` basis2venv es'
  add e (ExnEn { enExnId = exnId })
          = return (Dynamics.addExn e exnId)
  add e _ = return e

-- | Build the static environment
basis2tenv :: Monad m => [Entry] -> m S
basis2tenv  = foldM each env0 where
  each gg0 (ValEn { enName = n, enType = t }) = do
    Statics.addVal gg0 n t
  each gg0 (DecEn { enSrc = decl }) = do
    (gg1, _, _) <- tcDecls False gg0 [decl]
    return gg1
  each gg0 (TypEn { enName = n, enTyCon = i }) =
    return (Statics.addType gg0 n i)
  each gg0 (ModEn { enModName = n, enEnts = es }) =
    Statics.addMod gg0 n $ \gg' -> foldM each gg' es
  each gg0 (ExnEn { enExnId = ExnId { eiName = n }, enExnType = t }) =
    Statics.addExn gg0 n t

