-- | Tools for implementing primitive operations -- essentially an
--   object-language/meta-language FFI.
{-# LANGUAGE
  FlexibleInstances
 #-}
module BasisUtils (
  -- | * Initial environment entries
  Entry,
  -- ** Entry constructors
  -- *** Values
  fun, val, pfun, pval, binArith,
  -- *** Types
  typeC, typeA, typeT, primtype,
  -- *** Modules, exceptions, and arbitrary declarations
  submod, primexn, src,
  -- ** Sugar operators for entry construction
  (-:), (-::), (-=),
  -- ** Environment construction
  basis2venv, basis2tenv,

  -- * Function embedding
  MkFun(..), baseMkFun, vapp,

  -- * Re-exports
  text, Uid(..),
) where

import Dynamics (E, addVal, addMod)
import Env (GenEmpty(..))
import Parser (pt, pds)
import Ppr (ppr, text)
import Statics (S, env0, tcDecls, addVal, addType, addExn, addMod)
import Syntax
import Util
import Value (Valuable(..), FunName(..), Value(..))

-- | An entry in the initial environment
data Entry
  -- | A value entry has a name, separate types for each sublanguage
  --   (may be blank), and a value
  = ValEn {
    enName  :: Lid,
    enCType :: String,
    enAType :: String,
    enValue :: Value
  }
  -- | A declaration entry is just source code
  | DecEn {
    enSrc   :: String
  }
  -- | A type entry associates a tycon name with information about it
  | TypEn {
    enName  :: Lid,
    enTyTag :: TyTag
  }
  -- | A module entry associates a module name with a list of entries
  | ModEn {
    enModName :: Uid,
    enEnts    :: [Entry]
  }
  -- | An exception entry associates an exception name with its unique id
  | ExnEn {
    enExnId   :: ExnId,
    enExnType :: String
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
      next v = case n of
        FNAnonymous doc -> FNAnonymous doc
        FNNamed docs    -> FNNamed (docs ++ [ppr v])

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

-- | Make a value entry for a Haskell function, given a names and types
--   for the sublanguages.  (Leave blank to leave the binding out of
--   that language.
fun :: (MkFun r, Valuable v) =>
       String -> String -> String -> (v -> r) -> Entry
fun name cty aty f = ValEn (Lid name) cty aty (mkFun (FNNamed [text name]) f)

-- | Make a value entry for a Haskell non-function.
val :: Valuable v => String -> String -> String -> v -> Entry
val name cty aty v = ValEn (Lid name) cty aty (vinj v)

-- | Make a value entry for a value that is polymorphic in the object
--   language: appends the specified number of type lambdas
pval :: Valuable v => Int -> String -> String -> String -> v -> Entry
pval 0 name cty aty v = val name cty aty v
pval n name cty aty v = mkTyAbs (pval (n - 1) name cty aty v)

-- | Make a value entry for a function that is polymorphic in the object
--   language: appends the specified number of type lambdas
pfun :: (MkFun r, Valuable v) =>
        Int -> String -> String -> String -> (v -> r) -> Entry
pfun 0 name cty aty f = fun name cty aty f
pfun n name cty aty f = mkTyAbs (pfun (n - 1) name cty aty f)

mkTyAbs :: Entry -> Entry
mkTyAbs entry =
  let v     = enValue entry in
  entry { enValue = VaSus (FNNamed [ppr (enName entry)]) (return v) }

class TypeBuilder r where
  -- | @String String ... -> Entry@ variadic function for building
  --   source-level A type entries
  typeA :: String -> r
  -- | @String String ... -> Entry@ variadic function for building
  --   source-level C type entries
  typeC :: String -> r
  -- | @String String ... -> Entry@ variadic function for building
  --   source-level shared type entries
  typeT :: String -> r
  -- | @String String ... -> Entry@ variadic function for building
  --   source-level declaration entries
  src   :: String -> r

instance TypeBuilder Entry where
  typeC      = DecEn . ("type[C] " ++)
  typeA      = DecEn . ("type[A] " ++)
  typeT      = DecEn . ("type[*] " ++)
  src        = DecEn

instance TypeBuilder r => TypeBuilder (String -> r) where
  typeC s    = typeC . (s ++) . ('\n' :)
  typeA s    = typeA . (s ++) . ('\n' :)
  typeT s    = typeT . (s ++) . ('\n' :)
  src s      = src   . (s ++) . ('\n' :)

-- | Creates a module entry
submod :: String -> [Entry] -> Entry
submod  = ModEn . Uid

-- | Creates a primitve type entry, binding a name to a type tag
--   (which is usually defined in Syntax.hs)
primtype  :: String -> TyTag -> Entry
primtype   = TypEn . Lid

-- | Creates a primitve exception entry
primexn :: ExnId -> String -> Entry
primexn ei t = ExnEn { enExnId = ei, enExnType = t }

-- | Application
(-:), (-=) :: (a -> b) -> a -> b
(-:) = ($)
(-=) = ($)
-- | Application twice, for giving the same type in C and A
(-::) :: (a -> a -> b) -> a -> b
f -:: x = f x x
infixl 5 -:, -::
infixr 0 -=

-- | Instance of 'fun' for making binary arithmetic functions
binArith :: String -> (Integer -> Integer -> Integer) -> Entry
binArith name = fun name "int -> int -> int" "int -> int -> int"

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
  add e _ = return e

-- | Build the static environment
basis2tenv :: Monad m => [Entry] -> m S
basis2tenv  = foldM each env0 where
  each gg0 (ValEn { enName = n, enCType = ct, enAType = at }) = do
    gg1 <- if null ct
      then return gg0
      else Statics.addVal gg0 n (pt ct :: Type () C)
    gg2 <- if null at
      then return gg1
      else Statics.addVal gg1 n (pt at :: Type () A)
    return gg2
  each gg0 (DecEn { enSrc = s }) = do
    (gg1, _, _) <- tcDecls False gg0 (pds s)
    return gg1
  each gg0 (TypEn { enName = n, enTyTag = i }) =
    return (Statics.addType gg0 n i)
  each gg0 (ModEn { enModName = n, enEnts = es }) =
    Statics.addMod gg0 n $ \gg' -> foldM each gg' es
  each gg0 (ExnEn { enExnId = ExnId { eiName = n, eiIndex = ix, eiLang = LC },
                    enExnType = s }) =
    Statics.addExn gg0 n (pt_maybe s) C ix
  each gg0 (ExnEn { enExnId = ExnId { eiName = n, eiIndex = ix, eiLang = LA },
                    enExnType = s }) =
    Statics.addExn gg0 n (pt_maybe s) A ix

pt_maybe :: Language w => String -> Maybe (Type () w)
pt_maybe "" = Nothing
pt_maybe s  = Just (pt s)

