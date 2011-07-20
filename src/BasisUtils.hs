-- | Tools for implementing primitive operations -- essentially an
--   object-language/meta-language FFI.
module BasisUtils (
  -- | * Initial environment entries
  Entry,
  -- ** Entry constructors
  -- *** Values
  fun, val, binArith,
  -- *** Types
  dec, typ, primtype,
  -- *** Modules
  submod,
  -- ** Sugar operators for entry construction
  (-:), (-=),
  -- ** Default location for entries
  _loc,
  module Data.Loc,
  -- ** Environment construction
  basis2renv, basis2tenv, basis2venv,

  -- * Function embedding
  MkFun(..), baseMkFun, vapp,

  -- * Re-exports
  text, Id(..),
  module Meta.Quasi,
) where

import Util
import Util.MonadRef
import Dynamics (E, addVal, addMod)
import Env (GenEmpty(..), domain)
import Error (MonadAlmsError, almsBug, throwAlms, Phase(DynamicsPhase))
import Meta.Quasi
import Syntax.Parser (ptd)
import Syntax.Ppr (ppr, pprPrec, text, precApp)
import Statics
import Statics.Rename as Rename
import AST
import Type (TyCon, tcName, tcCons)
import Data.Loc (Loc(Loc), mkBogus, setLoc)
import Value (Valuable(..), FunName(..), funNameDocs, Value(..))

import Prelude ()

-- | Kind of identifier used in this module
type R = Raw

-- | The default location for primitive bindings
_loc  :: Loc
_loc   = mkBogus "<primitive>"

-- | An entry in the initial environment
data Entry i
  -- | A value entry has a name, a types, and a value
  = ValEn {
    enVarName :: VarId i,
    enType    :: Type i,
    enValue   :: Value
  }
  -- | A declaration entry
  | DecEn {
    enSrc     :: SigItem i
  }
  -- | A type entry associates a tycon name with information about it
  | TypEn {
    enTypName :: TypId i,
    enTyCon   :: TyCon
  }
  -- | A module entry associates a module name with a list of entries
  | ModEn {
    enModName :: ModId i,
    enEnts    :: [Entry i]
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
val :: Valuable v => String -> Type R -> v -> Entry Raw
val name t v = ValEn (ident name) t (vinj v)

-- | Make a value entry for a Haskell function, given a names and types
--   for the sublanguages.  (Leave blank to leave the binding out of
--   that language.
fun :: (MkFun r, Valuable v) =>
       String -> Type R -> (v -> r) -> Entry Raw
fun name t f = ValEn vid t (mkFun (FNNamed (ppr vid)) f)
  where vid = ident name

typ :: String -> Entry Raw
typ s = DecEn [sgQ| type $tydec:td |] where td = ptd s

-- | Creates a declaration entry
dec :: SigItem R -> Entry Raw
dec  = DecEn

-- | Creates a module entry
submod :: String -> [Entry Raw] -> Entry Raw
submod  = ModEn . ident

-- | Creates a primitive type entry, binding a name to a type tag
--   (which is usually defined in AST.hs)
primtype  :: String -> TyCon -> Entry Raw
primtype   = TypEn . ident

-- | Application
(-:), (-=) :: (a -> b) -> a -> b
(-:) = ($)
(-=) = ($)
-- | Application twice, for giving the same type in C and A
infixl 5 -:
infixr 0 -=

-- | Instance of 'fun' for making binary arithmetic functions
binArith :: String -> (Integer -> Integer -> Integer) -> Entry Raw
binArith name = fun name [ty| int -> int -> int |]

-- | Apply an object language function (as a 'Value')
vapp :: Valuable a => Value -> a -> IO Value
vapp (VaFun _ f) x = f (vinj x)
vapp _           _ = throwAlms
  $ almsBug DynamicsPhase "vapp" "applied non-function"
infixr 0 `vapp`

-- | Build the renaming environment and rename the entries
basis2renv :: MonadAlmsError m =>
              [Entry Raw] -> m ([Entry Renamed], RenameState)
basis2renv =
  runRenamingM False _loc renameState0 . renameMapM each where
  each ValEn { enVarName = u, enType = t, enValue = v } = do
    u' <- Rename.addVal u
    t' <- renameType t
    return ValEn { enVarName = u', enType = t', enValue = v }
  each DecEn { enSrc = d } = do
    d' <- renameSigItem d
    return DecEn { enSrc = d' }
  each TypEn { enTypName = l, enTyCon = tc } = do
    l' <- Rename.addType l (idTag (jname (tcName tc)))
                           (trivialRename <$> domain (tcCons tc))
    return TypEn { enTypName = l', enTyCon = tc }
  each ModEn { enModName = u, enEnts = es } = do
    (u', es') <- Rename.addMod u $ renameMapM each es
    return ModEn { enModName = u', enEnts = es' }

-- | Build the static environment
basis2tenv :: (MonadAlmsError m, MonadRef r m) =>
              StaticsState r -> [Entry Renamed] -> m (StaticsState r)
basis2tenv ss0 entries = addSignature ss1 sigexp
  where
    ss1             = foldl' (uncurry . addPrimType) ss0 prims
    (sigexp, prims) = evalRWS (eachEntries entries) [] (0 :: Int)
    eachEntries es  = do
      sigitems <- mapM eachEntry es
      return [seQ|+ sig $list:sigitems end |]
    eachEntry ValEn { enVarName = n, enType = t }
      = return [sgQ|+ val $vid:n : $t |]
    eachEntry DecEn { enSrc = sigitem }
      = return sigitem
    eachEntry TypEn { enTypName = n, enTyCon = tc }
      = do
        ix <- get
        put (ix + 1)
        let n' = ident (idName n ++ "_prim" ++ show ix)
        tell [(n', tc)]
        return [sgQ|+ type $tid:n = type $tid:n' |]
    eachEntry ModEn { enModName = n, enEnts = es }
      = do
        sig <- eachEntries es
        return [sgQ|+ module $mid:n : $sig |]

-- | Build the dynamic environment
basis2venv :: MonadAlmsError m => [Entry Renamed] -> m E
basis2venv es = foldM add genEmpty es where
  add :: MonadAlmsError m => E -> Entry Renamed -> m E
  add e (ValEn { enVarName = n, enValue = v })
          = return (Dynamics.addVal e n v)
  add e (ModEn { enModName = n, enEnts = es' })
          = Dynamics.addMod e n `liftM` basis2venv es'
  add e _ = return e

