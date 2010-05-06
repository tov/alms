-- | The internal representation of types, created by the type checker
--   from the syntactic types in 'Syntax.Type'.
{-# LANGUAGE
      DeriveDataTypeable,
      DeriveFunctor,
      FlexibleInstances,
      TypeFamilies #-}
module Type (
  -- * Representation of types
  Type(..), TyCon(..), tyApp,
  -- * Type reduction
  -- ** Head reduction
  isHeadNormalType, headReduceType, headNormalizeTypeK, headNormalizeType,
  -- ** Deep reduction
  isNormalType, reduceType, normalizeTypeK, normalizeType,
  -- * Miscellaneous type operations
  castableType, typeToStx,
  -- * Built-in types
  -- ** Type constructors
  mkTC,
  tcUnit, tcInt, tcFloat, tcString,
  tcExn, tcTuple, tcUn, tcAf,
  tcSend, tcRecv, tcSelect, tcFollow, tcDual,
  -- ** Types
  tyNulOp, tyUnOp, tyBinOp, tyUnit, tyTuple, tyArr, tyLol,
  -- * Re-exports
  module Syntax.Ident,
  module Syntax.Kind,
  module Syntax.POClass,
  Stx.Quant(..),
) where

import qualified Env
import Ppr (Ppr(..))
import Syntax.Ident
import Syntax.Kind
import Syntax.POClass
import qualified Syntax as Stx
import Util

import Data.Generics (Typeable, Data)
import Text.Show.Functions ()
import Control.Applicative

-- | The internal representation of a type
data Type
  -- | A type variable
  = TyVar TyVar
  -- | The application of a type constructor (possibly nullary); the
  --   third field caches the next head-reduction step if the type
  --   is not head-normal -- note that substitution invalidates this
  --   cache.  Use 'tyApp' to construct a type application that
  --   (re)initializes the cache.
  | TyApp TyCon [Type] (Maybe Type)
  -- | An arrow type, including qualifier expression
  | TyArr (QDen TyVar) Type Type
  -- | A quantified (all or ex) type
  | TyQu  Stx.Quant TyVar Type
  -- | A recursive (mu) type
  | TyMu  TyVar Type
  deriving (Typeable, Data, Show)

-- | Information about a type constructor
data TyCon
  = TyCon {
      -- | Unique identifier used for equality
      tcId        :: Integer,
      -- | Printable name (not yet unique)
      tcName      :: QLid,
      -- | Bounds and variances for parameters
      tcArity     :: [(QLit, Variance)],
      -- | Qualifier as a function of parameters
      tcQual      :: QDen Int,
      -- | For pattern-matchable types, the data constructors
      tcCons      :: Env.Env Uid (Maybe Type),
      -- | For type synonyms, the next head reduction
      tcNext      :: Maybe ([Type] -> Maybe Type)
    }
  deriving (Typeable, Data, Show)

instance Eq TyCon where
  tc == tc'  =  tcId tc == tcId tc'

instance Ord TyCon where
  compare tc tc'  = compare (tcId tc) (tcId tc')

instance Ppr Type where
  pprPrec p = pprPrec p . typeToStx

-- | Creates a type application, initializing the head-reduction cache
tyApp :: TyCon -> [Type] -> Type
tyApp tc ts = TyApp tc ts (tcNext tc >>= ($ ts))

-- | Takes one head reduction step.  Returns 'Nothing' if the type is
--   already head-normal.
headReduceType :: Type -> Maybe Type
headReduceType (TyApp _ _ next) = next
headReduceType _                = Nothing

-- | Is the type head-normal?  A type is head-normal unless its
--   top-level constructor is a type operator, which can take a step.
isHeadNormalType :: Type -> Bool
isHeadNormalType t = case headReduceType t of
  Nothing -> True
  Just _  -> False

-- | Head reduces a type until it is head-normal, given some amount of fuel
headNormalizeTypeF :: Type -> Fuel Type
headNormalizeTypeF t = case headReduceType t of
  Nothing -> pure t
  Just mt -> burnFuel *> headNormalizeTypeF mt

-- | Head reduces a type until it is head-normal or we run out of steps
headNormalizeTypeK :: Int -> Type -> Maybe Type
headNormalizeTypeK fuel t = evalFuel (headNormalizeTypeF t) fuel

-- | Head reduces a type until it is head-normal
headNormalizeType :: Type -> Type
headNormalizeType = fromJust . headNormalizeTypeK (-1)

-- | Is the type in normal form?
isNormalType :: Type -> Bool
isNormalType t = case t of
  TyVar _       -> True
  TyArr _ t1 t2 -> isNormalType t1 && isNormalType t2
  TyApp _ ts _  -> isNormalType t && all isNormalType ts
  TyQu _ _ t1   -> isNormalType t1
  TyMu _ t1     -> isNormalType t1

-- | Reduces a type until it is normal, given some amount of fuel
normalizeTypeF :: Type -> Fuel Type
normalizeTypeF t0 = do
  t <- headNormalizeTypeF t0
  case t of
    TyVar _       -> pure t
    TyArr q t1 t2 -> TyArr q <$> normalizeTypeF t1 <*> normalizeTypeF t2
    TyApp tc ts _ -> do
      t' <- tyApp tc <$> mapA normalizeTypeF ts
      if isHeadNormalType t'
        then return t'
        else normalizeTypeF t'
    TyQu qu tv t1 -> TyQu qu tv <$> normalizeTypeF t1
    TyMu tv t1    -> TyMu tv <$> normalizeTypeF t1

-- | Reduces a type until it is normal or we run out of steps
normalizeTypeK :: Int -> Type -> Maybe Type
normalizeTypeK fuel t = evalFuel (normalizeTypeF t) fuel

-- | Reduces a type until it is normal
normalizeType :: Type -> Type
normalizeType = fromJust . normalizeTypeK (-1)

-- | Performs one reduction step.  The order of evaluation is
--   different than used by 'normalizeType', but note that type
--   reduction is not guaranteed to be confluent
reduceType :: Type -> Maybe Type
reduceType t = case t of
  TyVar _       -> Nothing
  TyArr q t1 t2 -> TyArr q <$> reduceType t1 <*> pure t2
               <|> TyArr q <$> pure t1 <*> reduceType t2
  TyApp tc ts _ -> headReduceType t
               <|> tyApp tc <$> reduceTypeList ts
  TyQu qu tv t1 -> TyQu qu tv <$> reduceType t1
  TyMu tv t1    -> TyMu tv <$> reduceType t1

-- | Takes the first reduction step found in a list of types, or
--   returns 'Nothing' if they're all normal
reduceTypeList :: [Type] -> Maybe [Type]
reduceTypeList []     = Nothing
reduceTypeList (t:ts) = (:) <$> reduceType t <*> pure ts
                    <|> (:) <$> pure t <*> reduceTypeList ts
---
--- The Fuel monad
---

-- | The Fuel monad enables counting computation steps, and
--   fails if it runs out of fuel
newtype Fuel a
  = Fuel {
      -- | Run a 'Fuel' computation, getting back the
      --   answer and remaining fuel
      runFuel :: Int -> Maybe (a, Int)
    }
  deriving Functor

-- | Run a 'Fuel' computation, getting back the answer only
evalFuel :: Fuel a -> Int -> Maybe a
evalFuel  = fmap fst <$$> runFuel

-- | Use up one unit of fuel
burnFuel :: Fuel ()
burnFuel  = Fuel $ \fuel ->
  if fuel == 0
    then Nothing
    else Just ((), fuel - 1)

instance Applicative Fuel where
  pure a  = Fuel $ \fuel -> return (a, fuel)
  f <*> g = Fuel $ \fuel -> do
    (f', fuel')  <- runFuel f fuel
    (g', fuel'') <- runFuel g fuel'
    return (f' g', fuel'')

instance Alternative Fuel where
  empty   = Fuel (const Nothing)
  f <|> g = Fuel (\fuel -> runFuel f fuel <|> runFuel g fuel)

instance Monad Fuel where
  return a = Fuel $ \fuel -> return (a, fuel)
  m >>= k  = Fuel $ \fuel -> do
    (m', fuel')  <- runFuel m fuel
    runFuel (k m') fuel'

---
--- Built-in type constructors
---

class ExtTC r where
  extTC :: TyCon -> r

instance ExtTC TyCon where
  extTC = id
instance ExtTC r => ExtTC (Integer -> r) where
  extTC tc x = extTC (tc { tcId = x })
instance ExtTC r => ExtTC (String -> r) where
  extTC tc x = extTC (tc { tcName = qlid x })
instance ExtTC r => ExtTC (QLid -> r) where
  extTC tc x = extTC (tc { tcName = x })
instance (v ~ Variance, ExtTC r) => ExtTC ([(QLit, v)] -> r) where
  extTC tc x = extTC (tc { tcArity = x })
instance ExtTC r => ExtTC (QDen Int -> r) where
  extTC tc x = extTC (tc { tcQual = x })
instance ExtTC r => ExtTC (Env.Env Uid (Maybe Type) -> r) where
  extTC tc x = extTC (tc { tcCons = x })
instance ExtTC r => ExtTC (([Type] -> Maybe Type) -> r) where
  extTC tc x = extTC (tc { tcNext = Just x })
instance ExtTC r => ExtTC (Maybe ([Type] -> Maybe Type) -> r) where
  extTC tc x = extTC (tc { tcNext = x })

mkTC :: ExtTC r => Integer -> String -> r
mkTC i s = extTC TyCon {
  tcId    = i,
  tcName  = qlid s,
  tcArity = [],
  tcQual  = minBound,
  tcCons  = Env.empty,
  tcNext  = Nothing
}

tcUnit, tcInt, tcFloat, tcString,
  tcExn, tcTuple, tcUn, tcAf :: TyCon

tcUnit       = mkTC (-1) "unit"
tcInt        = mkTC (-2) "int"
tcFloat      = mkTC (-3) "float"
tcString     = mkTC (-4) "string"
tcExn        = mkTC (-5) "exn" (maxBound :: QDen Int)
tcUn         = mkTC (-6) "U"
tcAf         = mkTC (-7) "A"   (maxBound :: QDen Int)
tcTuple      = mkTC (-8) "*"   (0 \/ 1 :: QDen Int)   [(Qa, 1), (Qa, 1)]

-- For session types:

tcSend, tcRecv, tcSelect, tcFollow, tcDual :: TyCon

tcSend       = mkTC (-11) "send"   [(Qa, 1)]
tcRecv       = mkTC (-12) "recv"   [(Qa, -1)]
tcSelect     = mkTC (-13) "select" [(Qu, 1)]
tcFollow     = mkTC (-14) "follow" [(Qu, 1)]
tcDual       = mkTC (-15) "dual"   [(Qu, -1)] $ \t ->
  case t of
    [TyVar tv]         -> Just (TyVar tv)
    [TyApp tc ts _]
      | tc == tcSend   -> Just (tyApp tcRecv ts)
      | tc == tcRecv   -> Just (tyApp tcSend ts)
      | tc == tcSelect -> Just (tyApp tcFollow (map dual ts))
      | tc == tcFollow -> Just (tyApp tcSelect (map dual ts))
      | tc == tcUnit   -> Just (tyApp tcUnit ts)
      | tcName tc == qlid ";"
                       -> Just (tyApp tc (map dual ts))
    [TyMu tv t']       -> return (TyMu tv (dual t'))
    _ -> Nothing
  where dual t = tyApp tcDual [t]

---
--- Convenience type constructors
---

-- | Make a type from a nullary type constructor
tyNulOp :: TyCon -> Type
tyNulOp tc = tyApp tc []

-- | Make a type from a unary type constructor
tyUnOp :: TyCon -> Type -> Type
tyUnOp tc t1 = tyApp tc [t1]

-- | Make a type from a binary type constructor
tyBinOp :: TyCon -> Type -> Type -> Type
tyBinOp tc t1 t2 = tyApp tc [t1, t2]

-- | The unit type
tyUnit :: Type
tyUnit  = tyNulOp tcUnit

-- | Constructor for tuple types
tyTuple :: Type -> Type -> Type
tyTuple = tyBinOp tcTuple

-- | Constructor for unlimited arrow types
tyArr :: Type -> Type -> Type
tyArr   = TyArr minBound

-- | Constructor for affine arrow types
tyLol :: Type -> Type -> Type
tyLol   = TyArr maxBound

---
--- Miscellany
---

-- | Represent a type value as a syntactic type, for printing
typeToStx :: Type -> Stx.Type ()
typeToStx t0 = case t0 of
  TyVar tv      -> Stx.TyVar tv
  TyArr q t1 t2 -> Stx.TyArr (qRepresent q) (typeToStx t1) (typeToStx t2)
  TyApp tc ts _ -> Stx.TyCon (tcName tc) (map typeToStx ts) ()
  TyQu qu tv t1 -> Stx.TyQu qu tv (typeToStx t1)
  TyMu tv t1    -> Stx.TyMu tv (typeToStx t1)

castableType :: Type -> Bool
castableType t = case headNormalizeType t of
  TyVar _     -> False
  TyArr _ _ _ -> True
  TyApp _ _ _ -> False
  TyQu _ _ t1 -> castableType t1
  TyMu _ t1   -> castableType t1

