-- | The internal representation of types, created by the type checker
--   from the syntactic types in 'Syntax.Type'.
{-# LANGUAGE
      DeriveDataTypeable,
      DeriveFunctor,
      ViewPatterns,
      FlexibleInstances,
      ParallelListComp,
      PatternGuards,
      ScopedTypeVariables,
      TypeFamilies #-}
module Type (
  -- * Representation of types
  Type(..), TyCon(..), TyVarR, TyPat(..), tyApp,
  -- * Type reduction
  ReductionState(..),
  -- ** Head reduction
  isHeadNormalType, headReduceType,
  headNormalizeTypeK, headNormalizeTypeM,
  headNormalizeType,
  -- ** Deep reduction
  isNormalType, normalizeTypeK, normalizeType,
  -- ** Freshness
  Ftv(..), freshTyVar, freshTyVars,
  fastFreshTyVar, fastFreshTyVars,
  -- ** Substitutions
  tysubst, tysubsts, tyrename,
  -- * Miscellaneous type operations
  castableType, typeToStx, typeToStx', tyPatToStx, tyPatToStx',
  tyPatToType, qualifier,
  -- * Built-in types
  -- ** Type constructors
  mkTC,
  tcBot, tcUnit, tcInt, tcFloat, tcString, tcExn, tcTuple, tcUn, tcAf,
  -- ** Types
  tyNulOp, tyUnOp, tyBinOp,
  tyArr, tyLol,
  tyAll, tyEx,
  -- *** Convenience
  tyBot, tyUnit, tyInt, tyFloat, tyString, tyExn, tyUn, tyAf, tyTop,
  tyIdent, tyConst,
  tyTuple,
  (.*.), (.->.), (.-*.),
  -- * Views
  vtAppTc, isBotType,
  -- ** Unfolds
  vtFuns, vtQus,
  -- * Re-exports
  module Syntax.Ident,
  module Syntax.Kind,
  module Syntax.POClass,
  Stx.Quant(..),
  -- * Debugging and testing
  dumpType,
  tcSend, tcRecv, tcSelect, tcFollow, tcSemi, tcDual,
  tySend, tyRecv, tyDual, tySelect, tyFollow, tySemi, (.:.),
) where

import qualified Env
import Ppr
import Syntax.Ident
import Syntax.Kind
import Syntax.POClass
import qualified Syntax as Stx
import Util
import Viewable

import qualified Control.Monad.Writer as CMW
import Data.Char (isDigit)
import Data.Generics (Typeable, Data, everything, mkQ)
import qualified Data.Map as M
import qualified Data.Set as S

-- | All tyvars are renamed by this point
type TyVarR = TyVar Renamed

-- | The internal representation of a type
data Type
  -- | A type variable
  = TyVar TyVarR
  -- | The application of a type constructor (possibly nullary); the
  --   third field caches the next head-reduction step if the type
  --   is not head-normal -- note that substitution invalidates this
  --   cache.  Use 'tyApp' to construct a type application that
  --   (re)initializes the cache.
  | TyApp TyCon [Type] (ReductionState Type)
  -- | An arrow type, including qualifier expression
  | TyFun (QDen TyVarR) Type Type
  -- | A quantified (all or ex) type
  | TyQu  Stx.Quant TyVarR Type
  -- | A recursive (mu) type
  | TyMu  TyVarR Type
  deriving (Typeable, Data)

-- | Information about a type constructor
data TyCon
  = TyCon {
      -- | Printable name
      tcName      :: QLid Renamed,
      -- | Variances for parameters, and correct length
      tcArity     :: [Variance],
      -- | Bounds for parameters (may be infinite)
      tcBounds    :: [QLit],
      -- | Qualifier as a function of parameters
      tcQual      :: QDen Int,
      -- | For pattern-matchable types, the data constructors
      tcCons      :: ([TyVarR], Env.Env (Uid Renamed) (Maybe Type)),
      -- | For type operators, the next head reduction
      tcNext      :: Maybe [([TyPat], Type)]
    }
  deriving (Typeable, Data)

-- | A type pattern, for defining type operators
data TyPat
  -- | A type variable, matching any type and binding
  = TpVar TyVarR
  -- | A type application node, matching the given constructor
  --   and its parameters
  | TpApp TyCon [TyPat]
  deriving (Typeable, Data)

instance Eq TyCon where
  tc == tc'  =  tcName tc == tcName tc'

instance Ord TyCon where
  compare tc tc'  = compare (tcName tc) (tcName tc')

instance Ppr Type   where pprPrec p = pprPrec p . typeToStx
instance Show Type  where showsPrec = showFromPpr
instance Ppr TyPat  where pprPrec p = pprPrec p . tyPatToStx
instance Show TyPat where showsPrec = showFromPpr

-- | Find the qualifier of a type
qualifier     :: Type -> QDen TyVarR
qualifier (TyApp tc ts _) = denumberQDen (map qualifier ts) (tcQual tc)
qualifier (TyFun q _ _)   = q
qualifier (TyVar tv)
  | tvqual tv <: Qu       = minBound
  | otherwise             = qInterpret (qeVar tv)
qualifier (TyQu _ tv t)   = qSubst tv minBound (qualifier t)
qualifier (TyMu tv t)     = qSubst tv minBound (qualifier t)

---
--- Free type variables, freshness, and substitution
---

-- | Class for getting free type variables (from types, expressions,
-- lists thereof, pairs thereof, etc.)
class Ftv a where
  ftvVs :: a -> M.Map TyVarR Variance
  ftv   :: a -> S.Set TyVarR
  ftv    = M.keysSet . ftvVs
  alltv :: a -> S.Set TyVarR
  maxtv :: a -> Renamed

instance Ftv Type where
  ftv (TyApp _ ts _)  = S.unions (map ftv ts)
  ftv (TyVar tv)      = S.singleton tv
  ftv (TyFun q t1 t2) = S.unions [ftv t1, ftv t2, ftv q]
  ftv (TyQu _ tv t)   = S.delete tv (ftv t)
  ftv (TyMu tv t)     = S.delete tv (ftv t)
  --
  ftvVs (TyApp tc ts _) = M.unionsWith (+)
                          [ M.map (* var) m
                          | var   <- tcArity tc
                          | m     <- map ftvVs ts ]
  ftvVs (TyFun q t1 t2) = M.unionsWith (+)
                          [ ftvVs q
                          , M.map negate (ftvVs t1)
                          , ftvVs t2 ]
  ftvVs (TyVar tv)      = M.singleton tv 1
  ftvVs (TyQu _ tv t)   = M.delete tv (ftvVs t)
  ftvVs (TyMu tv t)     = M.delete tv (ftvVs t)
  --
  alltv (TyApp _ ts _)  = alltv ts
  alltv (TyVar tv)      = alltv tv
  alltv (TyFun q t1 t2) = alltv q `S.union` alltv t1 `S.union` alltv t2
  alltv (TyQu _ tv t)   = tv `S.insert` alltv t
  alltv (TyMu tv t)     = tv `S.insert` alltv t
  --
  maxtv (TyApp _ ts _)  = maxtv ts
  maxtv (TyVar tv)      = maxtv tv
  maxtv (TyFun q t1 t2) = maxtv q `max` maxtv t1 `max` maxtv t2
  maxtv (TyQu _ tv t)   = maxtv tv `max` maxtv t
  maxtv (TyMu tv t)     = maxtv tv `max` maxtv t

instance (Data a, Ord a, Ftv a) => Ftv (QDen a) where
  ftv   = everything S.union (mkQ S.empty (ftv :: a -> S.Set TyVarR))
  ftvVs = everything M.union
            (mkQ M.empty (ftvVs :: a -> M.Map TyVarR Variance))
  alltv = everything S.union (mkQ S.empty (alltv :: a -> S.Set TyVarR))
  maxtv = everything max (mkQ trivialId (maxtv :: a -> Renamed))

instance Ftv a => Ftv [a] where
  ftv   = S.unions . map ftv
  ftvVs = M.unionsWith (+) . map ftvVs
  alltv = S.unions . map alltv
  maxtv [] = trivialId
  maxtv xs = maximum (map maxtv xs)

instance (i ~ Renamed) => Ftv (TyVar i) where
  ftv      = S.singleton
  ftvVs tv = M.singleton tv 1
  alltv    = S.singleton
  maxtv    = lidUnique . tvname

instance (Ftv a, Ftv b) => Ftv (a, b) where
  ftv (a, b)   = ftv a `S.union` ftv b
  ftvVs (a, b) = M.unionWith (+) (ftvVs a) (ftvVs b)
  alltv (a, b) = alltv a `S.union` alltv b
  maxtv (a, b) = maxtv a `max` maxtv b

-- Rename a type variable, if necessary, to make its unique tag higher
-- than the one given
fastFreshTyVar :: TyVarR -> Renamed -> TyVarR
fastFreshTyVar tv@(TV (Lid i n) q) imax =
  if i > imax
    then tv
    else TV (Lid (succ imax) n) q
fastFreshTyVar (TVAnti a)         _ = Stx.antierror "Type.fastFreshTyVar" a
fastFreshTyVar (TV (LidAnti a) _) _ = Stx.antierror "Type.fastFreshTyVar" a

-- Rename a list of type variables, if necessary, to make each unique tag
-- higher than the one given and mutually unique
fastFreshTyVars :: [TyVarR] -> Renamed -> [TyVarR]
fastFreshTyVars []       _    = []
fastFreshTyVars (tv:tvs) imax =
  let tv' = fastFreshTyVar tv imax in
  tv' : fastFreshTyVars tvs (imax `max` maxtv tv')

-- | Given a type variable, rename it (if necessary) to make it
--   fresh for a set of type variables.
freshTyVar :: TyVarR -> S.Set TyVarR -> TyVarR
freshTyVar (TV l q) set = TV l' q where
  l'       = if unLid l `S.member` names
               then lid (loop count)
               else l
  names    = S.map (unLid . tvname) set
  loop n   =
    let tv' = prefix ++ show n
    in if tv' `S.member` names
         then loop (n + 1)
         else tv'
  suffix   = reverse . takeWhile isDigit . reverse . unLid $ l
  prefix   = reverse . dropWhile isDigit . reverse . unLid $ l
  count    = case reads suffix of
               ((n, ""):_) -> n
               _           -> 1::Integer
freshTyVar (TVAnti a) _ = Stx.antierror "Type.freshTyVar" a

-- | Given a list of type variables, rename them (if necessary) to make
--   each of them fresh for both the set of type variables and each
--   other.
freshTyVars :: [TyVarR] -> S.Set TyVarR -> [TyVarR]
freshTyVars []       _   = []
freshTyVars (tv:tvs) set = tv' : freshTyVars tvs (S.insert tv' set)
  where tv' = freshTyVar tv (set `S.union` S.fromList tvs)

-- | Type substitution
tysubst :: TyVarR -> Type -> Type -> Type
tysubst a t = loop where
  loop (TyVar a')
    | a' == a   = t
    | otherwise = TyVar a'
  loop (TyFun q t1 t2)
                = TyFun (qSubst a (qualifier t) q) (loop t1) (loop t2)
  loop (TyApp tc ts _)
                = tyApp tc (map loop ts)
  loop (TyQu u a' t')
    | a' == a   = TyQu u a' t'
    | a'' <- fastFreshTyVar a' imax
                = TyQu u a'' (loop (tysubst a' (TyVar a'') t'))
  loop (TyMu a' t')
    | a' == a   = TyMu a' t'
    | a'' <- fastFreshTyVar a' imax
                = TyMu a'' (loop (tysubst a' (TyVar a'') t'))
  imax = maxtv (a, t)

-- | Given a list of type variables and types, perform all the
--   substitutions, avoiding capture between them.
tysubsts :: [TyVarR] -> [Type] -> Type -> Type
tysubsts ps ts t =
  let ps' = fastFreshTyVars ps (maxtv (t:ts))
      substs tvs ts0 t0 = foldr2 tysubst t0 tvs ts0 in
  substs ps' ts .
    substs ps (map TyVar ps') $
      t

-- | Rename a type variable
tyrename :: TyVarR -> TyVarR -> Type -> Type
tyrename tv = tysubst tv . TyVar

---
--- Type reduction
---

-- | As we head-reduce a type, it can be in one of four states:
data ReductionState t
  -- | The type is head-normal -- that is, its head constructor is
  --   not a type synonym/operator
  = Done
  -- | The type has a next head-reduction step
  | Next t
  -- | The type may reduce further in the future, but right now it
  --   has a pattern match that depends on the value of a type variable
  | Blocked
  -- | The type's head constructor is a synonym/operator, but it
  --   can never take a step, due to a failed pattern match
  | Stuck
  deriving (Eq, Ord, Show, Functor, Typeable, Data)

-- | Helper type for 'tyApp'
type MatchResult t = Either (ReductionState t) ([TyVarR], [Type])

-- | Creates a type application, initializing the head-reduction cache
tyApp :: TyCon -> [Type] -> Type
tyApp tc0 ts0 = TyApp tc0 ts0 $ maybe Done clauses (tcNext tc0) where
  clauses []                = Stuck
  clauses ((tps, rhs):rest) = case patts tps ts0 of
    Right (xs, us)  -> Next (tysubsts xs us rhs)
    Left Stuck      -> clauses rest
    Left rs         -> fmap (tyApp tc0) rs

  patts :: [TyPat] -> [Type] -> MatchResult [Type]
  patts []       []     = Right ([], [])
  patts (tp:tps) (t:ts) = case patt tp t of
    Right (xs, us) -> case patts tps ts of
      Right (xs', us') -> Right (xs ++ xs', us ++ us')
      Left rs          -> Left (fmap (t:) rs)
    Left Blocked       -> Left (either (fmap (t:))
                                       (const Blocked)
                                       (patts tps ts))
    Left rs            -> Left (fmap (:ts) rs)
  patts _        _      = Left Stuck

  patt :: TyPat -> Type -> MatchResult Type
  patt (TpVar tv)     t = Right ([tv], [t])
  patt (TpApp tc tps) t = case t of
    TyApp tc' ts next
      | tc == tc'       -> (fmap (tyApp tc') +++ id) (patts tps ts)
      | Done <- next    -> Left Stuck
      | otherwise       -> Left next
    TyMu tv t1          -> Left (Next (tysubst tv (TyMu tv t1) t1))
    TyVar _             -> Left Blocked
    _                   -> Left Stuck

-- | Takes one head reduction step.  Returns 'Nothing' if the type is
--   already head-normal.
headReduceType :: Type -> ReductionState Type
headReduceType (TyApp _ _ next) = next
headReduceType _                = Done

-- | Is the type head-normal?  A type is head-normal unless its
--   top-level constructor is a type operator which can currently
--   take a step.
isHeadNormalType :: Type -> Bool
isHeadNormalType t = case headReduceType t of
  Next _ -> False
  _      -> True

-- | Head reduces a type until it is head-normal, given some amount of fuel
headNormalizeTypeF :: Type -> Fuel (ReductionState (), Type) Type
headNormalizeTypeF t = case headReduceType t of
    Done    -> pure t
    Next t' -> burnFuel (Next (), t') *> headNormalizeTypeF t'
    Blocked -> bailOut (Blocked, t)
    Stuck   -> bailOut (Stuck, t)

-- | Head reduces a type until it is head-normal or we run out of steps
headNormalizeTypeK :: Int -> Type -> (ReductionState (), Type)
headNormalizeTypeK fuel t = case evalFuel (headNormalizeTypeF t) fuel of
  Right t'      -> (Done, t')
  Left (rs, t') -> (rs, t')

headNormalizeTypeM :: Monad m => Int -> Type -> m Type
headNormalizeTypeM limit t = case headNormalizeTypeK limit t of
  (Next (), t') -> fail $
    "Gave up reducing type `" ++ show t' ++
    "' after " ++ show limit ++ " steps"
  (_, t') -> return t'

-- | Head reduces a type until it is head-normal
headNormalizeType :: Type -> Type
headNormalizeType = snd . headNormalizeTypeK (-1)

-- | Is the type in normal form?
isNormalType :: Type -> Bool
isNormalType t = case t of
  TyVar _       -> True
  TyFun _ t1 t2 -> isNormalType t1 && isNormalType t2
  TyApp _ ts _  -> isHeadNormalType t && all isNormalType ts
  TyQu _ _ t1   -> isNormalType t1
  TyMu _ t1     -> isNormalType t1

-- | Reduces a type until it is normal, given some amount of fuel
normalizeTypeF :: Type -> Fuel (ReductionState (), Type) Type
normalizeTypeF t0 = do
  t <- headNormalizeTypeF t0
  case t of
    TyVar _       -> pure t
    TyFun q t1 t2 -> do
      t1' <- normalizeTypeF t1 `mapError` fmap (flip (TyFun q) t2)
      t2' <- normalizeTypeF t2 `mapError` fmap (TyFun q t1')
      return (TyFun q t1' t2')
    TyApp tc ts0 _ -> do
      let loop []      = return []
          loop (t1:ts) = do
            t'  <- normalizeTypeF t1 `mapError` fmap (:ts)
            ts' <- loop ts `mapError` fmap (t':)
            return (t':ts')
      tyApp tc <$> (loop ts0 `mapError` fmap (tyApp tc))
    TyQu qu tv t1 -> do
      t1' <- normalizeTypeF t1 `mapError` fmap (TyQu qu tv)
      return (TyQu qu tv t1')
    TyMu tv t1 -> do
      t1' <- normalizeTypeF t1 `mapError` fmap (TyMu tv)
      return (TyMu tv t1')

normalizeTypeK :: Int -> Type -> (ReductionState (), Type)
normalizeTypeK fuel t = case evalFuel (normalizeTypeF t) fuel of
  Right t'      -> (Done, t')
  Left (rs, t') -> (rs, t')

-- | Reduces a type until it is normal
normalizeType :: Type -> (ReductionState (), Type)
normalizeType = normalizeTypeK (-1)

{-
-- | Performs one reduction step.  The order of evaluation is
--   different than used by 'normalizeType', but note that type
--   reduction is not guaranteed to be confluent
reduceType :: Type -> Maybe Type
reduceType t = case t of
  TyVar _       -> Nothing
  TyFun q t1 t2 -> TyFun q <$> reduceType t1 <*> pure t2
               <|> TyFun q <$> pure t1 <*> reduceType t2
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
-}

---
--- The Fuel monad
---

-- | The Fuel monad enables counting computation steps, and
--   fails if it runs out of fuel
newtype Fuel r a
  = Fuel {
      -- | Run a 'Fuel' computation, getting back the
      --   answer and remaining fuel
      runFuel :: Int -> Either r (a, Int)
    }
  deriving Functor

-- | Run a 'Fuel' computation, getting back the answer only
evalFuel :: Fuel r a -> Int -> Either r a
evalFuel  = fmap fst <$$> runFuel

-- | Use up one unit of fuel
burnFuel :: r -> Fuel r ()
burnFuel r = Fuel $ \fuel ->
  if fuel == 0
    then Left r
    else Right ((), fuel - 1)

-- | Give up on a fuel computation
bailOut :: r -> Fuel r a
bailOut = Fuel . const . Left

{-
-- | Catch a failed fuel computation, and potentially add more fuel
reFuel :: Fuel r a -> (r -> (Int, Fuel r a)) -> Fuel r a
reFuel f k = Fuel $ \fuel -> case runFuel f fuel of
  Left r           -> let (fuel', f') = k r in runFuel f' fuel'
  Right (fuel', a) -> Right (fuel', a)
-}

-- | Given a fuel computation with a given failure result, map
--   the failure result
mapError :: Fuel r a -> (r -> s) -> Fuel s a
mapError f h = Fuel $ \fuel -> case runFuel f fuel of
  Left r   -> Left (h r)
  Right a  -> Right a

instance Applicative (Fuel r) where
  pure a  = Fuel $ \fuel -> Right (a, fuel)
  f <*> g = Fuel $ \fuel -> case runFuel f fuel of
    Right (f', fuel') -> case runFuel g fuel' of
      Right (g', fuel'') -> Right (f' g', fuel'')
      Left r             -> Left r
    Left r            -> Left r

instance Monad (Fuel r) where
  return a = Fuel $ \fuel -> Right (a, fuel)
  m >>= k  = Fuel $ \fuel -> case runFuel m fuel of
    Right (m', fuel') -> runFuel (k m') fuel'
    Left r            -> Left r

---
--- Built-in type constructors
---

class ExtTC r where
  extTC :: TyCon -> r

instance ExtTC TyCon where
  extTC = id
instance ExtTC r => ExtTC (QLid Renamed -> r) where
  extTC tc x = extTC (tc { tcName = x })
instance (v ~ Variance, ExtTC r) => ExtTC ([(QLit, v)] -> r) where
  extTC tc x = extTC (tc { tcArity = map snd x, tcBounds = map fst x })
instance ExtTC r => ExtTC (QDen Int -> r) where
  extTC tc x = extTC (tc { tcQual = x })
instance (v ~ TyVarR, a ~ Type, i ~ Renamed, ExtTC r) =>
         ExtTC (([v], Env.Env (Uid i) (Maybe a)) -> r) where
  extTC tc x = extTC (tc { tcCons = x })
instance ExtTC r => ExtTC ([([TyPat], Type)] -> r) where
  extTC tc x = extTC (tc { tcNext = Just x })
instance ExtTC r => ExtTC (Maybe [([TyPat], Type)] -> r) where
  extTC tc x = extTC (tc { tcNext = x })

mkTC :: ExtTC r => QLid Renamed -> r
mkTC ql = extTC TyCon {
  tcName   = ql,
  tcArity  = [],
  tcBounds = [],
  tcQual   = minBound,
  tcCons   = ([], Env.empty),
  tcNext   = Nothing
}

internalTC :: ExtTC r => Int -> String -> r
internalTC i s = extTC TyCon {
  tcName   = J [] (Lid (Ren_ i) s),
  tcArity  = [],
  tcBounds = [],
  tcQual   = minBound,
  tcCons   = ([], Env.empty),
  tcNext   = Nothing
}

tcBot, tcUnit, tcInt, tcFloat, tcString,
  tcExn, tcUn, tcAf, tcTuple, tcIdent, tcConst :: TyCon

tcBot        = internalTC (-1) "any"
tcUnit       = internalTC (-2) "unit" ([], Env.fromList [(uid "()", Nothing)])
tcInt        = internalTC (-3) "int"
tcFloat      = internalTC (-4) "float"
tcString     = internalTC (-5) "string"
tcExn        = internalTC (-6) "exn" (maxBound :: QDen Int)
tcUn         = internalTC (-7) "U"
tcAf         = internalTC (-8) "A"   (maxBound :: QDen Int)
tcTuple      = internalTC (-9) "*"   (0 \/ 1 :: QDen Int)   [(Qa, 1), (Qa, 1)]
tcIdent      = internalTC (-10) "id"    (0 :: QDen Int) [(Qa, 1)]
    [([TpVar (tvAf "a")], TyVar (tvAf "a"))]
tcConst      = internalTC (-11) "const" (0 :: QDen Int) [(Qa, Invariant)]
    [([TpVar (tvAf "a")], tyUnit)]

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

-- | Constructor for unlimited arrow types
tyArr :: Type -> Type -> Type
tyArr   = TyFun minBound

-- | Constructor for affine arrow types
tyLol :: Type -> Type -> Type
tyLol   = TyFun maxBound

-- | Construct a universal type
tyAll :: TyVarR -> Type -> Type
tyAll  = TyQu Stx.Forall

-- | Construct a existential type
tyEx  :: TyVarR -> Type -> Type
tyEx   = TyQu Stx.Exists

-- | Preconstructed types
tyBot, tyUnit, tyInt, tyFloat, tyString, tyExn, tyUn, tyAf :: Type
tyIdent, tyConst :: Type -> Type
tyTuple :: Type -> Type -> Type
tyTop :: QLit -> Type

tyBot    = tyNulOp tcBot
tyUnit   = tyNulOp tcUnit
tyInt    = tyNulOp tcInt
tyFloat  = tyNulOp tcFloat
tyString = tyNulOp tcString
tyExn    = tyNulOp tcExn
tyUn     = tyNulOp tcUn
tyAf     = tyNulOp tcAf
tyTop    = elimQLit tyUn tyAf
tyTuple  = tyBinOp tcTuple
tyIdent  = tyUnOp tcIdent
tyConst  = tyUnOp tcConst

(.*.), (.->.), (.-*.) :: Type -> Type -> Type
(.*.)    = tyTuple
(.->.)   = tyArr
(.-*.)   = tyLol

infixr 6 .->., .-*., `tyArr`, `tyLol`
infixl 7 .*., `tyTuple`
infixr 8 .:., `tySemi`

---
--- Miscellany
---

-- | Represent a type value as a pre-syntactic type, for printing
typeToStx' :: Type -> Stx.Type' Renamed
typeToStx'  = view . typeToStx

-- | Represent a type value as a syntactic type, for printing; renames
--   so that scope is apparent, since internal renaming may result int
--   different identifiers that print the same
typeToStx :: Type -> Stx.Type Renamed
typeToStx = loop (S.empty, M.empty) where
  loop ren t0 = case t0 of
    TyVar tv      -> Stx.tyVar (maybe tv id (M.lookup tv (snd ren)))
    TyFun q t1 t2 -> Stx.tyFun (qRepresent q) (loop ren t1) (loop ren t2)
    TyApp tc ts _ -> Stx.tyApp (tcName tc) (map (loop ren) ts)
    TyQu qu tv t1 -> Stx.tyQu qu tv' (loop ren' t1)
      where (tv', ren') = fresh tv ren
    TyMu tv t1    -> Stx.tyMu tv' (loop ren' t1)
      where (tv', ren') = fresh tv ren
  fresh tv (seen, remap) = 
    let tv' = if S.member (unLid (tvname tv)) seen
                then freshTyVar tv $
                       M.keysSet remap `S.union`
                         S.fromList (M.elems remap)
                else tv
     in (tv', (S.insert (unLid (tvname tv')) seen,
               M.insert tv tv' remap))

tyPatToStx' :: TyPat -> Stx.TyPat' Renamed
tyPatToStx'  = view . tyPatToStx

-- | Represent a type pattern as a syntactic type pattern, for printing
tyPatToStx :: TyPat -> Stx.TyPat Renamed
tyPatToStx tp0 = case tp0 of
  TpVar tv      -> Stx.tpVar tv Invariant
  TpApp tc tps  -> Stx.tpApp (tcName tc) (map tyPatToStx tps)

-- | Convert a type pattern to a type; useful for quqlifier and variance
--   analysis
tyPatToType :: TyPat -> Type
tyPatToType (TpVar tv)     = TyVar tv
tyPatToType (TpApp tc tps) = tyApp tc (map tyPatToType tps)

castableType :: Type -> Bool
castableType t = case headNormalizeType t of
  TyVar _     -> False
  TyFun _ _ _ -> True
  TyApp _ _ _ -> False
  TyQu _ _ t1 -> castableType t1
  TyMu _ t1   -> castableType t1

{-
-- Example types and reduction

hgo t = loop 0 where
  loop 100 = putStrLn "gave up after 100 steps"
  loop i    = case headNormalizeTypeK i t of
    (Next (), t) -> do print t; loop (i + 1)
    (rs, _)      -> print rs

go t = loop 0 where
  loop 100 = putStrLn "gave up after 100 steps"
  loop i    = case normalizeTypeK i t of
    (Next (), t) -> do print t; loop (i + 1)
    (rs, _)      -> print rs

a = tyApp tcDual
       [tyApp tcSemi
         [tyApp tcRecv [tyApp tcInt []],
          tyApp tcSemi
           [tyApp tcSend [tyApp tcString []],
            tyUnit]]]

b = tyApp tcIdent
     [tyApp tcSemi
       [tyApp tcIdent [tyApp tcRecv [tyApp tcInt []]],
        tyApp tcIdent
         [tyApp tcSemi
           [tyApp tcSend [tyApp tcString []],
            tyUnit]]]]

c = tyApp tcIdent [tyApp tcDual [b]]

d = tyApp tcDual [c]

e = tyApp tcDual
     [tyApp tcIdent
       [tyApp tcSemi
         [tyApp tcIdent [tyUnit],
          tyApp tcIdent
           [tyApp tcSemi
             [tyApp tcSend [tyApp tcString []],
              tyUnit]]]]]

f = tyApp tcDual
     [tyApp tcIdent
       [tyApp tcSemi
         [tyApp tcIdent [TyVar (TV (Lid "c") Qu)],
          tyApp tcIdent
           [tyApp tcSemi
             [tyApp tcSend [tyApp tcString []],
              tyUnit]]]]]

g = tyApp tcInfiniteLoop [tyUnit] where

tcInfiniteLoop :: TyCon

tcInfiniteLoop = internalTC (-100) "loop"
  [([TpVar (TV (Lid "a") Qu)],
       tyApp tcInfiniteLoop [TyVar (TV (Lid "a") Qu)])]
-}

instance Viewable Type where
  type View Type = Type
  view t = case headNormalizeTypeM 1000 t of
    Just t' -> t'
    Nothing -> error "view: gave up reducting type after 1000 steps"

-- | Normalize a type enough to see if it's an application of
--   the given construtor
vtAppTc :: TyCon -> Type -> Type
vtAppTc tc t = case headNormalizeType t of
  t'@(TyApp tc' _ _) | tc == tc' -> t'
  _                              -> t

-- | Normalize a type enough to see if it's bottom
isBotType :: Type -> Bool
isBotType t = case view t of
  TyApp tc _ _ -> tc == tcBot
  _            -> False

-- | Unfold the arguments of a function type, normalizing as
--   necessary
vtFuns :: Type -> ([Type], Type)
vtFuns t = case view t of
  TyFun _ ta tr -> first (ta:) (vtFuns tr)
  _             -> ([], t)

-- | Unfold the parameters of a quantified type, normalizing as
--   necessary
vtQus  :: Stx.Quant -> Type -> ([TyVarR], Type)
vtQus u t = case view t of
  TyQu u' x t' | u == u' -> first (x:) (vtQus u t')
  _ -> ([], t)

-- For session types:

tcSend, tcRecv, tcSelect, tcFollow, tcSemi, tcDual :: TyCon

tcSend       = internalTC (-31) "send"   [(Qa, 1)]
tcRecv       = internalTC (-32) "recv"   [(Qa, -1)]
tcSelect     = internalTC (-33) "select" [(Qu, 1), (Qu, 1)]
tcFollow     = internalTC (-34) "follow" [(Qu, 1), (Qu, 1)]
tcSemi       = internalTC (-35) ";"      [(Qu, -1), (Qu, 1)]
tcDual       = internalTC (-36) "dual"   [(Qu, -1)]
  [ ([TpApp tcSemi   [TpApp tcSend [pa], pb]],
              (tyApp tcSemi [tyApp tcRecv [ta], dual tb]))
  , ([TpApp tcSemi   [TpApp tcRecv [pa], pb]],
              (tyApp tcSemi [tyApp tcSend [ta], dual tb]))
  , ([TpApp tcSelect [pa, pb]], (tyApp tcFollow [dual ta, dual tb]))
  , ([TpApp tcFollow [pa, pb]], (tyApp tcSelect [dual ta, dual tb]))
  , ([TpApp tcUnit   []],       (tyApp tcUnit []))
  ]
  where a = tvAf "a"
        b = tvAf "b"
        pa = TpVar a
        pb = TpVar b
        ta = TyVar a
        tb = TyVar b
        dual t = tyApp tcDual [t]

tySend, tyRecv, tyDual :: Type -> Type
tySelect, tyFollow, tySemi :: Type -> Type -> Type
(.:.) :: Type -> Type -> Type

tySend   = tyUnOp tcSend
tyRecv   = tyUnOp tcRecv
tySelect = tyBinOp tcSelect
tyFollow = tyBinOp tcFollow
tySemi   = tyBinOp tcSemi
tyDual   = tyUnOp tcDual
(.:.)    = tySemi

-- | Noisy type printer for debugging (includes type tags that aren't
--   normally pretty-printed)
dumpType :: Type -> String
dumpType = CMW.execWriter . loop 0 where
  loop i t0 = do
    CMW.tell (replicate i ' ')
    case t0 of
      TyApp tc ts _ -> do
        CMW.tell $
          show (tcName tc) ++ "[" ++
          show (lidUnique (jname (tcName tc))) ++ "] {\n"
        mapM_ (loop (i + 2)) ts
        CMW.tell (replicate i ' ' ++ "}\n")
      TyFun q dom cod -> do
        CMW.tell $ "-[" ++ show q ++ "]> {\n"
        loop (i + 2) dom
        loop (i + 2) cod
        CMW.tell (replicate i ' ' ++ "}\n")
      TyVar tv -> CMW.tell $ show tv
      TyQu u a t -> do
        CMW.tell $ show u ++ " " ++ show a ++ ". {\n"
        loop (i + 2) t
        CMW.tell (replicate i ' ' ++ "}\n")
      TyMu a t -> do
        CMW.tell $ "mu " ++ show a ++ ". {\n"
        loop (i + 2) t
        CMW.tell (replicate i ' ' ++ "}\n")

instance Ppr TyCon where
  ppr tc =
    case tcNext tc of
      Just [(tps,t)] -> ps tvs <+> ppr (tcName tc)
                          >?> qe tvs
                            >?> char '=' <+> ppr t
        where
          tvs  = [ case tp of
                     TpVar tv -> tv
                     _        -> TV (lid (show i)) qlit
                 | tp   <- tps
                 | qlit <- tcBounds tc
                 | i <- [ 1 .. ] :: [Int] ]
      --
      Just next -> ps tvs <+> ppr (tcName tc)
                     >?> (qe tvs <+> text "with"
                          $$ vcat (map alt next))
        where
          tvs  = [ TV (lid (show i)) qlit
                 | qlit <- tcBounds tc
                 | i <- [ 1 .. ] :: [Int] ]
          alt (tps,t) = char '|' <+> pprPrec precApp tps <+> ppr (tcName tc)
                          >?> char '=' <+> ppr t
      --
      Nothing -> ps tvs <+> ppr (tcName tc)
                   >?> qe tvs
                     >?> alts
        where
          tvs  = case fst (tcCons tc) of
            []   -> [ mk qlit | qlit <- tcBounds tc | mk <- tvalphabet ]
            tvs' -> tvs'
          alts = sep $
                 mapHead (text "=" <+>) $
                 mapTail (text "|" <+>) $
                 map alt (Env.toList (snd (tcCons tc)))
          alt (u, Nothing) = ppr u
          alt (u, Just t)  = ppr u <+> text "of" <+> ppr t
    where
      qe :: [TyVarR] -> Doc
      qe tvs = case qDenToLit (tcQual tc) of
                 Just Qu -> empty
                 _       -> text "qualifier" <+>
                            ppr (qRepresent
                                 (denumberQDen
                                  (map qDenOfTyVar tvs) (tcQual tc)))
      ps tvs = ppr
                 [ ppr var <> pprPrec precApp tv
                 | tv <- tvs
                 | var <- tcArity tc ]

instance Show TyCon where showsPrec = showFromPpr
