{-# LANGUAGE
      FlexibleInstances,
      QuasiQuotes,
      ParallelListComp,
      ScopedTypeVariables,
      TemplateHaskell #-}
module TypeRel (
  -- * Type operations
  -- ** Equality
  TypeTEq(..),
  -- ** Freshness
  Ftv(..), FtvVs(..), freshTyVar, freshTyVars,
  -- ** Substitutions
  tysubst, tysubsts,
  -- ** Queries and conversions
  qualifier, qualConst, replaceTyTags, removeTyTags,
  dualSessionType,
) where

import Quasi
import Syntax
import Util

import Data.Char (isDigit)
import Data.Generics (Data, everywhere, mkT, everything, mkQ)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State (State, evalState, get, put)

-- | Class for getting free type variables (from types, expressions,
-- lists thereof, pairs thereof, etc.)
class Ftv a where
  ftv :: a -> S.Set TyVar

instance Ftv (Type i) where
  ftv (TyCon _ ts _)  = S.unions (map ftv ts)
  ftv (TyVar tv)      = S.singleton tv
  ftv (TyArr q t1 t2) = S.unions [ftv t1, ftv t2, ftv q]
  ftv (TyQu _ tv t)   = S.delete tv (ftv t)
  ftv (TyMu tv t)     = S.delete tv (ftv t)
  ftv (TyAnti a)      = $antierror

instance (Data a, Ftv a) => Ftv (QExp a) where
  ftv = everything S.union (mkQ S.empty (ftv :: a -> S.Set TyVar))

instance Ftv a => Ftv [a] where
  ftv = S.unions . map ftv

instance Ftv TyVar where
  ftv = S.singleton

instance (Ftv a, Ftv b) => Ftv (a, b) where
  ftv (a, b) = ftv a `S.union` ftv b

class FtvVs a where
  ftvVs :: a -> M.Map TyVar Variance

instance FtvVs (Type TyTag) where
  ftvVs (TyCon _ ts td)= M.unionsWith (+)
                         [ M.map (* var) m
                         | var <- ttArity td
                         | m   <- map ftvVs ts ]
  ftvVs (TyArr q t1 t2)= M.unionsWith (+)
                         [ ftvVs q
                         , M.map negate (ftvVs t1)
                         , ftvVs t2 ]
  ftvVs (TyVar tv)     = M.singleton tv 1
  ftvVs (TyQu _ tv t)  = M.delete tv (ftvVs t)
  ftvVs (TyMu tv t)    = M.delete tv (ftvVs t)
  ftvVs (TyAnti a)     = antierror "ftvVs" a

instance (Data a, FtvVs a) => FtvVs (QExp a) where
  ftvVs = everything M.union
            (mkQ M.empty (ftvVs :: a -> M.Map TyVar Variance))

instance FtvVs a => FtvVs [a] where
  ftvVs = M.unionsWith (+) . map ftvVs

instance FtvVs TyVar where
  ftvVs tv = M.singleton tv 1

instance (FtvVs a, FtvVs b) => FtvVs (a, b) where
  ftvVs (a, b) = M.unionWith (+) (ftvVs a) (ftvVs b)

freshTyVars :: [TyVar] -> S.Set TyVar -> [TyVar]
freshTyVars tvs0 s0 = loop tvs0 (s0 `S.union` S.fromList tvs0) where
  loop (tv:tvs) s' = let tv' = freshTyVar tv s'
                      in tv' : loop tvs (S.insert tv' s')
  loop _        _ = []

freshTyVar :: TyVar -> S.Set TyVar -> TyVar
freshTyVar tv s = if tv `S.member` s
                    then loop count
                    else tv
  where
    suffix   = reverse . takeWhile isDigit . reverse . unLid $ tvname tv
    prefix   = reverse . dropWhile isDigit . reverse . unLid $ tvname tv
    count    = case reads suffix of
                 ((n, ""):_) -> n
                 _           -> 0
    attach n = tv { tvname = Lid (prefix ++ show n) }
    loop    :: Int -> TyVar
    loop n   =
      let tv' = attach n
      in if tv' `S.member` s
           then loop (n + 1)
           else tv'

-- | Given a list of type variables and types, perform all the
--   substitutions, avoiding capture between them.
tysubsts :: [TyVar] -> [TypeT] -> TypeT -> TypeT
tysubsts ps ts t =
  let ps'     = freshTyVars ps (ftv (t:ts))
      substs tvs ts0 t0 = foldr2 tysubst t0 tvs ts0 in
  substs ps' ts .
    substs ps (map TyVar ps') $
      t

-- | Type substitution
tysubst :: TyVar -> TypeT -> TypeT -> TypeT
tysubst a t = ts where
  ts (TyVar a')
                = if a' == a
                    then t
                    else TyVar a'
  ts (TyQu u a' t')
                = if a' == a
                    then TyQu u a' t'
                    else
                     let a'' = freshTyVar a' (ftv (a, [t, t']))
                      in TyQu u a'' (ts (tysubst a' (TyVar a'') t'))
  ts (TyMu a' t')
                = if a' == a
                    then TyMu a' t'
                    else
                     let a'' = freshTyVar a' (ftv (a, [t, t']))
                      in TyMu a'' (ts (tysubst a' (TyVar a'') t'))
  ts (TyCon c tys td)
                = TyCon c (map ts tys) td
  ts (TyArr q t1 t2)
                = TyArr q' (ts t1) (ts t2) where
    q' = qRepresent (qSubst a (qualifier t) (qInterpret q))
  ts (TyAnti an)= $(antierror 'an)

-- | Remove tycon information from a type
removeTyTags :: Type i -> Type ()
removeTyTags  = untype where
  untype :: Type i -> Type ()
  untype (TyCon con args _) = TyCon con (map untype args) ()
  untype (TyVar tv)         = TyVar tv
  untype (TyArr q t1 t2)    = TyArr q (untype t1) (untype t2)
  untype (TyQu quant tv t)  = TyQu quant tv (untype t)
  untype (TyMu tv t)        = TyMu tv (untype t)
  untype (TyAnti a)         = $antierror

-- | Given a type tag and something traversable, find all type tags
--   with the same identity as the given type tag, and replace them.
--   (We use this to do type abstraction, since we can replace datatype
--   type tags with abstract type tags that have the datacons redacted.)
replaceTyTags :: Data a => TyTag -> a -> a
replaceTyTags tag' = everywhere (mkT each) where
  each :: TyTag -> TyTag
  each tag | ttId tag == ttId tag' = tag'
           | otherwise             = tag

-- | The constant bound on the qualifier of a type
qualConst :: TypeT -> QLit
qualConst  = qConstBound . qualifier

-- | Find the qualifier of a type (which must be decorated with
--   tycon info)
qualifier     :: TypeT -> QDen TyVar
qualifier [$ty|+ ($list:ps) $qlid:_ $td |]
  = denumberQDen (map qualifier ps) (qInterpretCanonical (ttQual td))
qualifier [$ty|+ $_ -[$q]> $_ |]      = qInterpret (squashUnTyVars q)
qualifier [$ty|+ '$tv |]
  | tvqual tv <: Qu                   = minBound
  | otherwise                         = qInterpret (QeVar tv)
qualifier [$ty|+ $quant:_ '$_ . $t |] = qualifier t
qualifier [$ty|+ mu '$_ . $t |]       = qualifier t
qualifier [$ty|+ $anti:a |]           = $antierror

squashUnTyVars :: QExp TyVar -> QExp TyVar
squashUnTyVars = everywhere (mkT each) where
  each (QeVar tv) | tvqual tv <: Qu = QeLit Qu
  each qe = qe

-- | A fresh type for defining alpha equality up to mu.
newtype TypeTEq = TypeTEq { unTypeTEq :: TypeT }

-- | On TypeTEq, we define simple alpha equality, which we then use
-- to keep track of where we've been when we define type equality
-- that understands mu.
instance Eq TypeTEq where
  te1 == te2 = unTypeTEq te1 === unTypeTEq te2
    where
      (===) :: TypeT -> TypeT -> Bool
      [$ty|+ ($list:ps) $qlid:_ $td |]
        === [$ty|+@! ($list:ps') $qlid:_ $td' |]
                                 = td == td' && all2 (===) ps ps'
      TyVar x       === TyVar x' = x == x'
      TyArr q t1 t2 === TyArr q' t1' t2'
                                 = qInterpret q == qInterpret q'
                                   && t1 === t1' && t2 === t2'
      TyQu u x t    === TyQu u' x' t'
        | u == u' && tvqual x == tvqual x' =
          tysubst x a t === tysubst x' a t'
            where a = TyVar (freshTyVar x (ftv [t, t']))
      TyMu x t      === TyMu x' t'
        | tvqual x == tvqual x' =
          tysubst x a t === tysubst x' a t'
            where a = TyVar (freshTyVar x (ftv [t, t']))
      _             === _        = False

instance Eq (Type TyTag) where
  (==) t1i t2i = evalState (t1i `chk` t2i) [] where
    chk, cmp :: TypeT -> TypeT -> State [(TypeTEq, TypeTEq)] Bool
    t1 `chk` t2 = do
      seen <- get
      let te1 = TypeTEq t1; te2 = TypeTEq t2
      if (te1, te2) `elem` seen
        then return True
        else do
          put ((te1, te2) : (te2, te1) : seen)
          cmp t1 t2

    [$ty|+ $p $qlid:_ $td:dual |] `cmp` t = dualSessionType p `chk` t
    t `cmp` [$ty|+ $p $qlid:_ $td:dual |] = t `chk` dualSessionType p
    TyMu a t       `cmp` t'               = tysubst a (TyMu a t) t `chk` t'
    t'             `cmp` TyMu a t         = t' `chk` tysubst a (TyMu a t) t
    [$ty|+ ($list:ps) $qlid:_ $td |]
      `cmp` [$ty|+@! ($list:ps') $qlid:_ $td' |]
      | td == td'                         = allM2 chk ps ps'
    TyVar x        `cmp` TyVar x'         = return (x == x')
    TyArr q t1 t2  `cmp` TyArr q' t1' t2'
      | qInterpret q == qInterpret q'     = allM2 chk [t1,t2] [t1',t2']
    TyQu u x t     `cmp` TyQu u' x' t' 
      | u == u' && tvqual x == tvqual x'  =
        tysubst x a t `chk` tysubst x' a t'
          where a = TyVar (freshTyVar x (ftv [t, t']))
    _            `cmp` _                  = return False


-- | The Type partial order
instance PO (Type TyTag) where
  ifMJ bi t1i t2i = clean `liftM` chk [] bi t1i t2i where
    clean :: TypeT -> TypeT
    clean (TyCon c ps td)  = TyCon c (map clean ps) td
    clean (TyVar a)        = TyVar a
    clean (TyArr q t1 t2)  = TyArr q (clean t1) (clean t2)
    clean (TyQu u a t)     = TyQu u a (clean t)
    clean (TyMu a t)
      | a `S.member` ftv t = TyMu a (clean t)
      | otherwise          = clean t
    clean (TyAnti a)       = antierror "ifMJ" a

    chk, cmp :: Monad m =>
                [((Bool, TypeTEq, TypeTEq), TyVar)] ->
                Bool -> TypeT -> TypeT ->
                m TypeT
    chk seen b t1 t2 = do
      let te1 = TypeTEq t1; te2 = TypeTEq t2
      case lookup (b, te1, te2) seen of
        Just tv -> return (TyVar tv)
        Nothing -> TyMu tv `liftM` cmp seen' b t1 t2 where
          used  = S.fromList (map snd seen)
          tv    = freshTyVar
                    (TV (Lid "r") (qualConst t1 \/ qualConst t2))
                    (ftv [t1, t2] `S.union` used)
          seen' = (((b, te1, te2), tv) : ((b, te2, te1), tv) : seen)

    -- Special cases to treat "all 'a. 'a" as bottom:
    cmp _ b t'@(TyQu Forall tv (TyVar tv')) t
      | tv == tv' && qualConst t <: tvqual tv
      = return (if b then t else t')
    cmp _ b t t'@(TyQu Forall tv (TyVar tv'))
      | tv == tv' && qualConst t <: tvqual tv
      = return (if b then t else t')
    -- Special cases for session types duality:
    cmp seen b [$ty|+ $p $qlid:_ $td:dual |] t
                                    = chk seen b (dualSessionType p) t
    cmp seen b t [$ty|+ $p $qlid:_ $td:dual |]
                                    = chk seen b t (dualSessionType p)
    -- Arrows
    cmp seen b [$ty|+ $t11 -[$q1]> $t12 |]
               [$ty|+ $t21 -[$q2]> $t22 |] = do
        t1  <- chk seen (not b) t11 t21
        t2  <- chk seen b t12 t22
        q1' <- qInterpretM q1
        q2' <- qInterpretM q2
        q   <- qRepresent `liftM` ifMJ b q1' q2'
        return [$ty|+ $t1 -[$q]> $t2 |]
    -- Otherwise:
    cmp seen b [$ty|+ ($list:ps)  $qlid:tc $td  |]
               [$ty|+ ($list:ps') $qlid:_  $td' |] | td == td' = do
        params <- sequence
          [ case var of
              Covariant     -> chk seen b p p'
              Contravariant -> chk seen (not b) p p'
              _             -> if p == p'
                               then return p
                               else fail "\\/? or /\\?: Does not exist"
             | var <- ttArity td
             | p   <- ps
             | p'  <- ps' ]
        return [$ty|+ ($list:params) $qlid:tc $td |]
    cmp seen b (TyQu u a t) (TyQu u' a' t') | u == u' = do
      qual <- ifMJ (not b) (tvqual a) (tvqual a')
      let a1  = a { tvqual = qual } `freshTyVar` (ftv [t, t'])
          t1  = tysubst a (TyVar a1) t
          t'1 = tysubst a' (TyVar a1) t'
      TyQu u a1 `liftM` chk seen b t1 t'1
    cmp seen b (TyMu a t) t' = chk seen b (tysubst a (TyMu a t) t) t'
    cmp seen b t' (TyMu a t) = chk seen b t' (tysubst a (TyMu a t) t)
    cmp _    _ t t' | t == t' = return t
    cmp _    False t [$ty|+ U |] | qualConst t <: Qu = return t
    cmp _    False [$ty|+ U |] t | qualConst t <: Qu = return t
    cmp _    False t [$ty|+ A |] = return t
    cmp _    False [$ty|+ A |] t = return t
    cmp _    True t t'
      | qualConst t <: Qu && qualConst t' <: Qu = return [$ty|+ U |]
      | otherwise                               = return [$ty|+ A |]
    cmp _    _    _ _ = fail "\\/? or /\\?: Does not exist"

-- |
-- Helper for finding the dual of a session type (since we can't
-- express this directly in the type system at this point)
dualSessionType :: TypeT -> TypeT
dualSessionType  = d where
  d [$ty|+ $ta send $td:send ; $semi $tr |]
    = [$ty|+ $ta recv $td:recv ; $semi $tr' |] where tr' = d tr
  d [$ty|+ $ta recv $td:recv ; $semi $tr |]
    = [$ty|+ $ta send $td:send ; $semi $tr' |] where tr' = d tr
  d [$ty|+ ($t1 + $plus $t2) select $td:select |]
    = [$ty|+ ($t1' + $plus $t2') follow $td:follow |]
      where t1' = d t1; t2' = d t2
  d [$ty|+ ($t1 + $plus $t2) follow $td:follow |]
    = [$ty|+ ($t1' + $plus $t2') select $td:select |]
      where t1' = d t1; t2' = d t2
  d [$ty|+ mu '$tv . $t |]
    = [$ty|+ mu '$tv . $t' |] where t' = d t
  d t = t

