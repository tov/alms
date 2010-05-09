{-# LANGUAGE
      ParallelListComp,
      PatternGuards #-}
module TypeRel (
  -- * Type operations
  -- ** Equality and subtyping
  AType(..), subtype, jointype,
  -- ** Queries and conversions
  qualConst, abstractTyCon, replaceTyCon,
  -- * Tests
  tests,
) where

import Env
import Type
import Util

import Control.Monad.Error (MonadError(..))
import qualified Control.Monad.State as CMS
import Data.Generics (Data, everywhere, mkT, extT)
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Test.HUnit as T

-- | Remove the concrete portions of a type constructor.
abstractTyCon :: TyCon -> TyCon
abstractTyCon tc = tc { tcCons = ([], empty), tcNext = Nothing }

-- | Given a type constructor and something traversable, find all
--   constructors with the same identity as the given type one, and
--   replace them.  We can use this for type abstraction by redacting
--   data constructor or synonym expansions.
replaceTyCon :: Data a => TyCon -> a -> a
replaceTyCon tc' = everywhere (mkT tycon `extT` tyapp) where
  tycon :: TyCon -> TyCon
  tycon tc | tc == tc' = tc'
           | otherwise = tc
  tyapp :: Type -> Type
  tyapp (TyApp tc ts _)
    | tc == tc' = tyApp tc' ts
  tyapp t       = t

-- | The constant bound on the qualifier of a type
qualConst :: Type -> QLit
qualConst  = qConstBound . qualifier

{- -- deprecated?
squashUnTyVars :: QExp TyVar -> QExp TyVar
squashUnTyVars = everywhere (mkT each) where
  each (QeVar tv) | tvqual tv <: Qu = QeLit Qu
  each qe = qe
-}

-- | A fresh type for defining alpha equality up to mu.
newtype AType = AType { unAType :: Type }

-- | On AType, we define simple alpha equality, up to mu and operator
--   reduction, which we then use
--   to keep track of where we've been when we define type equality
--   that understands mu and reduction.
instance Eq AType where
  te1 == te2 = compare te1 te2 == EQ

instance Ord AType where
  te1 `compare` te2 = unAType te1 =?= unAType te2
    where
      (=?=) :: Type -> Type -> Ordering
      TyApp tc ts _ =?= TyApp tc' ts' _
        = tc `compare` tc'
           `thenCmp` map AType ts `compare` map AType ts'
      TyVar x       =?= TyVar x'
        = x `compare` x'
      TyFun q t1 t2 =?= TyFun q' t1' t2'
        = q `compare` q'
           `thenCmp` t1 =?= t1'
           `thenCmp` t2 =?= t2'
      TyQu u x t    =?= TyQu u' x' t'
        = u `compare` u'
           `thenCmp` tvqual x `compare` tvqual x'
           `thenCmp` tysubst x a t =?= tysubst x' a t'
              where a = TyVar (freshTyVar x (ftv (t, t')))
      TyMu x t    =?= TyMu x' t'
        = tvqual x `compare` tvqual x'
           `thenCmp` tysubst x a t =?= tysubst x' a t'
              where a = TyVar (freshTyVar x (ftv (t, t')))
      TyApp _ _ _   =?= _           = LT
      _             =?= TyApp _ _ _ = GT
      TyVar _       =?= _           = LT
      _             =?= TyVar _     = GT
      TyFun _ _ _   =?= _           = LT
      _             =?= TyFun _ _ _ = GT
      TyQu _ _ _    =?= _           = LT
      _             =?= TyQu _ _ _  = GT

instance Eq Type where
  t1 == t2 = t1 <: t2 && t2 <: t1

type UT s m a = CMS.StateT (TCS s) m a

data TCS s = TCS {
  tcsSeen    :: M.Map (AType, AType) s,
  tcsSubst1  :: M.Map TyVar Type,
  tcsSubst2  :: M.Map TyVar Type,
  tcsSupply  :: [QLit -> TyVar],
  tcsUvars1  :: M.Map TyVar (Type, Type),
  tcsUvars2  :: M.Map TyVar (Type, Type)
}

runUT  :: Monad m => UT s m a -> S.Set TyVar -> m a
runUT m set = CMS.evalStateT m TCS {
  tcsSeen   = M.empty,
  tcsSubst1 = M.empty,
  tcsSubst2 = M.empty,
  tcsSupply = [ f | f <- tvalphabet
                  , f Qu `S.notMember` set
                  , f Qa `S.notMember` set ],
  tcsUvars1 = M.empty,
  tcsUvars2 = M.empty
}

addUVars :: Monad m =>
            S.Set TyVar -> S.Set TyVar -> UT s m a ->
            UT s m (a, M.Map TyVar Type, M.Map TyVar Type)
addUVars set1 set2 body = do
  st0 <- CMS.get
  CMS.put st0 {
    tcsUvars1 = addSet set1 (tcsUvars1 st0),
    tcsUvars2 = addSet set2 (tcsUvars2 st0)
    }
  res <- body
  st1 <- CMS.get
  (new1, old1) <- partition set1 (tcsUvars1 st1)
  (new2, old2) <- partition set2 (tcsUvars2 st1)
  CMS.put st1 {
    tcsUvars1 = old1,
    tcsUvars2 = old2
    }
  return (res, new1, new2)
  where
    addSet set m =
      foldr (\tv -> M.insert tv (tyBot (tvqual tv), tyTop (tvqual tv)))
            m (S.toList set)
    partition set m = do
      let (new, old) = M.partitionWithKey (\tv _ -> S.member tv set) m
      new' <-
        M.fromList `liftM` sequence
          [ if lower <: upper
              then return (tv, if isTyBot lower then upper else lower)
              else fail $
                "Unification cannot solve: " ++
                show lower ++ " <: " ++ show upper
          | (tv, (lower, upper)) <- M.toList new ]
      return (new', old)

-- | Try to assert an upper bound on a unification variable, which
--   must be found on the left.
upperBoundUVar :: Monad m => TyVar -> Type -> UT s m ()
upperBoundUVar tv t = do
  st <- CMS.get
  let bounds = tcsUvars1 st
  case M.lookup tv bounds of
    Nothing -> fail $ "Free type variable: " ++ show tv
    Just (lower, upper) -> do
      upper' <- t /\? upper
      CMS.put st { tcsUvars1 = M.insert tv (lower, upper') bounds }

-- | Try to assert a lower bound on a unification variable, which
--   must be found on the right.
lowerBoundUVar :: Monad m => TyVar -> Type -> UT s m ()
lowerBoundUVar tv t = do
  st <- CMS.get
  let bounds = tcsUvars2 st
  case M.lookup tv bounds of
    Nothing -> fail $ "Free type variable: " ++ show tv
    Just (lower, upper) -> do
      lower' <- t \/? lower
      CMS.put st { tcsUvars2 = M.insert tv (lower', upper) bounds }

getUVars :: Monad m => UT s m (M.Map TyVar (Type, Type),
                               M.Map TyVar (Type, Type))
getUVars = do
  st <- CMS.get
  return (tcsUvars1 st, tcsUvars2 st)

chkU :: Monad m => Type -> Type -> s -> UT s m s -> UT s m s
chkU t1 t2 s body = do
  let key = (AType t1, AType t2)
  st0 <- CMS.get
  case M.lookup key (tcsSeen st0) of
    Just s' -> return s'
    Nothing -> do
      CMS.put st0 { tcsSeen = M.insert key s (tcsSeen st0) }
      res <- body
      st1 <- CMS.get
      CMS.put st1 { tcsSeen = M.insert key res (tcsSeen st1) }
      return res

get1U :: Monad m => TyVar -> UT s m (Maybe Type)
get1U tv = (M.lookup tv . tcsSubst1) `liftM` CMS.get

get2U :: Monad m => TyVar -> UT s m (Maybe Type)
get2U tv = (M.lookup tv . tcsSubst2) `liftM` CMS.get

add1U :: Monad m => TyVar -> Type -> UT s m a -> UT s m a
add1U tv t body = do
  st0 <- CMS.get
  CMS.put st0 { tcsSubst1 = M.insert tv t (tcsSubst1 st0) }
  res <- body
  st1 <- CMS.get
  CMS.put st1 { tcsSubst1 = tcsSubst1 st0 }
  return res

add2U :: Monad m => TyVar -> Type -> UT s m a -> UT s m a
add2U tv t body = do
  st0 <- CMS.get
  CMS.put st0 { tcsSubst2 = M.insert tv t (tcsSubst2 st0) }
  res <- body
  st1 <- CMS.get
  CMS.put st1 { tcsSubst2 = tcsSubst2 st0 }
  return res

flipU :: Monad m => UT s m a -> UT s m a
flipU body = do
  CMS.modify flipSt
  res <- body
  CMS.modify flipSt
  return res
    where
      flipSt (TCS seen s1 s2 supply u1 u2) =
        TCS (M.mapKeys (\(x,y) -> (y,x)) seen) s2 s1 supply u2 u1

freshU :: Monad m => QLit -> UT s m TyVar
freshU qlit = do
  st <- CMS.get
  let f:supply = tcsSupply st
  CMS.put st { tcsSupply = supply }
  return (f qlit)

hideU :: Monad m => UT s m a -> UT s m a
hideU body = do
  st0 <- CMS.get
  CMS.put st0 { tcsSubst1 = M.empty, tcsSubst2 = M.empty }
  res <- body
  st1 <- CMS.get
  CMS.put st1 { tcsSubst1 = tcsSubst1 st0, tcsSubst2 = tcsSubst2 st0 }
  return res

subtype :: MonadError e m =>
           Int ->
           S.Set TyVar -> Type ->
           S.Set TyVar -> Type ->
           m (M.Map TyVar Type, M.Map TyVar Type)
subtype limit uvars1 t1i uvars2 t2i =
  liftM (\(_, m1, m2) -> (m1, m2)) $
    runUT
      (addUVars uvars1 uvars2 $ cmp t1i t2i)
      (uvars1 `S.union` uvars2 `S.union` ftv (t1i, t2i))
  where
    cmp :: MonadError e m => Type -> Type -> UT () m ()
    cmp t u = chkU t u () $ case (t, u) of
      -- Handle top
      (_ , TyApp tcu _ _)
        | tcu == tcUn && qualConst t <: Qu
        -> return ()
      (_ , TyApp tcu _ _)
        | tcu == tcAf
        -> return ()
      -- Handle bottom (other Forall case below depends on this
      -- to bottom out)
      (TyQu Forall tvt (TyVar tvt'), _)
        | tvt == tvt'
        -> return ()
      -- Variables
      (TyVar vt, TyVar vu) -> do
        mt' <- get1U vt
        mu' <- get2U vu
        case (mt', mu') of
          (Just t', Just u') -> cmp t' u'
          (Nothing, Just u') -> upperBoundUVar vt u'
          (Just t', Nothing) -> lowerBoundUVar vu t'
          (Nothing, Nothing) -> unless (vt == vu) $ giveUp t u
      (TyVar vt, _) -> do
        mt' <- get1U vt
        case mt' of
          Just t' -> cmp t' u
          Nothing -> upperBoundUVar vt u
      (_, TyVar vu) -> do
        mu' <- get2U vu
        case mu' of
          Just u' -> cmp t u'
          Nothing -> lowerBoundUVar vu t
      -- Type applications
      (TyApp tct ts _, TyApp tcu us _)
        | tct == tcu,
          isHeadNormalType t, isHeadNormalType u ->
        cmpList (tcArity tct) ts us
      (TyApp tct ts _, TyApp tcu us _)
        | tct == tcu ->
        cmpList (tcArity tct) ts us `catchError` \_ -> do
          t' <- hn t
          u' <- hn u
          cmp t' u'
      (TyApp _ _ _, _)
        | not (isHeadNormalType t)
        -> (`cmp` u) =<< hn t
      (_, TyApp _ _ _)
        | not (isHeadNormalType u)
        -> (t `cmp`) =<< hn u
      -- Arrows
      (TyFun qt t1 t2, TyFun qu u1 u2) -> do
        subkind qt qu $ giveUp t u
        revCmp t1 u1
        cmp t2 u2
      -- Quantifiers
      (TyQu qt tvt t1, TyQu qu tvu u1)
        | qt == qu,
          tvqual tvu <: tvqual tvt -> do
        tv' <- freshU (tvqual tvu)
        hideU $
          cmp (tysubst tvt (TyVar tv') t1)
              (tysubst tvu (TyVar tv') u1)
      (TyQu Forall tvt t1, _) -> do
        tv' <- freshU (tvqual tvt)
        addUVars (S.singleton tv') S.empty $
          hideU $
            cmp (tysubst tvt (TyVar tv') t1) u
        return ()
      -- Recursion
      (TyMu tvt t1, _) ->
        -- Need to rename to dodge unification variables
        add1U tvt t $ cmp t1 u
      (_, TyMu tvu u1) ->
        add2U tvu u $ cmp t u1
      -- Failure
      (_, _) -> giveUp t u
    --
    giveUp t u = 
      fail $
        "Got type `" ++ show t ++ "' where type `" ++
        show u ++ "' expected"
    --
    revCmp u t = flipU (cmp t u)
    --
    hn t = headNormalizeTypeM limit t
    --
    cmpList arity ts us =
      sequence_
        [ case var of
            1  -> cmp tj uj
            -1 -> revCmp tj uj
            _  -> do cmp tj uj; revCmp tj uj
        | var      <- arity
        | tj       <- ts
        | uj       <- us ]
    --
    subkind qd1 qd2 orElse =
      if qd1 <: qd2 then return () else do
        (m1, m2) <- getUVars
        case (qRepresent qd1, qRepresent qd2) of
          (QeVar tv1, QeVar tv2)
            | M.member tv1 m1, not (M.member tv2 m2)
            -> upperBoundUVar tv1 (TyVar tv2)
            | not (M.member tv1 m1), M.member tv2 m2
            -> lowerBoundUVar tv2 (TyVar tv1)
          (QeVar tv1, QeLit qlit)
            | M.member tv1 m1
            -> upperBoundUVar tv1 (tyTop qlit)
          (QeLit qlit, QeVar tv2)
            | M.member tv2 m2
            -> lowerBoundUVar tv2 (tyTop qlit)
          _ -> orElse

jointype :: MonadError e m => Int -> Bool -> Type -> Type -> m Type
jointype limit b t1i t2i =
  liftM clean $ runUT (cmp (b, True) t1i t2i) (ftv (t1i, t2i))
  where
  cmp, revCmp :: MonadError e m =>
                 (Bool, Bool) -> Type -> Type -> UT Type m Type
  cmp m t u = do
    let (direction, _) = m
    tv   <- freshU (qualConst t \/ qualConst u)
    catchTop m t u $
      chkU t u (TyVar tv) $
        TyMu tv `liftM`
          case (t, u) of
      -- Handle top and bottom
      _ | Just t' <- points direction t u -> return t'
        | Just t' <- points direction u t -> return t'
      -- Variables
      (TyVar vt, TyVar ut)
        | vt == ut ->
        return t
      (TyVar vt, _) -> do
        Just t' <- get1U vt
        cmp m t' u
      (_, TyVar ut) -> do
        Just u' <- get2U ut
        cmp m t u'
      -- Type applications
      (TyApp tct ts _, TyApp tcu us _)
        | tct == tcu,
          isHeadNormalType t, isHeadNormalType u ->
        tyApp tct `liftM`
          cmpList (tcArity tct) (direction, True) ts us
      (TyApp tct ts _, TyApp tcu us _)
        | tct == tcu
        -> liftM (tyApp tct)
                 (cmpList (tcArity tct) (direction, False) ts us)
             `catchError` \_ -> do
               t' <- hn t
               u' <- hn u
               cmp m t' u'
      (TyApp _ _ _, _)
        | not (isHeadNormalType t) -> do
        t' <- hn t
        cmp m t' u
      (_, TyApp _ _ _)
        | not (isHeadNormalType u) -> do
        u' <- hn u
        cmp m t u'
      -- Arrows
      (TyFun qt t1 t2, TyFun qu u1 u2) -> do
        q'  <- ifMJ direction qt qu
        t1' <- revCmp m t1 u1
        t2' <- cmp m t2 u2
        return (TyFun q' t1' t2')
      -- Quantifiers
      (TyQu qt tvt t1, TyQu qu tvu u1)
        | qt == qu -> do
        q'  <- ifMJ direction (tvqual tvt) (tvqual tvu)
        tv' <- freshU q'
        liftM (TyQu qt tv') $
          hideU $
            cmp m (tysubst tvt (TyVar tv') t1)
                  (tysubst tvu (TyVar tv') u1)
      -- Recursion
      (TyMu tvt t1, _) ->
        add1U tvt t $ cmp m t1 u
      (_, TyMu tvu u1) ->
        add2U tvu u $ cmp m t u1
      -- Failure
      _ ->
        fail $
          "Could not " ++ (if direction then "join" else "meet") ++
          " types `" ++ show t ++
          "' and `" ++ show u ++ "'"
  --
  hn t = headNormalizeTypeM limit t
  --
  cmpList arity m ts us =
    sequence
      [ case var of
          1  -> cmp m tj uj
          -1 -> revCmp m tj uj
          _  -> if tj == uj
                  then return tj
                  else fail $
                    "Could not unify types `" ++ show tj ++
                    "' and `" ++ show uj ++ "'"
      | var      <- arity
      | tj       <- ts
      | uj       <- us ]
  --
  points True  t u@(TyApp tc _ _)
    | tc == tcAf                    = Just u
    | tc == tcUn, qualConst t <: Qu = Just u
  points True  t   (TyQu Forall tv (TyVar tv'))
    | tv == tv'                     = Just t
  points False t   (TyApp tc _ _)
    | tc == tcAf                    = Just t
    | tc == tcUn, qualConst t <: Qu = Just t
  points False _ u@(TyQu Forall tv (TyVar tv'))
    | tv == tv'                     = Just u
  points _     _   _                = Nothing
  --
  revCmp (direction, lossy) t u = cmp (not direction, lossy) t u
  --
  catchTop (True, True) t u body = body
    `catchError` \_ -> return (tyTop (qualConst t \/ qualConst u))
  catchTop _            _ _ body = body
  --
  clean :: Type -> Type
  clean (TyApp tc ts _)  = tyApp tc (map clean ts)
  clean (TyVar a)        = TyVar a
  clean (TyFun q t1 t2)  = TyFun q (clean t1) (clean t2)
  clean (TyQu u a t)     = TyQu u a (clean t)
  clean (TyMu a t)
    | a `S.member` ftv t = TyMu a (clean t)
    | otherwise          = clean t

-- | Helper to force 'Either' to the right type
runEither :: (String -> r) -> (a -> r) -> Either String a -> r
runEither  = either

-- | The Type partial order
instance PO Type where
  t1 <: t2     = runEither (const False) (const True)
                           (subtype 100 S.empty t1 S.empty t2)
  ifMJ b t1 t2 = runEither fail return (jointype 100 b t1 t2)

subtypeTests, joinTests, uvarsTests :: T.Test

subtypeTests = T.test
  [ tyUnit  <:! tyUnit
  , tyUnit !<:  tyInt
  , tyInt   <:! tyInt
  , tyInt  .->. tyInt   <:! tyInt .->. tyInt
  , tyInt  .->. tyInt   <:! tyInt .-*. tyInt
  , tyInt  .-*. tyInt   <:! tyInt .-*. tyInt
  , tyInt  .-*. tyInt  !<:  tyInt .->. tyInt
  , tyUnit .->. tyInt  !<:  tyInt .->. tyInt
  , (tyInt .-*. tyInt) .->. tyInt .->. tyInt <:!
    (tyInt .->. tyInt) .->. tyInt .-*. tyInt 
  , tyInt .->. tyInt  <:! tyUn
  , tyInt .->. tyInt  <:! tyAf
  , tyInt .-*. tyInt !<:  tyUn
  , tyInt .-*. tyInt  <:! tyAf
  , tyUn  <:! tyAf
  , tyAf !<:  tyUn
  , tyRecv tyInt  <:! tyRecv tyInt
  , tyRecv tyInt !<:  tyRecv tyUnit
  , tyRecv tyInt !<:  tySend tyInt
  , tyRecv (tyInt .-*. tyInt)  <:! tyRecv (tyInt .->. tyInt)
  , tyRecv (tyInt .->. tyInt) !<:  tyRecv (tyInt .-*. tyInt)
  , tySend (tyInt .-*. tyInt) !<:  tySend (tyInt .->. tyInt)
  , tySend (tyInt .->. tyInt)  <:! tySend (tyInt .-*. tyInt)
  , tyIdent tyInt  <:! tyIdent tyInt
  , tyIdent tyInt !<:  tyIdent tyUnit
  , tyInt          <:! tyIdent tyInt
  , tyIdent tyInt  <:! tyInt
  , tyInt         !<:  tyIdent tyUnit
  , tyIdent tyInt !<:  tyUnit
  , tyConst tyInt  <:! tyConst tyInt
  , tyConst tyInt  <:! tyConst tyUnit
  , tyConst tyInt  <:! tyUnit
  , tyUnit         <:! tyConst tyInt
  , tyUnit .->. tyInt <:! tyIdent (tyConst (tySend tyInt) .-*. tyInt)
  , tyInt .->. tyInt !<:  tyIdent (tyConst (tySend tyInt) .-*. tyInt)
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) <:!
    tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit)
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) <:!
    tySend tyInt .:. tyDual (tySend tyUnit .:. tyUnit) 
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) <:!
    tySend tyInt .:. tyRecv tyUnit .:. tyUnit 
  , tyAll a (TyVar a)  <:! tyInt .->. tyInt
  , tyInt .->. tyInt !<:  tyAll a (TyVar a)
  , TyVar a  <:! TyVar a
  , TyVar a !<:  TyVar b
  , tyAll a (tyInt .->. TyVar a)  <:! tyAll b (tyInt .->. TyVar b)
  , tyAll a (tyInt .->. TyVar a) !<:  tyAll b (tyInt .->. TyVar a)
  , tyAll c (TyVar c .->. tyInt)  <:! tyAll a (TyVar a .-*. tyInt)
  , tyAll a (TyVar a .->. tyInt) !<:  tyAll c (TyVar c .-*. tyInt)
  , tyAll a (tyAll b (TyVar a .*. TyVar b))  <:!
    tyAll b (tyAll a (TyVar b .*. TyVar a))
  , tyAll a (tyAll b (TyVar a .*. TyVar b)) !<:
    tyAll b (tyAll a (TyVar a .*. TyVar b))
  , tyAll a (tyAll a (TyVar a .*. TyVar b)) !<:
    tyAll b (tyAll a (TyVar a .*. TyVar b))
  , tyAll a (tyAll a (TyVar a .*. TyVar b))  <:!
    tyAll a (tyAll a (TyVar a .*. TyVar b))
  , TyMu a (tyInt .->. TyVar a)  <:!
    TyMu b (tyInt .->. TyVar b)
  , TyMu a (tyInt .->. TyVar a)  <:!
    TyMu b (tyInt .->. tyInt .->. TyVar b)
  , TyMu a (tyInt .->. TyVar a)  <:!
    TyMu b (tyInt .->. tyInt .-*. TyVar b)
  , TyMu a (tyInt .->. TyVar a) !<:
    TyMu b (tyInt .->. tyUnit .-*. TyVar b)
  , TyMu a (TyVar a .*. tyInt .*. tyInt) <:!
    TyMu a (TyVar a .*. tyInt .*. tyInt) .*. tyInt 
  , TyMu a (TyVar a .*. tyInt .*. tyUnit) <:!
    TyMu a (TyVar a .*. tyUnit .*. tyInt) .*. tyUnit 
  , tyAll c (TyMu a (TyVar a .*. tyInt .*. TyVar c))  <:!
    tyAll d (TyMu a (TyVar a .*. TyVar d .*. tyInt) .*. TyVar d)
  , tyAll c (TyMu a (TyVar a .*. tyInt .*. TyVar c)) !<:
    tyAll d (TyMu a (TyVar d .*. TyVar a .*. tyInt) .*. TyVar d)
  , TyMu a (tyAll c ((tyInt .-*. TyVar c) .->. TyVar a)) !<:
    TyMu b (tyAll d ((tyInt .->. TyVar d) .->. TyVar c))
  , TyMu a (tyAll c (tyInt .-*. TyVar c) .->. TyVar a)  <:!
    TyMu b (tyAll d (tyInt .->. TyVar d) .->. TyVar b)
  , TyMu a (tyAll c (TyVar a .-*. TyVar c) .->. TyVar a) !<:
    TyMu b (tyAll d (TyVar b .->. TyVar d) .->. TyVar b)
  , tyAll a (TyVar a .*. tyInt) .->. TyVar a  <:!
    tyAll b (TyVar b .*. tyInt) .->. TyVar a 
  , tyAll a (TyVar a .*. tyInt) .->. TyVar a !<:
    tyAll b (TyVar b .*. tyInt) .->. TyVar b 
  -- Universal instantiation tests
  , tyAll a (TyVar a .->. TyVar a)  <:! tyInt .->. tyInt
  , tyAll a (TyVar a .->. TyVar a) !<:  tyInt .->. tyUnit
  , tyInt .->. tyInt !<: tyAll a (TyVar a .->. TyVar a)
  , tyAll a (TyVar a .->. tyInt)  <:! tyInt .->. tyInt
  , tyAll a (tyInt   .->. tyInt)  <:! tyInt .->. tyInt
  , tyInt .->. tyAll a (TyVar a .->. TyVar a) <:!
    tyInt .->.          tyInt   .->. tyInt
  , TyMu a (TyVar a .*. (tyAll a (TyVar a .->. TyVar a)))  <:!
    TyMu a (TyVar a .*.          (tyInt   .->. tyInt))
  , TyMu a (TyVar a .*. (tyAll a (tyInt   .->. TyVar a)))  <:!
    TyMu a (TyVar a .*.          (tyInt   .->. tyInt))
  , TyMu b (TyVar b .*. (tyAll a (TyVar a .->. TyVar a)))  <:!
    TyMu a (TyVar a .*.          (tyInt   .->. tyInt))
  , TyMu b (TyVar b .*. (tyAll a (tyInt   .->. TyVar a)))  <:!
    TyMu a (TyVar a .*.          (tyInt   .->. tyInt))
  , TyMu a (tyAll b (TyVar b .->. TyVar a))  !<:
    TyMu a          (tyInt   .->. TyVar a)
  , tyAll a (TyVar a .*. tyInt)    <:! TyMu a (TyVar a .*. tyInt)
  , tyAll a (TyVar a .*. TyVar a) !<: TyMu a (TyVar a .*. tyInt)
  , tyAll a (TyMu b (TyVar a .->. TyVar b))  <:!
    TyMu b (tyInt .->. TyVar b)
  , tyAll a (TyMu a (tyInt .->. TyVar a))   !<:
    TyMu b (tyInt .->. tyInt)
  , tyAll a (tyInt .->. TyVar a) .->. tyInt !<:
    (tyInt .->. tyInt) .->. tyInt
  , (tyInt .->. tyInt) .->. tyInt            <:!
    tyAll a (tyInt .->. TyVar a) .->. tyInt
  , tyAll a (tyInt .->. TyVar a) !<: tyInt .->. tyInt .-*. tyInt
  ]
  where
  t1  <:! t2 = T.assertBool (show t1 ++ " <: " ++ show t2) (t1 <: t2)
  t1 !<:  t2 = T.assertBool (show t1 ++ " /<: " ++ show t2) (t1 /<: t2)
  infix 4 <:!, !<:
  a = tvUn "a"; b = tvUn "b"; c = tvAf "c"; d = tvAf "d"

joinTests = T.test
  [ tyUnit  \/! tyUnit ==! tyUnit
  , tyUnit  /\! tyUnit ==! tyUnit
  , tyInt   /\! tyInt  ==! tyInt
  , tyUnit  \/! tyInt  ==! tyUn
  , tyUnit !/\  tyInt
  , tyInt .->. tyInt  \/! tyInt .->. tyInt  ==! tyInt .->. tyInt
  , tyInt .->. tyInt  \/! tyInt .-*. tyInt  ==! tyInt .-*. tyInt
  , tyInt .-*. tyInt  \/! tyInt .-*. tyInt  ==! tyInt .-*. tyInt
  , tyInt .-*. tyInt  \/! tyInt .->. tyInt  ==! tyInt .-*. tyInt
  , tyInt .->. tyInt  /\! tyInt .->. tyInt  ==! tyInt .->. tyInt
  , tyInt .->. tyInt  /\! tyInt .-*. tyInt  ==! tyInt .->. tyInt
  , tyInt .-*. tyInt  /\! tyInt .-*. tyInt  ==! tyInt .-*. tyInt
  , tyInt .-*. tyInt  /\! tyInt .->. tyInt  ==! tyInt .->. tyInt
  , tyInt .->. tyInt  \/! tyInt .->. tyUnit ==! tyInt .->. tyUn
  , tyInt .->. tyInt  \/! tyUnit .->. tyInt ==! tyUn
  , tyInt .-*. tyInt  \/! tyUnit .->. tyInt ==! tyAf
  , tyInt .->. tyInt !/\  tyInt .->. tyUnit
  , tyInt .->. tyInt  /\! tyUnit .->. tyInt ==! tyUn .->. tyInt
  , tyInt .-*. tyInt  /\! tyUnit .->. tyInt ==! tyUn .->. tyInt
  , (tyInt .-*. tyInt) .-*. tyInt /\! tyUnit .->. tyInt
      ==! tyAf .->. tyInt
  , tyInt .->. tyInt  \/! tyUn ==! tyUn
  , tyInt .->. tyInt  \/! tyAf ==! tyAf
  , tyInt .-*. tyInt  \/! tyUn ==! tyAf
  , tyInt .-*. tyInt  \/! tyAf ==! tyAf
  , tyInt .->. tyInt  /\! tyUn ==! tyInt .->. tyInt
  , tyInt .->. tyInt  /\! tyAf ==! tyInt .->. tyInt
  , tyInt .-*. tyInt !/\  tyUn -- could do better
  , tyInt .-*. tyInt  /\! tyAf ==! tyInt .-*. tyInt
  , tyRecv tyInt \/! tyRecv tyInt  ==! tyRecv tyInt
  , tySend tyInt \/! tySend tyUnit ==! tySend tyUn
  , tyRecv tyInt \/! tySend tyInt  ==! tyUn
  , tyRecv (tyInt .-*. tyInt) \/!
    tyRecv (tyInt .->. tyInt) ==!
    tyRecv (tyInt .->. tyInt)
  , tyRecv (tyInt .->. tyInt) \/!
    tyRecv (tyInt .-*. tyInt) ==!
    tyRecv (tyInt .->. tyInt)
  , tySend (tyInt .-*. tyInt) \/!
    tySend (tyInt .->. tyInt) ==!
    tySend (tyInt .-*. tyInt)
  , tySend (tyInt .->. tyInt) \/!
    tySend (tyInt .-*. tyInt) ==!
    tySend (tyInt .-*. tyInt)
  , tyRecv (tyInt .-*. tyInt) /\!
    tyRecv (tyInt .->. tyInt) ==!
    tyRecv (tyInt .-*. tyInt)
  , tyRecv (tyInt .->. tyInt) /\!
    tyRecv (tyInt .-*. tyInt) ==!
    tyRecv (tyInt .-*. tyInt)
  , tySend (tyInt .-*. tyInt) /\!
    tySend (tyInt .->. tyInt) ==!
    tySend (tyInt .->. tyInt)
  , tySend (tyInt .->. tyInt) /\!
    tySend (tyInt .-*. tyInt) ==!
    tySend (tyInt .->. tyInt)
  , tyIdent tyInt  \/! tyIdent tyInt  ==! tyIdent tyInt
  , tyIdent tyInt  \/! tyIdent tyUnit ==! tyUn
  , tyInt          \/! tyIdent tyInt  ==! tyInt
  , tyInt          \/! tyIdent tyUnit ==! tyUn
  , tyIdent tyInt  /\! tyIdent tyInt  ==! tyIdent tyInt
  , tyIdent tyInt !/\  tyIdent tyUnit
  , tyInt          /\! tyIdent tyInt  ==! tyInt
  , tyInt         !/\  tyIdent tyUnit
  , tyIdent (tyIdent tyInt) \/! tyIdent tyInt            ==! tyIdent tyInt
  , tyIdent (tyConst tyInt) \/! tyIdent (tyConst tyUnit) ==! tyIdent tyUnit
  , tyConst tyInt  \/! tyConst tyInt   ==! tyConst tyInt
  , tyConst tyInt  \/! tyConst tyUnit  ==! tyUnit
  , tyConst tyInt  /\! tyConst tyInt   ==! tyConst tyInt
  , tyConst tyInt  /\! tyConst tyUnit  ==! tyUnit
  , tyUnit .->. tyInt  \/! tyIdent (tyConst (tySend tyInt) .-*. tyInt)
      ==! tyUnit .-*. tyInt
  , tyInt .->. tyInt   \/! tyIdent (tyConst (tySend tyInt) .-*. tyInt)
      ==! tyAf
  , tyUnit .->. tyInt  /\! tyIdent (tyConst (tySend tyInt) .-*. tyInt)
      ==! tyUnit .->. tyInt
  , tyInt .->. tyInt   /\! tyIdent (tyConst (tySend tyInt) .-*. tyInt)
      ==! tyUn .->. tyInt
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) \/!
    tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) ==!
    tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit)
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) \/!
    tySend tyInt .:. tyDual (tySend tyUnit .:. tyUnit)  ==!
    tySend tyInt .:. tyDual (tySend tyUnit .:. tyUnit) 
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) \/!
    tySend tyInt .:. tyRecv tyUnit .:. tyUnit  ==!
    tySend tyInt .:. tyRecv tyUnit .:. tyUnit 
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) /\!
    tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) ==!
    tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit)
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) /\!
    tySend tyInt .:. tyDual (tySend tyUnit .:. tyUnit)  ==!
    tySend tyInt .:. tyDual (tySend tyUnit .:. tyUnit) 
  , tyDual (tyRecv tyInt .:. tySend tyUnit .:. tyUnit) /\!
    tySend tyInt .:. tyRecv tyUnit .:. tyUnit  ==!
    tySend tyInt .:. tyRecv tyUnit .:. tyUnit 
  , tyAll a (TyVar a)  \/! tyInt .->. tyInt ==! tyInt .->. tyInt
  , tyInt .->. tyInt  /\! tyAll a (TyVar a) ==! tyAll b (TyVar b)
  , TyVar a  \/! TyVar a ==! TyVar a
  , TyVar a  \/! TyVar b ==! tyUn
  , TyVar a  \/! TyVar c ==! tyAf
  , TyVar a  /\! TyVar a ==! TyVar a
  , TyVar a !/\  TyVar b
  , TyVar a !/\  TyVar c
  , tyAll a (tyInt .->. TyVar a)  \/!  tyAll b (tyInt .->. TyVar b)
      ==! tyAll a (tyInt .->. TyVar a)
  , tyAll a (tyInt .->. TyVar a)  \/!  tyAll b (tyInt .->. TyVar a)
      ==! tyAll a (tyInt .->. tyUn)
  , tyAll c (TyVar c .->. tyInt)  \/! tyAll a (TyVar a .-*. tyInt)
      ==! tyAll d (TyVar d .-*. tyInt)
  , tyAll a (tyInt .->. TyVar a)  /\!  tyAll b (tyInt .->. TyVar b)
      ==! tyAll a (tyInt .->. TyVar a)
  , tyAll a (tyInt .->. TyVar a) !/\   tyAll b (tyInt .->. TyVar a)
  , tyAll c (TyVar c .->. tyInt)  /\!
    tyAll a (TyVar a .-*. tyInt)  ==!
    tyAll b (TyVar b .->. tyInt)
  , tyAll a (tyAll b (TyVar a .*. TyVar b))  \/!
    tyAll b (tyAll a (TyVar b .*. TyVar a))  ==!
    tyAll b (tyAll a (TyVar b .*. TyVar a))
  , tyAll a (tyAll b (TyVar a .*. TyVar b))  \/!
    tyAll b (tyAll a (TyVar a .*. TyVar b))  ==!
    tyAll b (tyAll a (tyUn .*. tyUn))
  , tyAll c (tyAll c (TyVar c .*. TyVar d))  \/!
    tyAll d (tyAll c (TyVar c .*. TyVar d))  ==!
    tyAll d (tyAll d (TyVar d .*. tyAf))
  , tyAll a (tyAll a (TyVar a .*. TyVar b))  \/!
    tyAll a (tyAll a (TyVar a .*. TyVar b))  ==!
    tyAll a (tyAll a (TyVar a .*. TyVar b))
  , tyAll a (tyAll b (TyVar a .*. TyVar b))  /\!
    tyAll b (tyAll a (TyVar b .*. TyVar a))  ==!
    tyAll b (tyAll a (TyVar b .*. TyVar a))
  , tyAll a (tyAll b (TyVar a .*. TyVar b)) !/\
    tyAll b (tyAll a (TyVar a .*. TyVar b))
  , tyAll c (tyAll c (TyVar c .*. TyVar d)) !/\
    tyAll d (tyAll c (TyVar c .*. TyVar d))
  , tyAll a (tyAll a (TyVar a .*. TyVar b))  /\!
    tyAll a (tyAll a (TyVar a .*. TyVar b))  ==!
    tyAll a (tyAll a (TyVar a .*. TyVar b))
  , TyMu a (tyInt .->. TyVar a)  \/!
    TyMu b (tyInt .->. TyVar b)  ==!
    TyMu b (tyInt .->. TyVar b)
  , TyMu a (tyInt .->. TyVar a)  /\!
    TyMu b (tyInt .->. TyVar b)  ==!
    TyMu b (tyInt .->. TyVar b)
  , TyMu a (tyInt .->. TyVar a)            \/!
    TyMu b (tyInt .->. tyInt .->. TyVar b) ==!
    TyMu a (tyInt .->. TyVar a)
  , TyMu a (tyInt .->. TyVar a)            /\!
    TyMu b (tyInt .->. tyInt .->. TyVar b) ==!
    TyMu a (tyInt .->. TyVar a)
  , TyMu a (tyInt .->. TyVar a)            \/!
    TyMu b (tyInt .->. tyInt .-*. TyVar b) ==!
    TyMu b (tyInt .->. tyInt .-*. TyVar b)
  , TyMu a (tyInt .->. TyVar a)            /\!
    TyMu b (tyInt .->. tyInt .-*. TyVar b) ==!
    TyMu b (tyInt .->. TyVar b)
  , TyMu a (tyInt .->. TyVar a)             \/!
    TyMu b (tyInt .->. tyUnit .-*. TyVar b) ==!
    tyInt .->. tyAf
  , TyMu a (tyInt .->. TyVar a)             /\!
    TyMu b (tyInt .->. tyUnit .-*. TyVar b) ==!
    TyMu a (tyInt .->. tyUn .->. TyVar a)
  , TyMu a (TyVar a .*. tyInt .*. tyInt)           \/!
    TyMu a (TyVar a .*. tyInt .*. tyInt) .*. tyInt ==!
    TyMu a (TyVar a .*. tyInt)
  , TyMu a (TyVar a .*. tyInt .*. tyInt)           /\!
    TyMu a (TyVar a .*. tyInt .*. tyInt) .*. tyInt ==!
    TyMu a (TyVar a .*. tyInt)
  , TyMu a (TyVar a .*. tyInt .*. tyUnit)            \/!
    TyMu a (TyVar a .*. tyUnit .*. tyInt) .*. tyUnit ==!
    TyMu b (TyVar b .*. tyInt .*. tyUnit)
  , TyMu a (TyVar a .*. tyInt .*. tyUnit)            /\!
    TyMu a (TyVar a .*. tyUnit .*. tyInt) .*. tyUnit ==!
    TyMu b (TyVar b .*. tyInt .*. tyUnit)
  , tyAll c (TyMu a (TyVar a .*. tyInt .*. TyVar c))             \/!
    tyAll d (TyMu a (TyVar a .*. TyVar d .*. tyInt) .*. TyVar d) ==!
    tyAll c (TyMu b (TyVar b .*. tyInt .*. TyVar c))
  , tyAll c (TyMu a (TyVar a .*. tyInt .*. TyVar c))             /\!
    tyAll d (TyMu a (TyVar a .*. TyVar d .*. tyInt) .*. TyVar d) ==!
    tyAll c (TyMu b (TyVar b .*. tyInt .*. TyVar c))
  , tyAll c (TyMu a (TyVar a .*. tyInt .*. TyVar c))             \/!
    tyAll d (TyMu a (TyVar d .*. TyVar a .*. tyInt) .*. TyVar d) ==!
    tyAll c (tyAf .*. tyAf .*. tyInt .*. TyVar c)
  , tyAll c (TyMu a (TyVar a .*. tyInt .*. TyVar c))            !/\
    tyAll d (TyMu a (TyVar d .*. TyVar a .*. tyInt) .*. TyVar d)
  , TyMu a (tyAll c (tyInt .-*. TyVar c) .->. TyVar a)           \/!
    TyMu b (tyAll d (tyInt .->. TyVar d) .->. TyVar c)           ==!
    tyAll d (tyInt .->. TyVar d) .->. tyAf
  , TyMu a (tyAll c (tyInt .-*. TyVar c) .->. TyVar a)          !/\
    TyMu b (tyAll d (tyInt .->. TyVar d) .->. TyVar c)
  , TyMu a (tyAll c (tyInt .-*. TyVar c) .->. TyVar a)           \/!
    TyMu b (tyAll d (tyInt .->. TyVar d) .->. TyVar b)           ==!
    TyMu b (tyAll c (tyInt .->. TyVar c) .->. TyVar b)
  , TyMu a (tyAll c (tyInt .-*. TyVar c) .->. TyVar a)           /\!
    TyMu b (tyAll d (tyInt .->. TyVar d) .->. TyVar b)           ==!
    TyMu b (tyAll c (tyInt .-*. TyVar c) .->. TyVar b)
  , TyMu a (tyAll c (TyVar a .-*. TyVar c) .->. TyVar a)         \/!
    TyMu b (tyAll d (TyVar b .->. TyVar d) .->. TyVar b)         ==!
    TyMu b (tyAll d (tyUn .->. TyVar d) .->. TyVar b)
  , TyMu a (tyAll c (TyVar a .-*. TyVar c) .->. TyVar a)         /\!
    TyMu b (tyAll d (TyVar b .->. TyVar d) .->. TyVar b)         ==!
    TyMu b (tyAll d tyAf .->. TyVar b)
  , tyAll a (TyVar a .*. tyInt) .->. TyVar a  \/!
    tyAll b (TyVar b .*. tyInt) .->. TyVar a  ==!
    tyAll b (TyVar b .*. tyInt) .->. TyVar a 
  , tyAll a (TyVar a .*. tyInt) .->. TyVar a  /\!
    tyAll b (TyVar b .*. tyInt) .->. TyVar a  ==!
    tyAll b (TyVar b .*. tyInt) .->. TyVar a 
  , tyAll a (TyVar a .*. tyInt) .->. TyVar a  \/!
    tyAll b (TyVar b .*. tyInt) .->. TyVar b  ==!
    tyAll b (TyVar b .*. tyInt) .->. tyUn
  , tyAll a (TyVar a .*. tyInt) .->. TyVar a !/\
    tyAll b (TyVar b .*. tyInt) .->. TyVar b 
  ]
  where
  t1 \/! t2 = Left (t1, t2)
  t1 /\! t2 = Right (t1, t2)
  Left  (t1, t2) ==! t =
    T.assertEqual (show t1 ++ " \\/ " ++ show t2 ++ " = " ++ show t)
                  (Just t) (t1 \/? t2)
  Right (t1, t2) ==! t =
    T.assertEqual (show t1 ++ " /\\ " ++ show t2 ++ " = " ++ show t)
                  (Just t) (t1 /\? t2)
  t1 !/\ t2 =
    T.assertEqual (show t1 ++ " /\\ " ++ show t2 ++ " DNE")
                  Nothing (t1 /\? t2)
  infix 2 ==!
  infix 4 \/!, /\!, !/\
  a = tvUn "a"; b = tvUn "b"; c = tvAf "c"; d = tvAf "d"

uvarsTests = T.test
  [ tyInt   !<:  tyUnit
  , tyInt    <:! tyInt   ==! (tyUn, tyUn, tyAf, tyAf)
  , TyVar a  <:! tyInt   ==! (tyInt, tyUn, tyAf, tyAf)
  , TyVar c  <:! tyInt   ==! (tyUn, tyUn, tyInt, tyAf)
  , tyInt   !<:  TyVar a
  , TyVar a .*. TyVar a   <:! tyInt .*. tyInt
      ==! (tyInt, tyUn, tyAf, tyAf)
  , TyVar a .*. TyVar a  !<:  tyInt .*. tyUnit
  , TyVar a .*. TyVar a   <:! (tyInt .->. tyInt) .*. (tyInt .-*. tyInt)
      ==! (tyInt .->. tyInt, tyUn, tyAf, tyAf)
  , TyVar a .*. TyVar a   <:! (tyUnit .->. tyInt) .*. (tyInt .-*. tyInt)
      ==! (tyUn .->. tyInt, tyUn, tyAf, tyAf)
  , TyVar a .->. tyInt    <:! tyInt .->. tyInt
      ==! (tyInt, tyUn, tyAf, tyAf)
  , TyVar a .->. TyVar a  <:! tyInt .->. tyInt
      ==! (tyInt, tyUn, tyAf, tyAf)
  , TyVar a .->. TyVar a !<:  tyFloat .->. tyInt
  , TyVar a .->. TyVar a !<:  (tyInt .->. tyInt) .-*. (tyInt .-*. tyInt)
  , TyVar c .->. TyVar c  <:! (tyInt .->. tyInt) .-*. (tyInt .-*. tyInt)
      ==! (tyUn, tyUn, tyInt .->. tyInt, tyAf)
  , TyVar c .->. TyVar c !<:  (tyInt .-*. tyInt) .-*. (tyInt .->. tyInt)
  , TyVar c .-*. TyVar c !<:  (tyInt .->. tyInt) .->. (tyInt .-*. tyInt)
  , TyVar a .*.  TyVar a  <:! tyDual (tyRecv tyInt .:. tyUnit) .*.
                                     (tySend tyInt .:. tyUnit)
      ==! (tySend tyInt .:. tyUnit, tyUn, tyAf, tyAf)
  , TyVar a .*.  TyVar a !<:  tyDual (tyRecv tyInt .:. tyUnit) .*.
                                     (tySend tyInt .:. tyInt)
  , TyVar a .*.  tyAll a (TyVar a .->. tyInt)  <:!
    tyInt   .*.  tyAll b (TyVar b .->. tyInt)
      ==!  (tyInt, tyUn, tyAf, tyAf)
  , TyVar a .*.  tyAll a (TyVar a .->. tyInt) !<:
    tyInt   .*.  tyAll b (tyInt   .->. tyInt)
  , tyAll a (TyVar a .->. tyInt) !<:
    tyAll a (tyInt   .->. tyInt)
  , TyVar a <:! tyInt .->. TyMu a (tyInt .->. TyVar a)
      ==!  (TyMu b (tyInt .->. TyVar b), tyUn, tyAf, tyAf)
  , TyVar a .->. TyVar b <:! tyInt .->. TyMu a (tyInt .->. TyVar a)
      ==!  (tyInt, TyMu b (tyInt .->. TyVar b), tyAf, tyAf)
  , TyVar a .->. TyVar b <:! TyMu a (tyInt .->. TyVar a)
      ==!  (tyInt, TyMu b (tyInt .->. TyVar b), tyAf, tyAf)
  , TyVar a >:! tyInt
      ==!  (tyInt, tyUn, tyAf, tyAf)
  , TyVar a .-*. TyVar a  >:! tyInt .->. tyInt
      ==!  (tyInt, tyUn, tyAf, tyAf)
  , TyVar a .->. TyVar a !>:  tyInt .-*. tyInt
  , TyVar a .-*. TyVar a  >:! tyUn  .->. tyInt
      ==!  (tyInt, tyUn, tyAf, tyAf)
  , TyFun (qInterpret (QeVar c)) tyInt tyInt <:! tyInt .-*. tyInt
      ==!  (tyUn, tyUn, tyAf, tyAf)
  , TyFun (qInterpret (QeVar c)) tyInt tyInt <:! tyInt .->. tyInt
      ==!  (tyUn, tyUn, tyUn, tyAf)
  ]
  where
  t1 <:! t2 = Left (t1, t2)
  t1 >:! t2 = Right (t1, t2)
  Left (t1, t2) ==! (ta, tb, tc, td) =
    T.assertEqual (show t1 ++ " `subtype` " ++ show t2)
      (Right (M.fromList [(a, ta), (b, tb), (c, tc), (d, td)], M.empty))
      (runEither Left Right $ subtype 100 set t1 S.empty t2)
  Right (t1, t2) ==! (ta, tb, tc, td) =
    T.assertEqual (show t1 ++ " `supertype` " ++ show t2)
      (Right (M.empty, M.fromList [(a, ta), (b, tb), (c, tc), (d, td)]))
      (runEither Left Right $ subtype 100 S.empty t2 set t1)
  t1 !<: t2 =
    T.assertEqual (show t1 ++ " `subtype` " ++ show t2 ++ " = ERROR")
                  Nothing (e2m (subtype 100 set t1 S.empty t2))
  t1 !>: t2 =
    T.assertEqual (show t1 ++ " `supertype` " ++ show t2 ++ " = ERROR")
                  Nothing (e2m (subtype 100 S.empty t2 set t1))
  e2m = runEither (const Nothing) Just
  infix 2 ==!
  infix 4 <:!, !<:, >:!, !>:
  set = S.fromList [a, b, c, d]
  a   = tvUn "a"; b = tvUn "b"; c = tvAf "c"; d = tvAf "d"

tests :: IO ()
tests = do
  T.runTestTT subtypeTests
  T.runTestTT joinTests
  T.runTestTT uvarsTests
  return ()
