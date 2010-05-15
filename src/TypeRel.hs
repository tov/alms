{-# LANGUAGE
      ParallelListComp,
      PatternGuards,
      RankNTypes #-}
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
import ErrorST
import Type
import Util
import Viewable

import qualified Control.Monad.Reader as CMR
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

type UT s t a = CMR.ReaderT (TCS s t) (ST t String) a

-- | An environment mapping mu-bound type variables to their
--   definition for unrolling ('Left') or forall-bound variables
--   to a pair of lower and upper bounds, for instantiation ('Right')
type UEnv t = M.Map TyVar (UVar t)
type UVar t = (Int, STRef t (Type, Type))

data TCS s t = TCS {
  -- | Pairs of types previously seen, and thus considered related
  --   if seen again.
  tcsSeen    :: STRef t (M.Map (AType, AType) s),
  -- | Should key pairs for 'tcsSeen' be flipped?
  tcsFlip    :: Bool,
  -- | A supply of fresh type variables
  tcsSupply  :: STRef t [QLit -> TyVar],
  -- | The number of instantiated foralls we are currently under
  tcsLevel   :: Int,
  -- | The environment for the left side of the relation
  tcsEnv1    :: UEnv t,
  -- | The environment for the right side of the relation
  tcsEnv2    :: UEnv t
}

data Field s t = Field {
  get    :: TCS s t -> UEnv t,
  update :: TCS s t -> UEnv t -> TCS s t
}

env1, env2 :: Field s t
env1 = Field tcsEnv1 (\tcs e -> tcs { tcsEnv1 = e })
env2 = Field tcsEnv2 (\tcs e -> tcs { tcsEnv2 = e })

lift :: (CMR.MonadTrans t, Monad m) => m a -> t m a
lift  = CMR.lift

runUT  :: forall s a m. Monad m =>
          (forall t. UT s t a) -> S.Set TyVar -> m a
runUT m set =
  either fail return $
    runST $ do
      seen   <- newTransSTRef M.empty
      supply <- newSTRef [ f | f <- tvalphabet
                         , f Qu `S.notMember` set
                         , f Qa `S.notMember` set ]
      CMR.runReaderT m TCS {
        tcsSeen   = seen,
        tcsFlip   = False,
        tcsSupply = supply,
        tcsLevel  = 1,
        tcsEnv1   = M.empty,
        tcsEnv2   = M.empty
      }

getVar :: TyVar -> Field s t -> UT s t (Maybe (UVar t))
getVar tv field = CMR.asks (M.lookup tv . get field)

-- | To add some unification variables to the scope, run the body,
--   and return a map containing their lower and upper bounds.
--   Unification variables are assumed to be fresh with respect to
--   existing variables.  In particular, the initial set of unification
--   variables precedes any other bindings, and all subsequent foralls
--   are renamed using fresh type variables.
withUVars :: [TyVar] -> Field s t -> UT s t a -> UT s t (a, [Type])
withUVars tvs field body = do
  level <- CMR.asks tcsLevel
  refs  <- lift $ sequence
    [ do ref <- newTransSTRef (tyBot, tyTop (tvqual tv))
         return (tv, (level, ref))
    | tv <- tvs ]
  res   <- CMR.local
    (\st -> update field st (M.fromList refs `M.union` get field st))
    body
  typs  <- sequence
    [ do
        (lower, upper) <- lift $ readSTRef ref
        if lower <: upper
          then return $
            -- This is a heuristic -- we prefer to return something
            -- with information, meaning not top or bottom, but if
            -- the choice is between top and bottom, we go with bottom
            if isBotType lower
              then if upper == tyUn || upper == tyAf then lower else upper
              else lower
          else fail $
            "Unification cannot solve:\n" ++
            dumpType lower ++ " <: " ++ dumpType upper
    | (_, (_, ref)) <- refs ]
  return (res, typs)

-- | Bump up the quantification nesting level
incU :: UT s t a -> UT s t a
incU  = CMR.local (\st -> st { tcsLevel = tcsLevel st + 1 })

-- | Try to assert an upper bound on a unification variable.
upperBoundUVar :: STRef t (Type, Type) -> Type -> UT s t ()
upperBoundUVar ref t = do
  (lower, upper) <- lift $ readSTRef ref
  unless (upper <: t) $ do
    upper' <- t /\? upper
    lift $ writeSTRef ref (lower, upper')


-- | Try to assert a lower bound on a unification variable.
lowerBoundUVar :: STRef t (Type, Type) -> Type -> UT s t ()
lowerBoundUVar ref t = do
  (lower, upper) <- lift $ readSTRef ref
  unless (t <: lower) $ do
    lower' <- t \/? lower
    lift $ writeSTRef ref (lower', upper)

-- | Get maps of the left and right uvars
getUVars :: UT s t (TyVar -> Maybe (Int, STRef t (Type, Type)),
                    TyVar -> Maybe (Int, STRef t (Type, Type)))
getUVars = do
  st <- CMR.ask
  return (flip M.lookup (tcsEnv1 st), flip M.lookup (tcsEnv2 st))

-- | Check if two types have been seen before.  If so, return the
--   previously stored answer.  If not, temporarily store the given
--   answer, then run a block, and finally replace the stored answer
--   with the result of the block.
chkU :: Type -> Type -> s -> UT s t s -> UT s t s
chkU t1 t2 s body = do
  st   <- CMR.ask
  let key = if tcsFlip st
              then (AType t2, AType t1)
              else (AType t1, AType t2)
      ref = tcsSeen st
  seen <- lift $ readSTRef ref
  case M.lookup key seen of
    Just s' -> return s'
    Nothing -> do
      lift $ modifySTRef ref (M.insert key s)
      res <- body
      lift $ modifySTRef ref (M.insert key res)
      return res

-- | Flip the left and right sides of the relation in the given block.
flipU :: UT s t a -> UT s t a
flipU body = CMR.local flipSt body where
  flipSt (TCS seen flipFlag level supply e1 e2) =
    TCS seen (not flipFlag) level supply e2 e1

-- | Get a fresh type variable from the supply.
freshU :: QLit -> UT s t TyVar
freshU qlit = do
  ref <- CMR.ask >>! tcsSupply
  f:supply <- lift $ readSTRef ref
  lift $ writeSTRef ref supply
  return (f qlit)

-- | Print a debug message
-- debug :: Show b => b -> UT s t ()
-- debug = lift . ST.unsafeIOToST . print
-- deubg = const $ return ()

subtype :: Monad m =>
           Int -> [TyVar] -> Type -> [TyVar] -> Type ->
           m ([Type], [Type])
subtype limit uvars1 t1i uvars2 t2i =
  runUT start (S.fromList uvars1 `S.union`
               S.fromList uvars2 `S.union`
               alltv (t1i, t2i))
  where
    start :: UT () t ([Type], [Type])
    start = liftM (first snd) $
              withUVars uvars2 env2 $
                withUVars uvars1 env1 $
                  cmp t1i t2i
    --
    cmp :: Type -> Type -> UT () t ()
    cmp t u = chkU t u () $ case (t, u) of
      -- Handle top
      (_ , TyApp tcu _ _)
        | tcu == tcUn && qualConst t <: Qu
        -> return ()
      (_ , TyApp tcu _ _)
        | tcu == tcAf
        -> return ()
      -- Handle bottom
      (TyApp tct _ _, _)
        | tct == tcBot
        -> return ()
      -- Variables
      (TyVar vt, TyVar vu) -> do
        mt' <- getVar vt env1
        mu' <- getVar vu env2
        case (mt', mu') of
          (Just (_, t'), Nothing) -> upperBoundUVar t' u
          (Nothing, Just (_, u')) -> lowerBoundUVar u' t
          (Just (lt, t'), Just (lu, u'))
            | lt > lu             -> upperBoundUVar t' u
            | lt < lu             -> lowerBoundUVar u' t
          _                       -> unless (vt == vu) $ giveUp t u
      (TyVar vt, _) -> do
        mt' <- getVar vt env1
        case mt' of
          Just (_, t') -> upperBoundUVar t' u
          Nothing      -> giveUp t u
      (_, TyVar vu) -> do
        mu' <- getVar vu env2
        case mu' of
          Just (_, u') -> lowerBoundUVar u' t
          Nothing      -> giveUp t u
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
        cmp (tysubst tvt (TyVar tv') t1)
            (tysubst tvu (TyVar tv') u1)
      (TyQu Forall tvt t1, _) -> do
        tv' <- freshU (tvqual tvt)
        incU $
          withUVars [tv'] env1 $
            cmp (tysubst tvt (TyVar tv') t1) u
        return ()
      -- Recursion
      (TyMu tvt t1, _) -> cmp (tysubst tvt t t1) u
      (_, TyMu tvu u1) -> cmp t (tysubst tvu u u1)
      -- Failure
      _ -> giveUp t u
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
        case (view $ qRepresent qd1, view $ qRepresent qd2) of
          (QeVar tv1, QeVar tv2)
            | Just (_, ref) <- m1 tv1, Nothing <- m2 tv2
            -> upperBoundUVar ref (TyVar tv2)
            | Nothing <- m1 tv1, Just (_, ref) <- m2 tv2
            -> lowerBoundUVar ref (TyVar tv1)
          (QeVar tv1, QeLit qlit)
            | Just (_, ref) <- m1 tv1
            -> upperBoundUVar ref (tyTop qlit)
          (QeLit qlit, QeVar tv2)
            | Just (_, ref) <- m2 tv2
            -> lowerBoundUVar ref (tyTop qlit)
          _ -> orElse

jointype :: Monad m => Int -> Bool -> Type -> Type -> m Type
jointype limit b t1i t2i =
  liftM clean $ runUT (cmp (b, True) t1i t2i) (alltv (t1i, t2i))
  where
  cmp, revCmp :: (Bool, Bool) -> Type -> Type -> UT Type t Type
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
      -- Variables
      (TyVar vt, TyVar ut)
        | vt == ut ->
        return t
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
          cmp m (tysubst tvt (TyVar tv') t1)
                (tysubst tvu (TyVar tv') u1)
      -- Recursion
      (TyMu tvt t1, _) ->
        cmp m (tysubst tvt t t1) u
      (_, TyMu tvu u1) ->
        cmp m t (tysubst tvu u u1)
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
    | tc == tcBot                   = Just t
  points False t u@(TyApp tc _ _)
    | tc == tcAf                    = Just t
    | tc == tcUn, qualConst t <: Qu = Just t
    | tc == tcBot                   = Just u
  points _     _   _                = Nothing
  --
  revCmp (direction, lossy) t u = cmp (not direction, lossy) t u
  --
  catchTop (True, True)  t u body = body
    `catchError` \_ -> return (tyTop (qualConst t \/ qualConst u))
  {-
  catchTop (False, True) _ _ body = body
    `catchError` \_ -> return tyBot
  -}
  catchTop _             _ _ body = body
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
instance Eq Type where
  t1 == t2 = t1 <: t2 && t2 <: t1

instance PO Type where
  t1 <: t2     = runEither (const False) (const True)
                           (subtype 100 [] t1 [] t2)
  ifMJ b t1 t2 = jointype 100 b t1 t2

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
  , tyBot  <:! tyInt .->. tyInt
  , tyInt .->. tyInt !<:  tyBot
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
  , TyMu a (tyAll c (TyVar a .-*. TyVar c) .->. TyVar a) <:!
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
  , TyMu a (tyAll b (TyVar b .->. TyVar a))  <:!
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
  , TyMu a (tyAll c (tyInt .->. tyAll d (TyVar c .->. TyVar a))) !<:
    tyAll c (tyInt .->.
             TyMu a (tyAll d (TyVar c .->.
                              tyAll c (tyInt .->. TyVar a))))
  , tyAll c (tyInt .->.
             TyMu a (tyAll d (TyVar c .->.
                              tyAll c (tyInt .->. TyVar a)))) !<:
    TyMu a (tyAll c (tyInt .->. tyAll d (TyVar c .->. TyVar a)))
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
  , tyBot  \/! tyInt .->. tyInt ==! tyInt .->. tyInt
  , tyInt .->. tyInt  /\! tyBot ==! tyAll b (TyVar b)
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
    TyMu b (tyAll d (TyVar b .->. TyVar d) .->. TyVar b)
  , TyMu a (tyAll c (TyVar a .-*. TyVar c) .->. TyVar a)         /\!
    TyMu b (tyAll d (TyVar b .->. TyVar d) .->. TyVar b)         ==!
    TyMu b (tyAll d (TyVar b .-*. TyVar d) .->. TyVar b)
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
  , tyBot  \/! TyVar b ==! TyVar b
  , tyIdent tyBot \/! TyVar b ==! TyVar b
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
  , tyInt    <:! tyInt   ==! (noU, noU, noA, noA)
  , TyVar a  <:! tyInt   ==! (tyInt, noU, noA, noA)
  , TyVar c  <:! tyInt   ==! (noU, noU, tyInt, noA)
  , tyInt   !<:  TyVar a
  , TyVar a .*. TyVar a   <:! tyInt .*. tyInt
      ==! (tyInt, noU, noA, noA)
  , TyVar a .*. TyVar a  !<:  tyInt .*. tyUnit
  , TyVar a .*. TyVar a   <:! (tyInt .->. tyInt) .*. (tyInt .-*. tyInt)
      ==! (tyInt .->. tyInt, noU, noA, noA)
  , TyVar a .*. TyVar a   <:! (tyUnit .->. tyInt) .*. (tyInt .-*. tyInt)
      ==! (tyUn .->. tyInt, noU, noA, noA)
  , TyVar a .->. tyInt    <:! tyInt .->. tyInt
      ==! (tyInt, noU, noA, noA)
  , TyVar a .->. TyVar a  <:! tyInt .->. tyInt
      ==! (tyInt, noU, noA, noA)
  , TyVar a .->. TyVar a !<:  tyFloat .->. tyInt
  , TyVar a .->. TyVar a !<:  (tyInt .->. tyInt) .-*. (tyInt .-*. tyInt)
  , TyVar c .->. TyVar c  <:! (tyInt .->. tyInt) .-*. (tyInt .-*. tyInt)
      ==! (noU, noU, tyInt .->. tyInt, noA)
  , TyVar c .->. TyVar c !<:  (tyInt .-*. tyInt) .-*. (tyInt .->. tyInt)
  , TyVar c .-*. TyVar c !<:  (tyInt .->. tyInt) .->. (tyInt .-*. tyInt)
  , TyVar a .*.  TyVar a  <:! tyDual (tyRecv tyInt .:. tyUnit) .*.
                                     (tySend tyInt .:. tyUnit)
      ==! (tySend tyInt .:. tyUnit, noU, noA, noA)
  , TyVar a .*.  TyVar a !<:  tyDual (tyRecv tyInt .:. tyUnit) .*.
                                     (tySend tyInt .:. tyInt)
  , TyVar a .*.  tyAll a (TyVar a .->. tyInt)  <:!
    tyInt   .*.  tyAll b (TyVar b .->. tyInt)
      ==!  (tyInt, noU, noA, noA)
  , TyVar a .*.  tyAll a (TyVar a .->. tyInt) !<:
    tyInt   .*.  tyAll b (tyInt   .->. tyInt)
  , tyAll a (TyVar a .->. tyInt) !<:
    tyAll a (tyInt   .->. tyInt)
  , TyVar a <:! tyInt .->. TyMu a (tyInt .->. TyVar a)
      ==!  (TyMu b (tyInt .->. TyVar b), noU, noA, noA)
  , TyVar a .->. TyVar b <:! tyInt .->. TyMu a (tyInt .->. TyVar a)
      ==!  (tyInt, TyMu b (tyInt .->. TyVar b), noA, noA)
  , TyVar a .->. TyVar b <:! TyMu a (tyInt .->. TyVar a)
      ==!  (tyInt, TyMu b (tyInt .->. TyVar b), noA, noA)
  , TyVar a >:! tyInt
      ==!  (tyInt, noU, noA, noA)
  , TyVar a .-*. TyVar a  >:! tyInt .->. tyInt
      ==!  (tyInt, noU, noA, noA)
  , TyVar a .->. TyVar a !>:  tyInt .-*. tyInt
  , TyVar a .-*. TyVar a  >:! tyUn  .->. tyInt
      ==!  (tyInt, noU, noA, noA)
  , TyFun (qInterpret (qeVar c)) tyInt tyInt <:! tyInt .-*. tyInt
      ==!  (noU, noU, noA, noA)
  , TyFun (qInterpret (qeVar c)) tyInt tyInt <:! tyInt .->. tyInt
      ==!  (noU, noU, noA, noA)
  , (TyVar c .->. TyVar d .-*. TyVar d) .*. TyVar d .*. tyRecv (TyVar c)
    <:!
    (TyVar e .->. TyVar f .-*. TyVar f) .*. TyVar f .*. tyRecv (TyVar e)
      ==! (noU, noU, TyVar e, TyVar f)
  , tyConst (TyVar a) <:! tyConst (tyInt)
      ==! (tyInt, noU, noA, noA) -- suboptimal
  , tyConst (TyVar a .*. tyUnit) <:! tyConst (tyInt .*. tyInt)
      ==! (noU, noU, noA, noA)
  , tyRecv (TyVar c) .*. tyRecv (TyVar c)  >:!
    tyRecv (TyVar e) .*. tyAll f (tyRecv (TyVar f))
      ==! (noU, noU, TyVar e, noA)
  , tyRecv (TyVar c) .*. tyRecv (TyVar c)  >:!
    tyRecv (TyVar e) .*. tyRecv (TyVar e)
      ==! (noU, noU, TyVar e, noA)
  , tyRecv (TyVar c) .*. tyRecv (TyVar c) !>:
    tyRecv (TyVar e) .*. tyRecv (TyVar f)
  , T.assertEqual "'<c `supertype` '<d = ERROR"
      Nothing (subtype 100 [c] (TyVar c) [d] (TyVar d))
  , tyFollow (TyVar a) (TyVar b) >:!
    tyFollow tyUnit (tyRecv tyInt .:.
                     TyMu e (tyFollow tyUnit (tyRecv tyInt .:.
                                              TyVar e)))
      ==! (tyUnit, (tyRecv tyInt .:.
                     TyMu e (tyFollow tyUnit (tyRecv tyInt .:.
                                              TyVar e))), noA, noA)
  , tyFollow (TyVar a) (TyVar b) >:!
    TyMu e (tyFollow tyUnit (tyRecv tyInt .:. TyVar e))
      ==! (tyUnit, (tyRecv tyInt .:.
                     TyMu e (tyFollow tyUnit (tyRecv tyInt .:.
                                              TyVar e))), noA, noA)
  ]
  where
  t1 <:! t2 = Left (t1, t2)
  t1 >:! t2 = Right (t1, t2)
  Left (t1, t2) ==! (ta, tb, tc, td) =
    T.assertEqual (show t1 ++ " `subtype` " ++ show t2)
      (Right ([ta, tb, tc, td], []))
      (runEither Left Right $ subtype 100 set t1 [] t2)
  Right (t1, t2) ==! (ta, tb, tc, td) =
    T.assertEqual (show t1 ++ " `supertype` " ++ show t2)
      (Right ([], [ta, tb, tc, td]))
      (runEither Left Right $ subtype 100 [] t2 set t1)
  t1 !<: t2 =
    T.assertEqual (show t1 ++ " `subtype` " ++ show t2 ++ " = ERROR")
                  Nothing (subtype 100 set t1 [] t2)
  t1 !>: t2 =
    T.assertEqual (show t1 ++ " `supertype` " ++ show t2 ++ " = ERROR")
                  Nothing (subtype 100 [] t2 set t1)
  infix 2 ==!
  infix 4 <:!, !<:, >:!, !>:
  noU = tyBot; noA = tyBot
  set = [a, b, c, d]
  a   = tvUn "a"; b = tvUn "b"; c = tvAf "c"; d = tvAf "d"
  e   = tvAf "e"; f = tvAf "f"

tests :: IO ()
tests = do
  T.runTestTT subtypeTests
  T.runTestTT joinTests
  T.runTestTT uvarsTests
  return ()
