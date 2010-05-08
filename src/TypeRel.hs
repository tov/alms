{-# LANGUAGE
      FlexibleInstances,
      QuasiQuotes,
      ParallelListComp,
      PatternGuards,
      ScopedTypeVariables,
      TemplateHaskell #-}
module TypeRel (
  -- * Type operations
  -- ** Equality and subtyping
  AType(..), subtype, jointype,
  -- ** Queries and conversions
  qualifier, qualConst, abstractTyCon, replaceTyCon,
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
abstractTyCon tc = tc { tcCons = empty, tcNext = Nothing }

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

-- | Find the qualifier of a type (which must be decorated with
--   tycon info)
qualifier     :: Type -> QDen TyVar
qualifier (TyApp tc ts _) = denumberQDen (map qualifier ts) (tcQual tc)
qualifier (TyArr q _ _)   = q
qualifier (TyVar tv)
  | tvqual tv <: Qu       = minBound
  | otherwise             = qInterpret (QeVar tv)
qualifier (TyQu _ _ t)    = qualifier t
qualifier (TyMu _ t)      = qualifier t

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
      TyArr q t1 t2 =?= TyArr q' t1' t2'
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
      TyArr _ _ _   =?= _           = LT
      _             =?= TyArr _ _ _ = GT
      TyQu _ _ _    =?= _           = LT
      _             =?= TyQu _ _ _  = GT

instance Eq Type where
  t1 == t2 = t1 <: t2 && t2 <: t1

type UT s m a = CMS.StateT (TCS s) m a

data TCS s = TCS {
  tcsSeen    :: M.Map (AType, AType) s,
  tcsSubst1  :: M.Map TyVar Type,
  tcsSubst2  :: M.Map TyVar Type,
  tcsSupply  :: [QLit -> TyVar]
}

runUT  :: Monad m => UT s m a -> S.Set TyVar -> m a
runUT m set = CMS.evalStateT m TCS {
  tcsSeen   = M.empty,
  tcsSubst1 = M.empty,
  tcsSubst2 = M.empty,
  tcsSupply = [ f | f <- tvalphabet
                  , f Qu `S.notMember` set
                  , f Qa `S.notMember` set ]
}

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

get1U :: Monad m => TyVar -> UT s m Type
get1U tv = do
  st <- CMS.get
  maybe (fail $ "unbound type variable: " ++ show tv) return $
    M.lookup tv (tcsSubst1 st)

get2U :: Monad m => TyVar -> UT s m Type
get2U tv = do
  st <- CMS.get
  maybe (fail $ "unbound type variable: " ++ show tv) return $
    M.lookup tv (tcsSubst2 st)

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
      flipSt (TCS seen s1 s2 supply) =
        TCS (M.mapKeys (\(x,y) -> (y,x)) seen) s2 s1 supply

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

  -- CMS.put st { tcsSeen = tcsSeen

subtype :: MonadError e m => Int -> Type -> Type -> m ()
subtype limit t1i t2i = runUT (cmp t1i t2i) (ftv (t1i, t2i))
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
      -- Handle bottom
      (TyQu Forall tvt (TyVar tvt'), _)
        | tvt == tvt'
        -> return ()
      -- Variables
      (TyVar vt, TyVar ut)
        | vt == ut ->
        return ()
      (TyVar vt, _) -> do
        t' <- get1U vt
        cmp t' u
      (_, TyVar ut) -> do
        u' <- get2U ut
        cmp t u'
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
      (TyArr qt t1 t2, TyArr qu u1 u2)
        | qt <: qu -> do
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
      -- Recursion
      (TyMu tvt t1, _) ->
        add1U tvt t $ cmp t1 u
      (_, TyMu tvu u1) ->
        add2U tvu u $ cmp t u1
      -- Failure
      (_, _) -> do
        fail $
          "Got type `" ++ show t ++ "' where type `" ++
          show u ++ "' expected"
    --
    revCmp u t = flipU (cmp t u)
    --
    hn t = case headNormalizeTypeK limit t of
      (Next (), t') -> fail $
        "Gave up reducing type `" ++ show t' ++
        "' after " ++ show limit ++ " steps"
      (_, t') -> return t'
    --
    cmpList arity ts us =
      sequence_
        [ case var of
            1  -> cmp tj uj
            -1 -> revCmp tj uj
            _  -> do cmp tj uj; revCmp tj uj
        | (_, var) <- arity
        | tj       <- ts
        | uj       <- us ]

jointype :: MonadError e m => Int -> Bool -> Type -> Type -> m Type
jointype limit b t1i t2i =
  liftM clean $ runUT (cmp (b, True) t1i t2i) (ftv (t1i, t2i))
  where
  cmp, revCmp :: MonadError e m =>
                 (Bool, Bool) -> Type -> Type -> UT Type m Type
  cmp m t u = do
    let (direction, _) = m
    tv   <- freshU (qualConst t \/ qualConst u)
    catch m t u $
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
        t' <- get1U vt
        cmp m t' u
      (_, TyVar ut) -> do
        u' <- get2U ut
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
      (TyArr qt t1 t2, TyArr qu u1 u2) -> do
        q'  <- ifMJ direction qt qu
        t1' <- revCmp m t1 u1
        t2' <- cmp m t2 u2
        return (TyArr q' t1' t2')
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
          "Could not unify types `" ++ show t ++
          "' and `" ++ show u ++ "'"
  --
  hn t = case headNormalizeTypeK limit t of
    (Next (), t') -> fail $
      "Gave up reducing type `" ++ show t' ++
      "' after " ++ show limit ++ " steps"
    (_, t') -> return t'
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
      | (_, var) <- arity
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
  catch (True, True) t u body = body
    `catchError` \_ -> return $
      case (qualConst t \/ qualConst u) of
        Qu -> tyNulOp tcUn
        Qa -> tyNulOp tcAf
  catch _            _ _ body = body
  --
  clean :: Type -> Type
  clean (TyApp tc ts _)  = tyApp tc (map clean ts)
  clean (TyVar a)        = TyVar a
  clean (TyArr q t1 t2)  = TyArr q (clean t1) (clean t2)
  clean (TyQu u a t)     = TyQu u a (clean t)
  clean (TyMu a t)
    | a `S.member` ftv t = TyMu a (clean t)
    | otherwise          = clean t

-- | The Type partial order
instance PO Type where
  t1 <: t2     = either (const False) (const True)
                        (subtype 100 t1 t2 :: Either String ())
  ifMJ b t1 t2 = either fail return (jointype 100 b t1 t2)

subtypeTests, joinTests :: T.Test

subtypeTests = T.test
  [ tyUnit  <:! tyUnit
  , tyUnit !<:  tyInt
  , tyInt   <:! tyInt
  , tyArr tyInt tyInt   <:! tyArr tyInt tyInt
  , tyArr tyInt tyInt   <:! tyLol tyInt tyInt
  , tyLol tyInt tyInt   <:! tyLol tyInt tyInt
  , tyLol tyInt tyInt  !<:  tyArr tyInt tyInt
  , tyArr tyUnit tyInt !<:  tyArr tyInt tyInt
  , tyArr (tyLol tyInt tyInt) (tyArr tyInt tyInt) <:!
      tyArr (tyArr tyInt tyInt) (tyLol tyInt tyInt)
  , tyArr tyInt tyInt  <:! tyNulOp tcUn
  , tyArr tyInt tyInt  <:! tyNulOp tcAf
  , tyLol tyInt tyInt !<:  tyNulOp tcUn
  , tyLol tyInt tyInt  <:! tyNulOp tcAf
  , tyNulOp tcUn  <:! tyNulOp tcAf
  , tyNulOp tcAf !<:  tyNulOp tcUn
  , tyRecv tyInt  <:! tyRecv tyInt
  , tyRecv tyInt !<:  tyRecv tyUnit
  , tyRecv tyInt !<:  tySend tyInt
  , tyRecv (tyLol tyInt tyInt)  <:! tyRecv (tyArr tyInt tyInt)
  , tyRecv (tyArr tyInt tyInt) !<:  tyRecv (tyLol tyInt tyInt)
  , tySend (tyLol tyInt tyInt) !<:  tySend (tyArr tyInt tyInt)
  , tySend (tyArr tyInt tyInt)  <:! tySend (tyLol tyInt tyInt)
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
  , tyArr tyUnit tyInt <:! tyIdent (tyLol (tyConst (tySend tyInt)) tyInt)
  , tyArr tyInt tyInt !<:  tyIdent (tyLol (tyConst (tySend tyInt)) tyInt)
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) <:!
      tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit))
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) <:!
      tySemi (tySend tyInt) (tyDual (tySemi (tySend tyUnit) tyUnit))
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) <:!
      tySemi (tySend tyInt) (tySemi (tyRecv tyUnit) tyUnit)
  , tyAll a (TyVar a)  <:! tyArr tyInt tyInt
  , tyArr tyInt tyInt !<:  tyAll a (TyVar a)
  , TyVar a  <:! TyVar a
  , TyVar a !<:  TyVar b
  , tyAll a (tyArr tyInt (TyVar a))  <:!  tyAll b (tyArr tyInt (TyVar b))
  , tyAll a (tyArr tyInt (TyVar a)) !<:  tyAll b (tyArr tyInt (TyVar a))
  , tyAll c (tyArr (TyVar c) tyInt)  <:! tyAll a (tyLol (TyVar a) tyInt)
  , tyAll a (tyArr (TyVar a) tyInt) !<:  tyAll c (tyLol (TyVar c) tyInt)
  , tyAll a (tyAll b (tyTuple (TyVar a) (TyVar b)))  <:!
      tyAll b (tyAll a (tyTuple (TyVar b) (TyVar a)))
  , tyAll a (tyAll b (tyTuple (TyVar a) (TyVar b))) !<:
      tyAll b (tyAll a (tyTuple (TyVar a) (TyVar b)))
  , tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b))) !<:
      tyAll b (tyAll a (tyTuple (TyVar a) (TyVar b)))
  , tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b)))  <:!
      tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b)))
  , TyMu a (tyArr tyInt (TyVar a))  <:! TyMu b (tyArr tyInt (TyVar b))
  , TyMu a (tyArr tyInt (TyVar a))  <:!
      TyMu b (tyArr tyInt (tyArr tyInt (TyVar b)))
  , TyMu a (tyArr tyInt (TyVar a))  <:!
      TyMu b (tyArr tyInt (tyLol tyInt (TyVar b)))
  , TyMu a (tyArr tyInt (TyVar a)) !<:
      TyMu b (tyArr tyInt (tyLol tyUnit (TyVar b)))
  , TyMu a (tyTuple tyInt (tyTuple tyInt (TyVar a))) <:!
      tyTuple tyInt (TyMu a (tyTuple tyInt (tyTuple tyInt (TyVar a))))
  , TyMu a (tyTuple tyUnit (tyTuple tyInt (TyVar a))) <:!
      tyTuple tyUnit (TyMu a (tyTuple tyInt (tyTuple tyUnit (TyVar a))))
  , tyAll c (TyMu a (tyTuple (TyVar c) (tyTuple tyInt (TyVar a))))  <:!
      tyAll d (tyTuple
                 (TyVar d)
                 (TyMu a (tyTuple tyInt (tyTuple (TyVar d) (TyVar a)))))
  , tyAll c (TyMu a (tyTuple (TyVar c) (tyTuple tyInt (TyVar a)))) !<:
      tyAll d (tyTuple
                 (TyVar d)
                 (TyMu a (tyTuple tyInt (tyTuple (TyVar a) (TyVar d)))))
  , TyMu a (tyArr (tyAll c (tyLol tyInt (TyVar c))) (TyVar a)) !<:
      TyMu b (tyArr (tyAll d (tyArr tyInt (TyVar d))) (TyVar c))
  , TyMu a (tyArr (tyAll c (tyLol tyInt (TyVar c))) (TyVar a))  <:!
      TyMu b (tyArr (tyAll d (tyArr tyInt (TyVar d))) (TyVar b))
  , TyMu a (tyArr (tyAll c (tyLol (TyVar a) (TyVar c))) (TyVar a)) !<:
      TyMu b (tyArr (tyAll d (tyArr (TyVar b) (TyVar d))) (TyVar b))
  , tyArr (tyAll a (tyTuple (TyVar a) tyInt)) (TyVar a)  <:!
      tyArr (tyAll b (tyTuple (TyVar b) tyInt)) (TyVar a)
  , tyArr (tyAll a (tyTuple (TyVar a) tyInt)) (TyVar a) !<:
      tyArr (tyAll b (tyTuple (TyVar b) tyInt)) (TyVar b)
  ]
  where
  tyInt   = tyNulOp tcInt
  tySend  = tyUnOp tcSend
  tyRecv  = tyUnOp tcRecv
  tyDual  = tyUnOp tcDual
  tySemi  = tyBinOp tcSemi
  tyIdent = tyUnOp $ mkTC 10 "id"  (0 :: QDen Int) [(Qa, 1)]
    [([TpVar a], TyVar a)]
  tyConst = tyUnOp $ mkTC 11 "const"  (0 :: QDen Int) [(Qa, 1)]
    [([TpVar a], tyUnit)]
  tyAll   = TyQu Forall
  t1  <:! t2 = T.assertBool (show t1 ++ " <: " ++ show t2) (t1 <: t2)
  t1 !<:  t2 = T.assertBool (show t1 ++ " /<: " ++ show t2) (t1 /<: t2)
  a      = TV (Lid "a") Qu
  b      = TV (Lid "b") Qu
  c      = TV (Lid "c") Qa
  d      = TV (Lid "d") Qa

joinTests = T.test
  [ tyUnit  \/! tyUnit ==! tyUnit
  , tyUnit  /\! tyUnit ==! tyUnit
  , tyInt   /\! tyInt  ==! tyInt
  , tyUnit  \/! tyInt  ==! tyUn
  , tyUnit !/\  tyInt
  , tyArr tyInt tyInt  \/! tyArr tyInt tyInt  ==! tyArr tyInt tyInt
  , tyArr tyInt tyInt  \/! tyLol tyInt tyInt  ==! tyLol tyInt tyInt
  , tyLol tyInt tyInt  \/! tyLol tyInt tyInt  ==! tyLol tyInt tyInt
  , tyLol tyInt tyInt  \/! tyArr tyInt tyInt  ==! tyLol tyInt tyInt
  , tyArr tyInt tyInt  /\! tyArr tyInt tyInt  ==! tyArr tyInt tyInt
  , tyArr tyInt tyInt  /\! tyLol tyInt tyInt  ==! tyArr tyInt tyInt
  , tyLol tyInt tyInt  /\! tyLol tyInt tyInt  ==! tyLol tyInt tyInt
  , tyLol tyInt tyInt  /\! tyArr tyInt tyInt  ==! tyArr tyInt tyInt
  , tyArr tyInt tyInt  \/! tyArr tyInt tyUnit ==! tyArr tyInt tyUn
  , tyArr tyInt tyInt  \/! tyArr tyUnit tyInt ==! tyUn
  , tyLol tyInt tyInt  \/! tyArr tyUnit tyInt ==! tyAf
  , tyArr tyInt tyInt !/\  tyArr tyInt tyUnit
  , tyArr tyInt tyInt  /\! tyArr tyUnit tyInt ==! tyArr tyUn tyInt
  , tyLol tyInt tyInt  /\! tyArr tyUnit tyInt ==! tyArr tyUn tyInt
  , tyLol (tyLol tyInt tyInt) tyInt /\! tyArr tyUnit tyInt
      ==! tyArr tyAf tyInt
  , tyArr tyInt tyInt  \/! tyUn ==! tyUn
  , tyArr tyInt tyInt  \/! tyAf ==! tyAf
  , tyLol tyInt tyInt  \/! tyUn ==! tyAf
  , tyLol tyInt tyInt  \/! tyAf ==! tyAf
  , tyArr tyInt tyInt  /\! tyUn ==! tyArr tyInt tyInt
  , tyArr tyInt tyInt  /\! tyAf ==! tyArr tyInt tyInt
  , tyLol tyInt tyInt !/\  tyUn -- could do better
  , tyLol tyInt tyInt  /\! tyAf ==! tyLol tyInt tyInt
  , tyRecv tyInt \/! tyRecv tyInt  ==! tyRecv tyInt
  , tySend tyInt \/! tySend tyUnit ==! tySend tyUn
  , tyRecv tyInt \/! tySend tyInt  ==! tyUn
  , tyRecv (tyLol tyInt tyInt) \/! tyRecv (tyArr tyInt tyInt)
      ==! tyRecv (tyArr tyInt tyInt)
  , tyRecv (tyArr tyInt tyInt) \/! tyRecv (tyLol tyInt tyInt)
      ==! tyRecv (tyArr tyInt tyInt)
  , tySend (tyLol tyInt tyInt) \/! tySend (tyArr tyInt tyInt)
      ==! tySend (tyLol tyInt tyInt)
  , tySend (tyArr tyInt tyInt) \/! tySend (tyLol tyInt tyInt)
      ==! tySend (tyLol tyInt tyInt)
  , tyRecv (tyLol tyInt tyInt) /\! tyRecv (tyArr tyInt tyInt)
      ==! tyRecv (tyLol tyInt tyInt)
  , tyRecv (tyArr tyInt tyInt) /\! tyRecv (tyLol tyInt tyInt)
      ==! tyRecv (tyLol tyInt tyInt)
  , tySend (tyLol tyInt tyInt) /\! tySend (tyArr tyInt tyInt)
      ==! tySend (tyArr tyInt tyInt)
  , tySend (tyArr tyInt tyInt) /\! tySend (tyLol tyInt tyInt)
      ==! tySend (tyArr tyInt tyInt)
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
  , tyArr tyUnit tyInt  \/! tyIdent (tyLol (tyConst (tySend tyInt)) tyInt)
      ==! tyLol tyUnit tyInt
  , tyArr tyInt tyInt   \/! tyIdent (tyLol (tyConst (tySend tyInt)) tyInt)
      ==! tyAf
  , tyArr tyUnit tyInt  /\! tyIdent (tyLol (tyConst (tySend tyInt)) tyInt)
      ==! tyArr tyUnit tyInt
  , tyArr tyInt tyInt   /\! tyIdent (tyLol (tyConst (tySend tyInt)) tyInt)
      ==! tyArr tyUn tyInt
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) \/!
      tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit))
      ==! tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit))
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) \/!
      tySemi (tySend tyInt) (tyDual (tySemi (tySend tyUnit) tyUnit))
      ==! tySemi (tySend tyInt) (tyDual (tySemi (tySend tyUnit) tyUnit))
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) \/!
      tySemi (tySend tyInt) (tySemi (tyRecv tyUnit) tyUnit)
      ==! tySemi (tySend tyInt) (tySemi (tyRecv tyUnit) tyUnit)
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) /\!
      tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit))
      ==! tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit))
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) /\!
      tySemi (tySend tyInt) (tyDual (tySemi (tySend tyUnit) tyUnit))
      ==! tySemi (tySend tyInt) (tyDual (tySemi (tySend tyUnit) tyUnit))
  , tyDual (tySemi (tyRecv tyInt) (tySemi (tySend tyUnit) tyUnit)) /\!
      tySemi (tySend tyInt) (tySemi (tyRecv tyUnit) tyUnit)
      ==! tySemi (tySend tyInt) (tySemi (tyRecv tyUnit) tyUnit)
  , tyAll a (TyVar a)  \/! tyArr tyInt tyInt ==! tyArr tyInt tyInt
  , tyArr tyInt tyInt  /\! tyAll a (TyVar a) ==! tyAll b (TyVar b)
  , TyVar a  \/! TyVar a ==! TyVar a
  , TyVar a  \/! TyVar b ==! tyUn
  , TyVar a  \/! TyVar c ==! tyAf
  , TyVar a  /\! TyVar a ==! TyVar a
  , TyVar a !/\  TyVar b
  , TyVar a !/\  TyVar c
  , tyAll a (tyArr tyInt (TyVar a))  \/!  tyAll b (tyArr tyInt (TyVar b))
      ==! tyAll a (tyArr tyInt (TyVar a))
  , tyAll a (tyArr tyInt (TyVar a))  \/!  tyAll b (tyArr tyInt (TyVar a))
      ==! tyAll a (tyArr tyInt tyUn)
  , tyAll c (tyArr (TyVar c) tyInt)  \/! tyAll a (tyLol (TyVar a) tyInt)
      ==! tyAll d (tyLol (TyVar d) tyInt)
  , tyAll a (tyArr tyInt (TyVar a))  /\!  tyAll b (tyArr tyInt (TyVar b))
      ==! tyAll a (tyArr tyInt (TyVar a))
  , tyAll a (tyArr tyInt (TyVar a)) !/\   tyAll b (tyArr tyInt (TyVar a))
  , tyAll c (tyArr (TyVar c) tyInt)  /\! tyAll a (tyLol (TyVar a) tyInt)
      ==! tyAll b (tyArr (TyVar b) tyInt)
  , tyAll a (tyAll b (tyTuple (TyVar a) (TyVar b)))  \/!
      tyAll b (tyAll a (tyTuple (TyVar b) (TyVar a)))
      ==! tyAll b (tyAll a (tyTuple (TyVar b) (TyVar a)))
  , tyAll a (tyAll b (tyTuple (TyVar a) (TyVar b)))  \/!
      tyAll b (tyAll a (tyTuple (TyVar a) (TyVar b)))
      ==! tyAll b (tyAll a (tyTuple tyUn tyUn))
  , tyAll c (tyAll c (tyTuple (TyVar c) (TyVar d)))  \/!
      tyAll d (tyAll c (tyTuple (TyVar c) (TyVar d)))
      ==! tyAll d (tyAll d (tyTuple (TyVar d) tyAf))
  , tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b)))  \/!
      tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b)))
      ==! tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b)))
  , tyAll a (tyAll b (tyTuple (TyVar a) (TyVar b)))  /\!
      tyAll b (tyAll a (tyTuple (TyVar b) (TyVar a)))
      ==! tyAll b (tyAll a (tyTuple (TyVar b) (TyVar a)))
  , tyAll a (tyAll b (tyTuple (TyVar a) (TyVar b))) !/\
      tyAll b (tyAll a (tyTuple (TyVar a) (TyVar b)))
  , tyAll c (tyAll c (tyTuple (TyVar c) (TyVar d))) !/\
      tyAll d (tyAll c (tyTuple (TyVar c) (TyVar d)))
  , tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b)))  /\!
      tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b)))
      ==! tyAll a (tyAll a (tyTuple (TyVar a) (TyVar b)))
  , TyMu a (tyArr tyInt (TyVar a))  \/! TyMu b (tyArr tyInt (TyVar b))
      ==! TyMu b (tyArr tyInt (TyVar b))
  , TyMu a (tyArr tyInt (TyVar a))  /\! TyMu b (tyArr tyInt (TyVar b))
      ==! TyMu b (tyArr tyInt (TyVar b))
  , TyMu a (tyArr tyInt (TyVar a))  \/!
      TyMu b (tyArr tyInt (tyArr tyInt (TyVar b)))
      ==! TyMu a (tyArr tyInt (TyVar a))
  , TyMu a (tyArr tyInt (TyVar a))  /\!
      TyMu b (tyArr tyInt (tyArr tyInt (TyVar b)))
      ==! TyMu a (tyArr tyInt (TyVar a))
  , TyMu a (tyArr tyInt (TyVar a))  \/!
      TyMu b (tyArr tyInt (tyLol tyInt (TyVar b)))
      ==! TyMu b (tyArr tyInt (tyLol tyInt (TyVar b)))
  , TyMu a (tyArr tyInt (TyVar a))  /\!
      TyMu b (tyArr tyInt (tyLol tyInt (TyVar b)))
      ==! TyMu b (tyArr tyInt (TyVar b))
  , TyMu a (tyArr tyInt (TyVar a))  \/!
      TyMu b (tyArr tyInt (tyLol tyUnit (TyVar b)))
      ==! tyArr tyInt tyAf
  , TyMu a (tyArr tyInt (TyVar a))  /\!
      TyMu b (tyArr tyInt (tyLol tyUnit (TyVar b)))
      ==! TyMu a (tyArr tyInt (tyArr tyUn (TyVar a)))
  , TyMu a (tyTuple tyInt (tyTuple tyInt (TyVar a))) \/!
      tyTuple tyInt (TyMu a (tyTuple tyInt (tyTuple tyInt (TyVar a))))
      ==! TyMu a (tyTuple tyInt (TyVar a))
  , TyMu a (tyTuple tyInt (tyTuple tyInt (TyVar a))) /\!
      tyTuple tyInt (TyMu a (tyTuple tyInt (tyTuple tyInt (TyVar a))))
      ==! TyMu a (tyTuple tyInt (TyVar a))
  , TyMu a (tyTuple tyUnit (tyTuple tyInt (TyVar a))) \/!
      tyTuple tyUnit (TyMu a (tyTuple tyInt (tyTuple tyUnit (TyVar a))))
      ==! TyMu b (tyTuple tyUnit (tyTuple tyInt (TyVar b)))
  , TyMu a (tyTuple tyUnit (tyTuple tyInt (TyVar a))) /\!
      tyTuple tyUnit (TyMu a (tyTuple tyInt (tyTuple tyUnit (TyVar a))))
      ==! TyMu b (tyTuple tyUnit (tyTuple tyInt (TyVar b)))
  , tyAll c (TyMu a (tyTuple (TyVar c) (tyTuple tyInt (TyVar a))))  \/!
      tyAll d (tyTuple
                 (TyVar d)
                 (TyMu a (tyTuple tyInt (tyTuple (TyVar d) (TyVar a)))))
      ==! tyAll c (TyMu b (tyTuple (TyVar c) (tyTuple tyInt (TyVar b))))
  , tyAll c (TyMu a (tyTuple (TyVar c) (tyTuple tyInt (TyVar a))))  /\!
      tyAll d (tyTuple
                 (TyVar d)
                 (TyMu a (tyTuple tyInt (tyTuple (TyVar d) (TyVar a)))))
      ==! tyAll c (TyMu b (tyTuple (TyVar c) (tyTuple tyInt (TyVar b))))
  , tyAll c (TyMu a (tyTuple (TyVar c) (tyTuple tyInt (TyVar a))))  \/!
      tyAll d (tyTuple
                 (TyVar d)
                 (TyMu a (tyTuple tyInt (tyTuple (TyVar a) (TyVar d)))))
      ==! tyAll c (tyTuple (TyVar c) (tyTuple tyInt (tyTuple tyAf tyAf)))
  , tyAll c (TyMu a (tyTuple (TyVar c) (tyTuple tyInt (TyVar a)))) !/\
      tyAll d (tyTuple
                 (TyVar d)
                 (TyMu a (tyTuple tyInt (tyTuple (TyVar a) (TyVar d)))))
  , TyMu a (tyArr (tyAll c (tyLol tyInt (TyVar c))) (TyVar a))  \/!
      TyMu b (tyArr (tyAll d (tyArr tyInt (TyVar d))) (TyVar c))
      ==! tyArr (tyAll d (tyArr tyInt (TyVar d))) tyAf
  , TyMu a (tyArr (tyAll c (tyLol tyInt (TyVar c))) (TyVar a)) !/\
      TyMu b (tyArr (tyAll d (tyArr tyInt (TyVar d))) (TyVar c))
  , TyMu a (tyArr (tyAll c (tyLol tyInt (TyVar c))) (TyVar a))  \/!
      TyMu b (tyArr (tyAll d (tyArr tyInt (TyVar d))) (TyVar b))
      ==! TyMu b (tyArr (tyAll c (tyArr tyInt (TyVar c))) (TyVar b))
  , TyMu a (tyArr (tyAll c (tyLol tyInt (TyVar c))) (TyVar a))  /\!
      TyMu b (tyArr (tyAll d (tyArr tyInt (TyVar d))) (TyVar b))
      ==! TyMu b (tyArr (tyAll c (tyLol tyInt (TyVar c))) (TyVar b))
  , TyMu a (tyArr (tyAll c (tyLol (TyVar a) (TyVar c))) (TyVar a)) \/!
      TyMu b (tyArr (tyAll d (tyArr (TyVar b) (TyVar d))) (TyVar b))
      ==! TyMu b (tyArr (tyAll d (tyArr tyUn (TyVar d))) (TyVar b))
  , TyMu a (tyArr (tyAll c (tyLol (TyVar a) (TyVar c))) (TyVar a)) /\!
      TyMu b (tyArr (tyAll d (tyArr (TyVar b) (TyVar d))) (TyVar b))
      ==! TyMu b (tyArr (tyAll d tyAf) (TyVar b))
  , tyArr (tyAll a (tyTuple (TyVar a) tyInt)) (TyVar a)  \/!
      tyArr (tyAll b (tyTuple (TyVar b) tyInt)) (TyVar a)
      ==! tyArr (tyAll b (tyTuple (TyVar b) tyInt)) (TyVar a)
  , tyArr (tyAll a (tyTuple (TyVar a) tyInt)) (TyVar a)  /\!
      tyArr (tyAll b (tyTuple (TyVar b) tyInt)) (TyVar a)
      ==! tyArr (tyAll b (tyTuple (TyVar b) tyInt)) (TyVar a)
  , tyArr (tyAll a (tyTuple (TyVar a) tyInt)) (TyVar a)  \/!
      tyArr (tyAll b (tyTuple (TyVar b) tyInt)) (TyVar b)
      ==! tyArr (tyAll b (tyTuple (TyVar b) tyInt)) tyUn
  , tyArr (tyAll a (tyTuple (TyVar a) tyInt)) (TyVar a) !/\
      tyArr (tyAll b (tyTuple (TyVar b) tyInt)) (TyVar b)
  ]
  where
  tyUn    = tyNulOp tcUn
  tyAf    = tyNulOp tcAf
  tyInt   = tyNulOp tcInt
  tySend  = tyUnOp tcSend
  tyRecv  = tyUnOp tcRecv
  tyDual  = tyUnOp tcDual
  tySemi  = tyBinOp tcSemi
  tyIdent = tyUnOp $ mkTC 10 "id"  (0 :: QDen Int) [(Qa, 1)]
    [([TpVar a], TyVar a)]
  tyConst = tyUnOp $ mkTC 11 "const"  (0 :: QDen Int) [(Qa, 1)]
    [([TpVar a], tyUnit)]
  tyAll   = TyQu Forall
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
  a      = TV (Lid "a") Qu
  b      = TV (Lid "b") Qu
  c      = TV (Lid "c") Qa
  d      = TV (Lid "d") Qa

tests :: IO ()
tests = do
  T.runTestTT subtypeTests
  T.runTestTT joinTests
  return ()
