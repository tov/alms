module Statics (
  S, env0,
  tcProg, tcDecls,
  addVal, addTyTag
) where

import System.IO.Unsafe

import Util
import Syntax
import Env as Env
import Ppr ()

import Data.List (elemIndex)
import qualified Data.Map as M
import qualified Data.Set as S

import qualified Control.Monad.Reader as M.R
import qualified Control.Monad.State  as M.S

-- Get the usage (sharing) of a variable in an expression:
usage :: Lid -> Expr i A -> Q
usage x e = case M.lookup x (fv e) of
  Just u | u > 1 -> Qu
  _              -> Qa

-- Type constructors are bound to either "type info" or a synonym
data TyInfo w = TiAbs TyTag
              | TiSyn [TyVar] (TypeT w)
              | TiDat TyTag (M.Map Uid (Maybe (TypeT w)))

-- Type environments
type D   = S.Set TyVar         -- tyvars in scope
type G w = Env Ident (TypeT w) -- types of variables in scope
type I w = Env Lid (TyInfo w)  -- type constructors in scope

data S   = S {
             cVars   :: G C,
             aVars   :: G A,
             cTypes  :: I C,
             aTypes  :: I A,
             currIx  :: Integer
           }

-- The type checking monad
newtype TC w m a =
  TC { unTC :: M.R.ReaderT (TCEnv w) (M.S.StateT Integer m) a }
data TCEnv w = TCEnv (G w, G (OtherLang w)) (I w, I (OtherLang w)) (D, D)

instance Monad m => Monad (TC w m) where
  m >>= k = TC (unTC m >>= unTC . k)
  return  = TC . return
  fail    = TC . fail . ("Type error: "++)

asksM :: M.R.MonadReader r m => (r -> m a) -> m a
asksM  = (M.R.ask >>=)

saveTC :: (Language w, Monad m) => TC w m S
saveTC  = intoC . TC $ do
  TCEnv (g, g') (i, i') _ <- M.R.ask
  index                   <- M.S.get
  return S {
    cVars  = g,
    aVars  = g',
    cTypes = i,
    aTypes = i',
    currIx = index
  }

newtype WrapTC a m w = WrapTC { unWrapTC :: TC w m a }

runTC :: (Language w, Monad m) => S -> TC w m a -> m a
runTC gg0 m0 = langCase (WrapTC m0)
                 (runTCw (cVars, aVars) (cTypes, aTypes) gg0 . unWrapTC)
                 (runTCw (aVars, cVars) (aTypes, cTypes) gg0 . unWrapTC)
  where
    runTCw :: (Language w, Monad m) =>
              (S -> G w, S -> G (OtherLang w)) ->
              (S -> I w, S -> I (OtherLang w)) ->
              S -> TC w m a -> m a
    runTCw (getVars, getVars') (getTypes, getTypes') gg (TC m) = do
      let r0 = TCEnv (getVars gg, getVars' gg)
                     (getTypes gg, getTypes' gg)
                     (S.empty, S.empty)
          s0 = currIx gg
      M.S.evalStateT (M.R.runReaderT m r0) s0

data WrapGI w = WrapGI (G w) (I w)

intoC :: Language w => TC C m a -> TC w m a
intoC  = TC . M.R.withReaderT sw . unTC where
  sw (TCEnv (g, g') (i, i') (d, d')) =
    langCase (WrapGI g i)
      (\(WrapGI gC iC) -> TCEnv (gC, g') (iC, i') (d, d'))
      (\(WrapGI gA iA) -> TCEnv (g', gA) (i', iA) (d', d))

intoA :: Language w => TC A m a -> TC w m a
intoA  = TC . M.R.withReaderT sw . unTC where
  sw (TCEnv (g, g') (i, i') (d, d')) =
    langCase (WrapGI g i)
      (\(WrapGI gC iC)  -> langCase (WrapGI g' i')
          (\_           -> error "impossible! (Statics.intoA)")
          (\(WrapGI g'A i'A) -> TCEnv (g'A, gC) (i'A, iC) (d', d)))
      (\(WrapGI gA iA) -> TCEnv (gA, g') (iA, i') (d, d'))

outofC :: Language w => TC w m a -> TC C m a
outofC m = langCase (WrapTC m) unWrapTC (intoA . unWrapTC)

outofA :: Language w => TC w m a -> TC A m a
outofA m = langCase (WrapTC m) (intoC . unWrapTC) unWrapTC

newIndex :: Monad m => TC w m Integer
newIndex  = TC $ do
  M.S.modify (+ 1)
  M.S.get

withTVs :: Monad m => [TyVar] -> TC w m a -> TC w m a
withTVs tvs = TC . M.R.local add . unTC where
  add (TCEnv g ii (d, dw)) = TCEnv g ii (foldr S.insert d tvs, dw)

withVars :: Monad m => G w -> TC w m a -> TC w m a
withVars g' = TC . M.R.local add . unTC where
  add (TCEnv (g, gw) ii dd) = TCEnv (g =+= g', gw) ii dd

withTypes :: Monad m => I w -> TC w m a -> TC w m a
withTypes i' = TC . M.R.local add . unTC where
  add (TCEnv g (i, iw) dd) = TCEnv g (i =+= i', iw) dd

checkTV :: Monad m => TyVar -> TC w m ()
checkTV tv = TC $ asksM check where
  check (TCEnv _ _ (d, _)) = tassert (S.member tv d) $
                               "Free type variable: " ++ show tv

getVar :: Monad m => Ident -> TC w m (TypeT w)
getVar x = TC $ asksM get where
  get (TCEnv (g, _) _ _) = g =.= x
    |! "Unbound variable: " ++ show x

tryGetVar :: Monad m => Ident -> TC w m (Maybe (TypeT w))
tryGetVar x = TC $ asksM get where
  get (TCEnv (g, _) _ _) = return (g =.= x)

getType :: Monad m => Lid -> TC w m (TyInfo w)
getType n = TC $ asksM get where
  get (TCEnv _ (i, _) _) = i =.= n
    |! "Unbound type constructor: " ++ show n

-- A type checking "assertion" raises a type error if the
-- asserted condition is false.
tassert :: Monad m => Bool -> String -> m ()
tassert True  _ = return ()
tassert False s = fail s

-- A common form of type error
tgot :: Monad m => String -> Type i w -> String -> m a
tgot who got expected = fail $ who ++ " got " ++ show got ++
                               " where " ++ expected ++ " expected"

-- Run a partial computation, and if it fails, substitute
-- the given failure message.
(|!) :: Monad m => Maybe a -> String -> m a
m |! s = case m of
  Just r  -> return r
  _       -> fail s
infix 1 |!

-- Check type for closed-ness and and defined-ness, and add info
tcType :: (Language w, Monad m) => Type i w -> TC w m (TypeT w)
tcType = tc where
  tc :: (Language w, Monad m) => Type i w -> TC w m (TypeT w)
  tc (TyVar tv)   = do
    checkTV tv
    return (TyVar tv)
  tc (TyCon n ts _) = do
    ts'  <- mapM tc ts
    tcon <- getType n
    case tcon of
      TiAbs td -> do
        checkLength (length (tdArity td))
        return (TyCon n ts' td)
      TiSyn ps t -> do
        checkLength (length ps)
        let avoid   = M.unions (map ftv ts')
            ps'     = freshTyVars ps avoid
            substs :: Language w =>
                      [TyVar] -> [TypeT w] -> TypeT w -> TypeT w
            substs tvs ts0 t0 = foldr2 tysubst t0 tvs ts0
        return .
          substs ps' ts' .
            substs ps (map TyVar ps') $ t
      TiDat td _ -> do
        checkLength (length (tdArity td))
        return (TyCon n ts' td)
    where
      checkLength len =
        tassert (length ts == len) $
          "Type constructor " ++ unLid n ++ " applied to " ++
          show (length ts) ++ " arguments where " ++
          show len ++ " expected"
  tc (TyAll tv t) = TyAll tv `liftM` withTVs [tv] (tc t)
  tc (TyMu  tv t) = TyMu tv  `liftM` withTVs [tv] (tc t)
  tc (TyC t)      = TyC      `liftM` intoC (tc t)
  tc (TyA t)      = TyA      `liftM` intoA (tc t)

-- Type check an expression
tcExprC :: Monad m => Expr i C -> TC C m (TypeT C, ExprT C)
tcExprC = tc where
  tc :: Monad m => Expr i C -> TC C m (TypeT C, ExprT C)
  tc e0 = case expr' e0 of
    -- XXX -- ExId (Con (Uid "()"))  -> return (tyUnitT, exCon (Uid "()"))
    -- ExId (Con (Uid s))
      -- | s `elem` constants -> fail $ "Constant must be applied: " ++ s
      -- | otherwise          -> fail $ "Unrecognized constant: " ++ s
    ExId x -> do
      tx <- getVar x
      return (tx, exId x)
    ExStr s       -> return (TyCon (Lid "string") [] tdString, exStr s)
    ExInt z       -> return (TyCon (Lid "int") [] tdInt, exInt z)
    ExIf e1 e2 e3 -> do
      (t1, e1') <- tc e1
      tassert (tyinfo t1 == tdBool) $
        "If condition was " ++ show t1 ++ " where bool expected"
      (t2, e2') <- tc e2
      (t3, e3') <- tc e3
      tassert (t2 == t3) $
        "Mismatch in if: " ++ show t2 ++ " /= " ++ show t3
      return (t2, exIf e1' e2' e3')
    ExCase e1 (xl, el) (xr, er) -> do
      (t1, e1') <- tc e1
      case t1 of
        TyCon (Lid "either") [txl, txr] td | td == tdEither -> do
          (tl, el') <- withVars (Var xl =:= txl) $ tc el
          (tr, er') <- withVars (Var xr =:= txr) $ tc er
          tassert (tl == tr) $
            "Mismatch in match: " ++ show tl ++ " /= " ++ show tr
          return (tl, exCase e1' (xl, el') (xr, er'))
        _ -> tgot "match" t1 "('a, 'b) either"
    ExLet x e1 e2 -> do
      (t1, e1') <- tc e1
      (t2, e2') <- withVars (Var x =:= t1) $ tc e2
      return (t2, exLet x e1' e2')
    ExLetRec bs e2 -> do
      tfs <- mapM (tcType . bntype) bs
      let makeG seen (b:bs') (t:ts') = do
            tassert (bnvar b `notElem` seen) $
              "Duplicate binding in let rec: " ++ show (bnvar b)
            tassert (syntacticValue (bnexpr b)) $
              "Not a syntactic value in let rec: " ++ show (bnexpr b)
            g' <- makeG (bnvar b : seen) bs' ts'
            return (g' =+= Var (bnvar b) =:= t)
          makeG _    _       _       = return empty
      g'  <- makeG [] bs tfs
      (tas, e's) <- unzip `liftM` mapM (withVars g' . tc . bnexpr) bs
      zipWithM_ (\tf ta -> do
                   tassert (tf == ta) $
                      "Actual type " ++ show ta ++
                      " does not agree with declared type " ++
                      show tf ++ " in let rec")
                tfs tas
      (t2, e2') <- withVars g' (tc e2)
      let b's = zipWith3 (\b tf e' -> b { bntype = tf, bnexpr = e' })
                         bs tfs e's
      return (t2, exLetRec b's e2')
    ExPair e1 e2  -> do
      (t1, e1') <- tc e1
      (t2, e2') <- tc e2
      return (TyCon (Lid "*") [t1, t2] tdTuple, exPair e1' e2')
    ExLetPair (x, y) e1 e2 -> do
      tassert (x /= y) $ "Repeated variable in let pair: " ++ show x
      (t1, e1') <- tc e1
      case t1 of
        TyCon (Lid "*") [tx, ty] td | td == tdTuple
          -> do
               (t2, e2') <- withVars (Var x =:= tx =+= Var y =:= ty) $ tc e2
               return (t2, exLetPair (x, y) e1' e2')
        _ -> tgot "let" t1 "pair type"
    ExAbs x t e     -> do
      t' <- tcType t
      (te, e') <- withVars (Var x =:= t') $ tc e
      return (tyArrT t' te, exAbs x t' e')
    ExApp e1 e2   -> case expr' e1 of
      -- XXX -- ExId (Con u)  -> do
        -- (t2, e2') <- tc e2
        -- t         <- tcCon u t2
        -- return (t, exApp (exCon u) e2')
      _             -> do
        (t1, e1') <- tc e1
        (t2, e2') <- tc e2
        let (tvs, body) = unfoldTyAll t1
        case body of
          TyCon (Lid "->") [ta, tr] td | td == tdArr -> do
            subst <- tryUnify tvs ta t2
            let ta' = subst ta
                tr' = subst tr
            tassert (ta' == t2) $
              "Mismatch in application: got " ++
              show t2 ++ " where " ++ show ta' ++ " expected"
            return (tr', exApp e1' e2')
          _ -> fail $ "Mismatch in application: got " ++
                       show t1 ++ " where function type expected"
    ExTAbs tv e   -> do
      (t, e') <- withTVs [tv] $ tc e
      return (TyAll tv t, exTAbs tv e')
    ExTApp e1 t2  -> do
      (t1, e1') <- tc e1
      t2'       <- tcType t2
      case t1 of
        TyAll tv t1' -> return (tysubst tv t2' t1', exTApp e1' t2')
        _            -> tgot "type application" t1 "(for)all type"
    ExSeq e1 e2   -> do
      (_,  e1') <- tc e1
      (t2, e2') <- tc e2
      return (t2, exSeq e1' e2')
    ExCast e1 t ta -> do
      t'  <- tcType t
      ta' <- intoA $ tcType ta
      case t' of
        TyCon _ [_, _] td | td `elem` funtypes -> return ()
        _ -> tgot "cast (:>)" t' "function type"
      (t1, e1') <- tc e1
      tassert (t1 == t') $
        "Mismatch in cast: declared type " ++ show t' ++
        " doesn't match actual type " ++ show t1
      tassert (t1 == atype2ctype ta') $
        "Mismatch in cast: C type " ++ show t1 ++
        " is incompatible with A contract " ++ show t'
      return (t', exCast e1' t' ta')

tcExprA :: Monad m => Expr i A -> TC A m (TypeT A, ExprT A)
tcExprA = tc where
  tc :: Monad m => Expr i A -> TC A m (TypeT A, ExprT A)
  tc e0 = case expr' e0 of
    -- XXX -- ExId (Con (Uid "()"))  -> return (tyUnitT, exCon (Uid "()"))
    -- ExId (Con (Uid s))
      -- | s `elem` constants -> fail $ "Constant must be applied: " ++ s
      -- | otherwise          -> fail $ "Unrecognized constant: " ++ s
    ExId x -> do
      tx <- getVar x
      return (tx, exId x)
    ExStr s       -> return (TyCon (Lid "string") [] tdString, exStr s)
    ExInt z       -> return (TyCon (Lid "int") [] tdInt, exInt z)
    ExIf e1 e2 e3 -> do
      (t1, e1') <- tc e1
      tassert (tyinfo t1 == tdBool) $
        "If condition was " ++ show t1 ++ " where bool expected"
      (t2, e2') <- tc e2
      (t3, e3') <- tc e3
      t <- t2 \/? t3
        |! "Mismatch in if: " ++ show t2 ++ " and " ++ show t3
      return (t, exIf e1' e2' e3')
    ExCase e1 (xl, el) (xr, er) -> do
      (t1, e1') <- tc e1
      case t1 of
        TyCon (Lid "either") [txl, txr] td | td == tdEither -> do
          tassert (qualifier txl <: usage xl el) $
            "Affine variable " ++ show xl ++ " : " ++
            show txl ++ " duplicated in match body"
          tassert (qualifier txr <: usage xr er) $
            "Affine variable " ++ show xr ++ " : " ++
            show txr ++ " duplicated in match body"
          (tl, el') <- withVars (Var xl =:= txl) $ tc el
          (tr, er') <- withVars (Var xr =:= txr) $ tc er
          t <- tl \/? tr
            |! "Mismatch in match: " ++ show tl ++ " and " ++ show tr
          return (t, exCase e1' (xl, el') (xr, er'))
        _ -> tgot "match" t1 "('a, 'b) either"
    ExLet x e1 e2 -> do
      (t1, e1') <- tc e1
      tassert (qualifier t1 <: usage x e2) $
        "Affine variable " ++ show x ++ " : " ++
        show t1 ++ " duplicated in let body"
      (t2, e2') <- withVars (Var x =:= t1) $ tc e2
      return (t2, exLet x e1' e2')
    ExLetRec bs e2 -> do
      tfs <- mapM (tcType . bntype) bs
      let makeG seen (b:bs') (t:ts') = do
            tassert (bnvar b `notElem` seen) $
              "Duplicate binding in let rec: " ++ show (bnvar b)
            tassert (syntacticValue (bnexpr b)) $
              "Not a syntactic value in let rec: " ++ show (bnexpr b)
            tassert (qualifier t <: Qu) $
              "Affine type in let rec binding: " ++ show t
            g' <- makeG (bnvar b : seen) bs' ts'
            return (g' =+= Var (bnvar b) =:= t)
          makeG _    _       _       = return empty
      g'  <- makeG [] bs tfs
      (tas, e's) <- unzip `liftM` mapM (withVars g' . tc . bnexpr) bs
      zipWithM_ (\tf ta ->
                   tassert (ta <: tf) $
                      "Actual type " ++ show ta ++
                      " does not agree with declared type " ++
                      show tf ++ " in let rec")
                tfs tas
      (t2, e2') <- withVars g' $ tc e2
      let b's = zipWith3 (\b tf e' -> b { bntype = tf, bnexpr = e' })
                         bs tfs e's
      return (t2, exLetRec b's e2')
    ExPair e1 e2  -> do
      (t1, e1') <- tc e1
      (t2, e2') <- tc e2
      return (TyCon (Lid "*") [t1, t2] tdTuple, exPair e1' e2')
    ExLetPair (x, y) e1 e2 -> do
      tassert (x /= y) $
        "Repeated variable in let pair: " ++ show x
      (t1, e1') <- tc e1
      case t1 of
        TyCon (Lid "*") [tx, ty] td | td == tdTuple -> do
          tassert (qualifier tx <: usage x e2) $
            "Affine variable " ++ show x ++ " : " ++
            show tx ++ " duplicated in let body"
          tassert (qualifier ty <: usage y e2) $
            "Affine variable " ++ show y ++ " : " ++
            show ty ++ " duplicated in let body"
          (t2, e2') <- withVars (Var x =:= tx =+= Var y =:= ty) $ tc e2
          return (t2, exLetPair (x, y) e1' e2')
        _ -> fail $ "Let pair got non-pair type: " ++ show t1
    ExAbs x t e     -> do
      t' <- tcType t
      tassert (qualifier t' <: usage x e) $
        "Affine variable " ++ show x ++ " : " ++
        show t' ++ " duplicated in lambda body"
      (te, e') <- withVars (Var x =:= t') $ tc e
      unworthy <- isUnworthy e0
      if unworthy
        then return (tyLolT t' te, exAbs x t' e')
        else return (tyArrT t' te, exAbs x t' e')
    ExApp e1 e2   -> case expr' e1 of
      -- XXX -- ExId (Con u)  -> do
        -- (t2, e2') <- tc e2
        -- t         <- tcCon u t2
        -- return (t, exApp (exCon u) e2')
      _             -> do
        (t1, e1') <- tc e1
        (t2, e2') <- tc e2
        let (tvs, body) = unfoldTyAll t1
        case body of
          TyCon _ [ta, tr] td
              | td `elem` funtypes -> do
            subst <- tryUnify tvs ta t2
            let ta' = subst ta
                tr' = subst tr
            tassert (t2 <: ta') $
              "Mismatch in application: got " ++
              show t2 ++ " where " ++ show ta' ++ " expected"
            return (tr', exApp e1' e2')
          _ -> fail $ "Mismatch in application: got " ++
                       show t1 ++ " where function type expected"
    ExTAbs tv e   -> do
      (t, e') <- withTVs [tv] $ tc e
      return (TyAll tv t, exTAbs tv e')
    ExTApp e1 t2  -> do
      t2'       <- tcType t2
      (t1, e1') <- tc e1
      case t1 of
        TyAll tv t1' -> do
          tassert (qualifier t2' <: tvqual tv) $
            "Mismatch in type application: got " ++
            show (qualifier t2') ++
            " type for type variable " ++ show tv
          return (tysubst tv t2' t1', exTApp e1' t2')
        _            -> tgot "type application" t1 "(for)all type"
    ExSeq e1 e2   -> do
      (_,  e1') <- tc e1
      (t2, e2') <- tc e2
      return (t2, exSeq e1' e2')
    ExCast e1 t ta -> do
      t'  <- tcType t
      ta' <- tcType ta
      case t' of
        TyCon _ [_, _] td | td `elem` funtypes -> return ()
        _ -> fail $ "Cast requires a function type, but got" ++ show t'
      (t1, e1') <- tc e1
      tassert (t1 <: t') $
        "Mismatch in cast: got " ++ show t1 ++
        " where " ++ show t' ++ " expected"
      t1 \/? ta' |!
        "Mismatch in cast: types " ++ show t1 ++
        " and " ++ show t' ++ " are incompatible"
      return (ta', exCast e1' t' ta')

  isUnworthy e =
    anyM (\x -> do
           mtx <- tryGetVar (Var x)
           return $ case mtx of
             Just tx -> qualifier tx == Qa
             Nothing -> False)
         (M.keys (fv e))

{- XXX
tcCon         :: (Monad m, Language w) =>
                 Uid -> TypeT w -> TC w m (TypeT w)
tcCon (Uid "unroll") t0 = do
  case tc t0 of
    Nothing -> fail $ "Nothing to unroll in: " ++ show t0
    Just tf -> return tf
  where
    tc (TyCon n ts0 td) =
      let ts0' = map tc ts0
          each t Nothing   (ts, Nothing)  = (t:ts, Nothing)
          each t Nothing   (ts, Just ts') = (t:ts, Just (t:ts'))
          each t (Just t') (ts, _)        = (t:ts, Just (t':ts))
       in do
         ts0'' <- snd (foldr2 each ([], Nothing) ts0 ts0')
         return (TyCon n ts0'' td)
    tc (TyAll tv t)  = TyAll tv `fmap` tc t
    tc (TyMu tv t)   = Just (tysubst tv (TyMu tv t) t)
    tc _             = Nothing
tcCon (Uid "()") _ = fail $ "Applied 0 arity constant: ()"
tcCon (Uid s)    _ = fail $ "Unrecognized constant: " ++ s
-}

-- Given a list of type variables tvs, an type t in which tvs
-- may be free, and a type t', tries to substitute for tvs in t
-- to produce a type that *might* unify with t'
tryUnify :: (Monad m, Language w) =>
             [TyVar] -> TypeT w -> TypeT w -> TC w m (TypeT w -> TypeT w)
tryUnify [] _ _        = return id
tryUnify (tv:tvs) t t' =
  case findSubst tv t t' of
    tguess:_ -> do
                  let subst' = tysubst tv tguess
                  subst <- tryUnify tvs (subst' t) t'
                  return (subst . subst')
    _        -> fail $
                  "Cannot guess type application to unify " ++
                  show t ++ " and " ++ show t'

-- Given a type variable tv, type t in which tv may be free,
-- and a second type t', finds a plausible candidate to substitute
-- for tv to make t and t' unify.  (The answer it finds doesn't
-- have to be correct.
findSubst :: Language w => TyVar -> TypeT w -> TypeT w -> [TypeT w]
findSubst tv = fs where
  fs :: Language w => TypeT w -> TypeT w -> [TypeT w]
  fs (TyCon _ [t] td) t' | td == tdDual = fs (dualSessionType t) t'
  fs t' (TyCon _ [t] td) | td == tdDual = fs t' (dualSessionType t)
  fs (TyVar tv') t' | tv == tv'
    = [t']
  fs (TyCon _ ts _) (TyCon _ ts' _)
    = concat (zipWith fs ts ts')
  fs (TyAll tv0 t) (TyAll tv0' t') | tv /= tv0
    = [ tr | tr <- fs t t', tr /= TyVar tv0' ]
  fs (TyC t) (TyC t')
    = concat (zipWith fs (cgetas t) (cgetas t'))
  fs (TyA t) (TyA t')
    = concat (zipWith fs (agetcs t) (agetcs t'))
  fs _ _
    = []

withTyDec :: (Language w, Monad m) =>
           TyDec i -> (TyDecT -> TC w m a) -> TC w m a
withTyDec (TdAbsA name params variances quals) k = intoA $ do
  index <- newIndex
  let each (Left tv) = case tv `elemIndex` params of
        Nothing -> fail $ "unbound tyvar " ++ show tv ++
                          " in qualifier list for type " ++ unLid name
        Just n  -> return (Left n)
      each (Right q) = return (Right q)
  quals' <- mapM each quals
  withTypes (name =:= TiAbs TyTag {
               tdId    = index,
               tdArity = variances,
               tdQual  = quals',
               tdTrans = False
             })
    (outofA . k $ TdAbsA name params variances quals)
withTyDec (TdAbsC name params) k = intoC $ do
  index <- newIndex
  withTypes (name =:= TiAbs TyTag {
               tdId    = index,
               tdArity = map (const Invariant) params,
               tdQual  = [],
               tdTrans = False
             })
    (outofC . k $ TdAbsC name params)
withTyDec (TdSynC name params rhs) k = intoC $ do
  t' <- withTVs params $ tcType rhs
  withTypes (name =:= TiSyn params t')
    (outofC . k $ TdSynC name params rhs)
withTyDec (TdSynA name params rhs) k = intoA $ do
  t' <- withTVs params $ tcType rhs
  withTypes (name =:= TiSyn params t')
    (outofA . k $ TdSynA name params rhs)
withTyDec (TdDatC name params alts) k = intoC $ do
  index <- newIndex
  let tag = TyTag {
              tdId    = index,
              tdArity = map (const Invariant) params,
              tdQual  = [],
              tdTrans = False
            }
  alts' <- withTVs params $
    withTypes (name =:= TiDat tag M.empty) $
      sequence
        [ case mt of
            Nothing -> return (cons, Nothing)
            Just t  -> do
              t' <- tcType t
              return (cons, Just t')
        | (cons, mt) <- alts ]
  withTypes (name =:= TiDat tag (M.fromList alts')) $
    withVars (alts2env name params tag alts') $
      (outofC . k $ TdDatC name params alts)
withTyDec (TdDatA name params alts) k = intoA $ do
  index <- newIndex
  let tag0 = TyTag {
               tdId    = index,
               tdArity = map (const 0) params,
               tdQual  = [],
               tdTrans = False
             }
  (tag, alts') <- fixDataType name params alts tag0
  unsafePerformIO $ do
    print tag
    return $
      withTypes (name =:= TiDat tag (M.fromList alts')) $
        withVars (alts2env name params tag alts') $
          (outofA . k $ TdDatA name params alts)

fixDataType :: Monad m =>
               Lid -> [TyVar] -> [(Uid, Maybe (Type () A))] ->
               TyTag -> TC A m (TyTag, [(Uid, Maybe (TypeT A))])
fixDataType name params alts = loop where
  loop :: Monad m => TyTag -> TC A m (TyTag, [(Uid, Maybe (TypeT A))])
  loop tag = do
    alts' <- withTVs params $
      withTypes (name =:= TiDat tag M.empty) $
        sequence
          [ case mt of
              Nothing -> return (k, Nothing)
              Just t  -> do
                t' <- tcType t
                return (k, Just t')
          | (k, mt) <- alts ]
    let t'    = foldl tyTupleT tyUnitT [ t | (_, Just t) <- alts' ]
        arity = typeVariances params t'
        qual  = typeQual params t'
    if arity == tdArity tag && qual == tdQual tag
      then return (tag, alts')
      else loop tag {
             tdArity = arity,
             tdQual  = qual
           }

alts2env :: Lid -> [TyVar] -> TyTag -> [(Uid, Maybe (TypeT w))] -> G w
alts2env name params tag = fromList . map each where
  each (uid, Nothing) = (Con uid, alls result)
  each (uid, Just t)  = (Con uid, alls (t `tyArrT` result))
  alls t              = foldr TyAll t params
  result              = TyCon name (map TyVar params) tag

typeVariances :: [TyVar] -> TypeT A -> [Variance]
typeVariances d0 = finish . loop where
  finish m = [ maybe 0 id (M.lookup tv m)
             | tv <- d0 ]

  loop :: TypeT A -> M.Map TyVar Variance
  loop (TyCon _ ts info)
                    = M.unionsWith (\/)
                        (zipWith
                          (\t v -> M.map (* v) (loop t))
                          ts
                          (tdArity info))
  loop (TyVar tv)   = M.singleton tv 1
  loop (TyAll tv t) = M.delete tv (loop t)
  loop (TyMu tv t)  = M.delete tv (loop t)
  loop (TyC t)      = loopC t
  loop _            = error "Can't get TyA here"

  loopC :: TypeT C -> M.Map TyVar Variance
  loopC (TyCon _ ps _) = M.unionsWith (\/) (map loopC ps)
  loopC (TyVar _)      = M.empty
  loopC (TyAll _ t)    = loopC t
  loopC (TyMu _ t)     = loopC t
  loopC (TyA t)        = M.map (const Invariant) (loop t)
  loopC _              = error "Can't get TyC here"

typeQual :: [TyVar] -> TypeT A -> [Either Int Q]
typeQual d0 = finish . loop where
  finish es = [ e | Just e <-
                  [ case e of
                      Right q -> Just (Right q)
                      Left tv -> fmap Left (elemIndex tv d0)
                  | e <- S.toList es ] ]

  loop :: TypeT A -> S.Set (Either TyVar Q)
  loop (TyCon _ ts info)
                    = S.unions
                        [ case qual of
                            Right q -> S.singleton (Right q)
                            Left i  -> loop (ts !! i)
                        | qual <- tdQual info ]
  loop (TyVar tv)   = S.singleton (Left tv)
  loop (TyAll tv t) = S.delete (Left tv) (loop t)
  loop (TyMu tv t)  = S.delete (Left tv) (loop t)
  loop _            = S.empty

withMod :: (Language w, Monad m) =>
         Mod i -> (ModT -> TC w m a) -> TC w m a
withMod (MdC x mt e) k = intoC $ do
  (te, e') <- tcExprC e
  t' <- case mt of
    Just t  -> do
      t' <- tcType t
      tassert (te == t') $
        "Declared type for module " ++ show x ++ " : " ++ show t ++
        " doesn't match actual type " ++ show te
      return t'
    Nothing -> return te
  withVars (Var x =:= t') .
    intoA .
      withVars (Var x =:= ctype2atype t') .
        outofA .
          k $ MdC x (Just t') e'
withMod (MdA x mt e) k = intoA $ do
  (te, e') <- tcExprA e
  t' <- case mt of
    Just t  -> do
      t' <- tcType t
      tassert (qualifier t' == Qu) $
        "Declared type of module " ++ show x ++ " is not unlimited"
      tassert (te <: t') $
        "Declared type for module " ++ show x ++ " : " ++ show t' ++
        " is not subsumed by actual type " ++ show te
      return t'
    Nothing -> do
      tassert (qualifier te == Qu) $
        "Type of module " ++ show x ++ " is not unlimited"
      return te
  withVars (Var x =:= t') .
    intoC .
      withVars (Var x =:= atype2ctype t') .
        outofC .
          k $ MdA x (Just t') e'
withMod (MdInt x t y) k = do
  ty <- intoC $ getVar (Var y)
  t' <- intoA $ tcType t
  tassert (ty == atype2ctype t') $
    "Declared type of interface " ++ show x ++ " :> " ++
    show t' ++ " not compatible with RHS type: " ++ show ty
  intoA .
    withVars (Var x =:= t') .
      intoC .
        withVars (Var x =:= atype2ctype t') .
          outofC .
            k $ MdInt x t' y

withDecl :: (Language w, Monad m) =>
          Decl i -> (DeclT -> TC w m a) -> TC w m a
withDecl (DcMod m)  k = withMod m (k . DcMod)
withDecl (DcTyp td) k = withTyDec td (k . DcTyp)

withDecls :: Monad m => [Decl i] -> ([DeclT] -> TC C m a) -> TC C m a
withDecls []     k = k []
withDecls (d:ds) k = withDecl d $ \d' ->
                       withDecls ds $ \ds' ->
                         k (d':ds')

tcDecls :: Monad m => S -> [Decl i] -> m (S, [DeclT])
tcDecls gg ds = runTC gg $
                  withDecls ds $ \ds' -> do
                    gg' <- saveTC
                    return (gg', ds')

-- For adding types of primitives to the environment
addVal :: (Language w, Monad m) => S -> Ident -> Type i w -> m S
addVal gg x t = runTC gg $ do
  t' <- tcType t
  withVars (x =:= t') saveTC

addTyTag :: S -> Lid -> TyTag -> S
addTyTag gg n td =
  gg {
    cTypes = cTypes gg =+= n =:= TiAbs td,
    aTypes = aTypes gg =+= n =:= TiAbs td
  }

-- Type check a program
tcProg :: Monad m => S -> Prog i -> m (TypeT C, ProgT)
tcProg gg (Prog ds e) =
  runTC gg $
    withDecls ds $ \ds' -> do
      (t, e') <- tcExprC e
      return (t, Prog ds' e')

env0 :: S
env0 = S g0 g0 i0 i0 0 where
  g0 :: G w
  g0  = Con (Uid "()")    =:= tyUnitT =+=
        Con (Uid "true")  =:= tyBoolT =+=
        Con (Uid "false") =:= tyBoolT
  i0 :: I w
  i0  = Lid "unit" =:= TiDat tdUnit (M.fromList [
          (Uid "()",    Nothing)
        ]) =+=
        Lid "bool" =:= TiDat tdBool (M.fromList [
          (Uid "true",  Nothing),
          (Uid "false", Nothing)
        ])
