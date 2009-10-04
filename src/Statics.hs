{-# LANGUAGE
      DeriveDataTypeable,
      ImplicitParams,
      ScopedTypeVariables #-}
module Statics (
  S, env0,
  tcProg, tcDecls,
  addVal, addTyTag
) where

import Util
import Syntax
import Loc
import Env as Env
import Ppr ()

import Data.Data (Typeable, Data)
import qualified Data.Map as M
import qualified Data.Set as S

import qualified Control.Monad.Reader as M.R
import qualified Control.Monad.State  as M.S
import qualified Control.Monad.RWS    as RWS

-- import System.IO.Unsafe (unsafePerformIO)
-- p :: (Show a) => a -> b -> b
-- p a b = unsafePerformIO (print a) `seq` b
-- p = const

-- Get the usage (sharing) of a variable in an expression:
usage :: QLid -> Expr i A -> Q
usage x e = case M.lookup x (fv e) of
  Just u | u > 1 -> Qu
  _              -> Qa

-- Type constructors are bound to either "type info" or a synonym
data TyInfo w = TiAbs TyTag
              | TiSyn [TyVar] (TypeT w)
              | TiDat TyTag [TyVar] (Env Uid (Maybe (TypeT w)))
  deriving (Data, Typeable)

-- Type environments
type D   = Env TyVar TyVar       -- tyvars in scope, with idempot. renaming
type G w = Env BIdent (TypeT w)  -- types of variables in scope
type I w = Env Lid (TyInfo w)    -- type constructors in scope

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
  fail    = TC . fail

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
                     (empty, empty)
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

withTVs :: Monad m => [TyVar] -> ([TyVar] -> TC w m a) -> TC w m a
withTVs tvs m = TC $ do
  TCEnv g ii (d, dw) <- M.R.ask
  let (d', tvs') = foldr rename (d, []) tvs
      r'         = TCEnv g ii (d', dw)
  M.R.local (const r') (unTC (m tvs'))
    where
      rename :: TyVar -> (D, [TyVar]) -> (D, [TyVar])
      rename tv (d, tvs') =
        let tv' = case d =.= tv of
                    Nothing -> tv
                    Just _  -> tv `freshTyVar` unEnv d
        in (d =+= tv =:+= tv', tv':tvs')

withVars :: Monad m => G w -> TC w m a -> TC w m a
withVars g' = TC . M.R.local add . unTC where
  add (TCEnv (g, gw) ii dd) = TCEnv (g =+= g', gw) ii dd

withDG :: Monad m => D -> G w -> TC w m a -> TC w m a
withDG d' g' = TC . M.R.local add . unTC where
  add (TCEnv (g, gw) ii (d, dw)) = TCEnv (g =+= g', gw) ii (d =+= d', dw)

withTypes :: (?loc :: Loc, Monad m) => I w -> TC w m a -> TC w m a
withTypes i' = TC . M.R.local add . unTC where
  add (TCEnv g (i, iw) dd) = TCEnv g (i =+= i', iw) dd

withoutConstructors :: Monad m => TyTag -> TC w m a -> TC w m a
withoutConstructors tag = TC . M.R.local clean . unTC where
  clean (TCEnv (g, gw) ii dd) =
    TCEnv (fromList (filter keep (toList g)), gw) ii dd
  keep (BCon _, TyCon _ [_, TyCon _ _ tag'] _) = tag' /= tag
  keep (BCon _, TyCon _ _ tag')                = tag' /= tag
  keep _                                       = True

withReplacedTyTags :: (Language w, Data w, Monad m) =>
                      TyTag -> TC w m a -> TC w m a
withReplacedTyTags tag = TC . M.R.local replace . unTC where
  replace (TCEnv (g, g') (i, i') dd) =
    langCase (WrapGI g i)
      (\_ -> TCEnv (r g, r g') (r i, r i') dd)
      (\_ -> TCEnv (r g, r g') (r i, r i') dd)
  r a = replaceTyTags tag a

getTV :: (?loc :: Loc, Monad m) => TyVar -> TC w m TyVar
getTV tv = TC $ asksM check where
  check (TCEnv _ _ (d, _)) = case d =.= tv of
    Just tv' -> return tv'
    _        -> terr $ "Free type variable: " ++ show tv

getVar :: (?loc :: Loc, Monad m) => Ident -> TC w m (TypeT w)
getVar qx = TC $ asksM get where
  get (TCEnv (g, _) _ _) = g =.= x
    |! "Unbound variable: " ++ show x
  x = case qx of
        Var (QLid _ lid) -> BVar lid 
        Con (QUid _ uid) -> BCon uid 

tryGetVar :: Monad m => Ident -> TC w m (Maybe (TypeT w))
tryGetVar qx = TC $ asksM get where
  get (TCEnv (g, _) _ _) = return (g =.= x)
  x = case qx of
        Var (QLid _ lid) -> BVar lid 
        Con (QUid _ uid) -> BCon uid 

getType :: (?loc :: Loc, Monad m) => QLid -> TC w m (TyInfo w)
getType qn = TC $ asksM get where
  get (TCEnv _ (i, _) _) = i =.= n
    |! "Unbound type constructor: " ++ show n
  QLid _ n = qn

getTypeTag :: (?loc :: Loc, Monad m) => String -> QLid -> TC w m TyTag
getTypeTag who n = do
  ti <- getType n
  case ti of
    TiAbs td     -> return td
    TiSyn _ _    -> terr $
      who ++ " expects an abstract or data type, but " ++
      "got type synonym: " ++ show n
    TiDat td _ _ -> return td

-- Raise a type error
terr :: (?loc :: Loc, Monad m) => String -> m a
terr  = fail . (label ++)
  where label = "Type error: " ++ if isBogus ?loc
                                    then ""
                                    else show ?loc ++ ": "

-- A type checking "assertion" raises a type error if the
-- asserted condition is false.
tassert :: (?loc :: Loc, Monad m) =>
           Bool -> String -> m ()
tassert True  _ = return ()
tassert False s = terr s

-- A common form of type error
tgot :: (?loc :: Loc, Monad m) =>
        String -> Type i w -> String -> m a
tgot who got expected = terr $ who ++ " got " ++ show got ++
                               " where " ++ expected ++ " expected"

-- Combination of tassert and tgot
tassgot :: (?loc :: Loc, Monad m) =>
           Bool -> String -> Type i w -> String -> m ()
tassgot False = tgot
tassgot True  = \_ _ _ -> return ()

-- Run a partial computation, and if it fails, substitute
-- the given failure message.
(|!) :: (?loc :: Loc, Monad m) => Maybe a -> String -> m a
m |! s = case m of
  Just r  -> return r
  _       -> terr s
infix 1 |!

-- Check type for closed-ness and and defined-ness, and add info
tcType :: (?loc :: Loc, Language w, Monad m) =>
          Type i w -> TC w m (TypeT w)
tcType = tc where
  tc :: (Language w, Monad m) => Type i w -> TC w m (TypeT w)
  tc (TyVar tv)   = do
    tv' <- getTV tv
    return (TyVar tv')
  tc (TyCon n ts _) = do
    ts'  <- mapM tc ts
    tcon <- getType n
    case tcon of
      TiAbs td -> do
        checkLength (length (ttArity td))
        return (TyCon n ts' td)
      TiSyn ps t -> return (tysubsts ps ts' t)
      TiDat td _ _ -> do
        checkLength (length (ttArity td))
        return (TyCon n ts' td)
    where
      checkLength len =
        tassert (length ts == len) $
          "Type constructor " ++ show n ++ " applied to " ++
          show (length ts) ++ " arguments where " ++
          show len ++ " expected"
  tc (TyQu u tv t) = withTVs [tv] $ \[tv'] -> TyQu u tv' `liftM` tc t
  tc (TyMu  tv t) = withTVs [tv] $ \[tv'] -> do
    t' <- tc t
    langCase t'
      (\_ -> return ())
      (\_ -> tassert (qualifier t' == tvqual tv) $
         "Recursive type " ++ show (TyMu tv t) ++ " qualifier " ++
         "does not match its own type variable.")
    return (TyMu tv' t')
  tc (TyC t)      = ctype2atype `liftM` intoC (tc t)
  tc (TyA t)      = atype2ctype `liftM` intoA (tc t)

-- Given a list of type variables and types, perform all the
-- substitutions, avoiding capture between them.
tysubsts :: Language w => [TyVar] -> [TypeT w] -> TypeT w -> TypeT w
tysubsts ps ts t =
  let ps'     = freshTyVars ps (ftv (t:ts))
      substs :: Language w =>
                [TyVar] -> [TypeT w] -> TypeT w -> TypeT w
      substs tvs ts0 t0 = foldr2 tysubst t0 tvs ts0 in
  substs ps' ts .
    substs ps (map TyVar ps') $
      t

-- Type check an expression
tcExprC :: Monad m => Expr i C -> TC C m (TypeT C, ExprT C)
tcExprC = tc where
  tc :: Monad m => Expr i C -> TC C m (TypeT C, ExprT C)
  tc e0 = let ?loc = getLoc e0 in case view e0 of
    ExId x -> do
      tx <- getVar x
      return (tx, exId x)
    ExStr s   -> return (TyCon (qlid "string") [] tdString, exStr s)
    ExInt z   -> return (TyCon (qlid "int") [] tdInt, exInt z)
    ExFloat f -> return (TyCon (qlid "float") [] tdFloat, exFloat f)
    ExCase e1 clauses -> do
      (t1, e1') <- tc e1
      (ti:tis, clauses') <- liftM unzip . forM clauses $ \(xi, ei) -> do
        (_, xi', ti, ei') <- withPatt t1 xi $ tc ei
        return (ti, (xi', ei'))
      forM_ tis $ \ti' ->
        tassert (ti == ti') $
          "Mismatch in match/let: " ++ show ti ++ " /= " ++ show ti'
      return (ti, exCase e1' clauses')
    ExLetRec bs e2 -> do
      tfs <- mapM (tcType . bntype) bs
      let makeG seen (b:bs') (t:ts') = do
            tassert (bnvar b `notElem` seen) $
              "Duplicate binding in let rec: " ++ show (bnvar b)
            tassert (syntacticValue (bnexpr b)) $
              "Not a syntactic value in let rec: " ++ show (bnexpr b)
            g' <- makeG (bnvar b : seen) bs' ts'
            return (g' =+= bnvar b =:= t)
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
      return (TyCon (qlid "*") [t1, t2] tdTuple, exPair e1' e2')
    ExAbs x t e     -> do
      t' <- tcType t
      (_, x', te, e') <- withPatt t' x $ tc e
      return (tyArrT t' te, exAbs x' t' e')
    ExApp _ _     -> do
      tcExApp (==) tc e0
    ExTAbs tv e   ->
      withTVs [tv] $ \[tv'] -> do
        tassert (syntacticValue e) $
          "Not a syntactic value under type abstraction: " ++ show e0
        (t, e') <- tc e
        return (tyAll tv' t, exTAbs tv' e')
    ExTApp e1 t2  -> do
      (t1, e1') <- tc e1
      t2'       <- tcType t2
      t1'       <- tapply t1 t2'
      return (t1', exTApp e1' t2')
    ExPack t1 t2 e -> do
      t1'      <- tcType t1
      t2'      <- tcType t2
      (te, e') <- tc e
      case t1' of
        TyQu Exists tv t11' -> do
          te' <- tapply (tyAll tv t11') t2'
          tassert (te == te') $
            "Could not pack type " ++ show te ++
            " (abstracting " ++ show t2 ++
            ") to get " ++ show t1
          return (t1', exPack t1' t2' e')
        _ -> tgot "Pack[-]" t1' "ex(istential) type"
    ExCast e1 t ta -> do
      t'  <- tcType t
      ta' <- intoA $ tcType ta
      tassgot (castableType t')
        "cast (:>)" t' "function type"
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
  tc e0 = let ?loc = getLoc e0 in case view e0 of
    ExId x -> do
      tx <- getVar x
      return (tx, exId x)
    ExStr s   -> return (TyCon (qlid "string") [] tdString, exStr s)
    ExInt z   -> return (TyCon (qlid "int") [] tdInt, exInt z)
    ExFloat f -> return (TyCon (qlid "float") [] tdFloat, exFloat f)
    ExCase e clauses -> do
      (t0, e') <- tc e
      (t1:ts, clauses') <- liftM unzip . forM clauses $ \(xi, ei) -> do
        (gi, xi', ti, ei') <- withPatt t0 xi $ tc ei
        checkSharing "match" gi ei
        return (ti, (xi', ei'))
      tr <- foldM (\ti' ti -> ti' \/? ti
                      |! "Mismatch in match/let: " ++ show ti ++
                          " and " ++ show ti')
            t1 ts
      return (tr, exCase e' clauses')
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
            return (g' =+= bnvar b =:= t)
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
      return (TyCon (qlid "*") [t1, t2] tdTuple, exPair e1' e2')
    ExAbs x t e     -> do
      t' <- tcType t
      (gx, x', te, e') <- withPatt t' x $ tc e
      checkSharing "lambda" gx e
      unworthy <- isUnworthy e0
      if unworthy
        then return (tyLolT t' te, exAbs x' t' e')
        else return (tyArrT t' te, exAbs x' t' e')
    ExApp _  _    -> do
      tcExApp (<:) tc e0
    ExTAbs tv e   ->
      withTVs [tv] $ \[tv'] -> do
        tassert (syntacticValue e) $
          "Not a syntactic value under type abstraction: " ++ show e0
        (t, e') <- tc e
        return (tyAll tv' t, exTAbs tv' e')
    ExTApp e1 t2  -> do
      (t1, e1') <- tc e1
      t2'       <- tcType t2
      t1'       <- tapply t1 t2'
      return (t1', exTApp e1' t2')
    ExPack t1 t2 e -> do
      t1'      <- tcType t1
      t2'      <- tcType t2
      (te, e') <- tc e
      case t1' of
        TyQu Exists tv t11' -> do
          te' <- tapply (tyAll tv t11') t2'
          tassert (te <: te') $
            "Could not pack type " ++ show te ++
            " (abstracting " ++ show t2 ++
            ") to get " ++ show t1
          return (t1', exPack t1' t2' e')
        _ -> tgot "Pack[-]" t1' "ex(istential) type"
    ExCast e1 t ta -> do
      t'  <- tcType t
      ta' <- tcType ta
      tassgot (castableType t')
        "cast (:>)" t' "function type"
      (t1, e1') <- tc e1
      tassgot (t1 <: t')
        "cast (:>)" t1 (show t')
      t1 \/? ta' |!
        "Mismatch in cast: types " ++ show t1 ++
        " and " ++ show t' ++ " are incompatible"
      return (ta', exCast e1' t' ta')

  checkSharing name g e =
    forM_ (toList g) $ \(x, tx) ->
      case x of
        BVar x' ->
          tassert (qualifier tx <: usage (QLid [] x') e) $
            "Affine variable " ++ show x' ++ " : " ++
            show tx ++ " duplicated in " ++ name ++ " body"
        _ -> return ()

  isUnworthy e =
    anyM (\x -> do
           mtx <- tryGetVar (Var x)
           return $ case mtx of
             Just tx -> qualifier tx == Qa
             Nothing -> False)
         (M.keys (fv e))

tcExApp :: (?loc :: Loc, Language w, Monad m) =>
           (TypeT w -> TypeT w -> Bool) ->
           (Expr i w -> TC w m (TypeT w, ExprT w)) ->
           Expr i w -> TC w m (TypeT w, ExprT w)
tcExApp (<::) tc e0 = do
  let foralls t1 ts = do
        let (tvs, t1f) = unfoldTyQu Forall t1 -- peel off quantification
            (tas, _)   = unfoldTyFun t1f      -- peel off arg types
            nargs      = min (length tas) (length ts)
            tup ps     = TyCon (qlid "") (take nargs ps) tdTuple
        -- try to find types to unify formals and actuals, and apply
        t1' <- tryUnify tvs (tup tas) (tup ts) >>= foldM tapply t1
        arrows t1' ts
      arrows tr                   [] = return tr
      arrows t'@(TyQu Forall _ _) ts = foralls t' ts
      arrows (TyCon _ [ta, tr] td) (t:ts) | td `elem` funtypes = do
        b <- unifies [] t ta
        tassgot b "Application (operand)" t (show ta)
        arrows tr ts
      arrows t' _ = tgot "Application (operator)" t' "function type"
      unifies tvs ta tf =
        case tryUnify tvs ta tf of
          Just ts  -> do
            ta' <- foldM tapply (foldr tyAll ta tvs) ts
            if (ta' <:: tf)
              then return True
              else deeper
          Nothing -> deeper
        where
          deeper = case ta of
            TyQu Forall tv ta1 -> unifies (tvs++[tv]) ta1 tf
            _                  -> return False
  let (es, e1) = unfoldExApp e0            -- get operator and args
  (t1, e1')   <- tc e1                     -- check operator
  (ts, es')   <- unzip `liftM` mapM tc es  -- check args
  tr <- foralls t1 ts
  return (tr, foldl exApp e1' es')

tapply :: (?loc :: Loc, Language w, Monad m) =>
          TypeT w -> TypeT w -> m (TypeT w)
tapply (TyQu Forall tv t1') t2 = do
  langCase t2
    (\_ -> return ())
    (\_ ->
      tassert (qualifier t2 <: tvqual tv) $
        "Type application cannot instantiate type variable " ++
        show tv ++ " with type " ++ show t2)
  return (tysubst tv t2 t1')
tapply t1 _ = tgot "type application" t1 "(for)all type"

-- Given the type of thing to match and a pattern, return
-- the type environment bound by that pattern.
tcPatt :: (?loc :: Loc, Monad m, Language w) =>
          TypeT w -> Patt -> TC w m (D, G w, Patt)
tcPatt t x0 = case x0 of
  PaWild     -> return (empty, empty, PaWild)
  PaVar x    -> return (empty, BVar x =:= t, PaVar x)
  PaCon u mx -> do
    case t of
      TyCon name ts tag -> do
        tcon <- getType name
        case tcon of
          TiDat tag' params alts | tag == tag' -> do
            case alts =.= u of
              Nothing -> tgot "Pattern" t ("constructor " ++ show u)
              Just mt -> case (mt, mx) of
                (Nothing, Nothing) -> return (empty, empty, PaCon u Nothing)
                (Just t1, Just x1) -> do
                  let t1' = tysubsts params ts t1
                  (dx1, gx1, x1') <- tcPatt t1' x1
                  return (dx1, gx1, PaCon u (Just x1'))
                _ -> tgot "Pattern" t "different arity"
          _ ->
            terr $ "Pattern " ++ show x0 ++ " for type not in scope"
      _ -> tgot "Pattern" t ("constructor " ++ show u)
  PaPair x y -> do
    case t of
      TyCon (QLid [] (Lid "*")) [tx, ty] td | td == tdTuple
        -> do
          (dx, gx, x') <- tcPatt tx x
          (dy, gy, y') <- tcPatt ty y
          tassert (isEmpty (gx =|= gy)) $
            "Pattern " ++ show x0 ++ " binds variable twice"
          tassert (isEmpty (dx =|= dy)) $
            "Pattern " ++ show x0 ++ " binds type variable twice"
          return (dx =+= dy, gx =+= gy, PaPair x' y')
      _ -> tgot "Pattern" t "pair type"
  PaStr s    -> do
    tassgot (tyinfo t == tdString)
      "Pattern" t "string"
    return (empty, empty, PaStr s)
  PaInt z    -> do
    tassgot (tyinfo t == tdInt)
      "Pattern" t "int"
    return (empty, empty, PaInt z)
  PaAs x y   -> do
    (dx, gx, x') <- tcPatt t x
    let gy        = y =:= t
    tassert (isEmpty (gx =|= gy)) $
      "Pattern " ++ show x0 ++ " binds " ++ show y ++ " twice"
    return (dx, gx =+= gy, PaAs x' y)
  PaPack tv x -> do
    case t of
      TyQu Exists tve te -> do
        tassert (tvqual tve <: tvqual tv) $
          "Cannot bind existential tyvar " ++ show tv ++
          " to " ++ show tve
        withTVs [tv] $ \[tv'] -> do
          let te' = tysubst1 tve (TyVar tv') te
          (dx, gx, x') <- tcPatt te' x
          tassert (dx =.= tv == Nothing) $
            "Pattern " ++ show x0 ++ " binds " ++ show tv ++ " twice"
          return (dx =+= tv =:+= tv', gx, PaPack tv' x')
      _ -> tgot "Pattern" t "existential type"

withPatt :: (?loc :: Loc, Monad m, Language w) =>
            TypeT w -> Patt -> TC w m (TypeT w, e) ->
            TC w m (G w, Patt, TypeT w, e)
withPatt t x m = do
  (d, g, x') <- tcPatt t x
  (t', e')   <- withDG d g m
  tcType t'
  return (g, x', t', e')

-- Given a list of type variables tvs, an type t in which tvs
-- may be free, and a type t', tries to substitute for tvs in t
-- to produce a type that *might* unify with t'
tryUnify :: (?loc :: Loc, Monad m, Language w) =>
            [TyVar] -> TypeT w -> TypeT w -> m [TypeT w]
tryUnify [] _ _        = return []
tryUnify (tv:tvs) t t' =
  case findSubst tv t t' of
    tguess:_ -> do
                  let subst' = tysubst tv tguess
                  tguesses <- tryUnify tvs (subst' t) t'
                  return (tguess : tguesses)
    _        -> terr $
                  "Cannot guess type t such that (" ++ show t ++
                  ")[t/" ++ show tv ++ "] ~ " ++ show t'

-- Given a type variable tv, type t in which tv may be free,
-- and a second type t', finds a plausible candidate to substitute
-- for tv to make t and t' unify.  (The answer it finds doesn't
-- have to be correct.
findSubst :: forall w. Language w => TyVar -> TypeT w -> TypeT w -> [TypeT w]
findSubst tv = chk True [] where
  chk, cmp :: Language w' =>
              Bool -> [(TypeTW, TypeTW)] -> TypeT w' -> TypeT w' -> [TypeT w']
  chk b seen t1 t2 =
    let tw1 = typeTW t1; tw2 = typeTW t2
     in if (tw1, tw2) `elem` seen
          then []
          else cmp b ((tw1, tw2) : seen) t1 t2

  cmp True _  (TyVar tv') t'
    | tv == tv'    = [t']
  cmp False _ (TyA (TyVar tv')) t'
    | tv == tv'    = [t']
  cmp False _ (TyC (TyVar tv')) t'
    | tv == tv'    = [t']
  cmp b seen (TyCon _ [t] td) t'
    | td == tdDual = chk b seen (dualSessionType t) t'
  cmp b seen t' (TyCon _ [t] td)
    | td == tdDual = chk b seen t' (dualSessionType t)
  cmp b seen (TyCon _ ts _) (TyCon _ ts' _)
                   = concat (zipWith (chk b seen) ts ts')
  cmp b seen (TyQu _ tv0 t) (TyQu _ tv0' t')
    | tv /= tv0    = [ tr | tr <- chk b seen t t',
                            not (tv0  `M.member` ftv tr),
                            not (tv0' `M.member` ftv tr) ]
  cmp b seen (TyC t) (TyC t')
                   = ctype2atype `map` cmp (not b) seen t t'
  cmp b seen (TyA t) (TyA t')
                   = atype2ctype `map` cmp (not b) seen t t'
  cmp b seen (TyMu a t) t'
                   = chk b seen (tysubst a (TyMu a t) t) t'
  cmp b seen t' (TyMu a t)
                   = chk b seen t' (tysubst a (TyMu a t) t)
  cmp _ _ _ _        = []

indexQuals :: (?loc :: Loc, Monad m) =>
              Lid -> [TyVar] -> [Either TyVar Q] -> TC w m QualSet
indexQuals name = qsFromListM unbound where
  unbound tv = terr $ "unbound tyvar " ++ show tv ++
                      " in qualifier list for type " ++ show name
-- BEGIN type decl checking

withTyDec :: (?loc :: Loc, Language w, Monad m) =>
             TyDec -> (TyDec -> TC w m a) -> TC w m a
withTyDec (TyDecC tl tds0) k0 = intoC $ do
  tassert (unique (map tdcName tds0)) $
    "Duplicate type(s) in recursive type declaration"
  let (atds, stds0, dtds) = foldr partition ([], [], []) tds0
  stds <- topSort getEdge stds0
  -- We need to:
  --  1) Add stubs for datatypes
  --  2) Visit all types in order:
  --     a) abstract
  --     b) synonyms, topologically sorted
  --     c) datatypes again
  mapCont_ withStub dtds $
    mapCont withTyDecC (atds ++ stds ++ dtds) $
      \tds' -> outofC $
        k0 (TyDecC tl tds')
  where
    withStub (TdDatC name params _) k = do
      index <- newIndex
      let tag = TyTag {
                  ttId    = index,
                  ttArity = map (const Invariant) params,
                  ttQual  = minBound,
                  ttTrans = False
                }
      withTypes (name =:= TiDat tag params empty) k
    withStub _           k = k
    getEdge (TdSynC name _ ty)   = (name, tyConsOfType True ty)
    getEdge (TdAbsC name _)      = (name, S.empty)
    getEdge (TdDatC name _ alts) = (name, names) where
       names = S.unions [ tyConsOfType True ty | (_, Just ty) <- alts ]
    partition td (atds, stds, dtds) =
      case td of
        TdAbsC _ _   -> (td : atds, stds, dtds)
        TdSynC _ _ _ -> (atds, td : stds, dtds)
        TdDatC _ _ _ -> (atds, stds, td : dtds)
withTyDec (TyDecA tl tds0) k0 = intoA $ do
  tassert (unique (map tdaName tds0)) $
    "Duplicate type(s) in recursive type declaration"
  let (atds, stds0, dtds) = foldr partition ([], [], []) tds0
  stds <- topSort getEdge stds0
  mapCont_ withStub dtds $
    let loop =
          mapCont withTyDecA (atds ++ stds ++ dtds) $
            \tds'changed ->
              if any snd tds'changed
                then loop
                else outofA $ k0 (TyDecA tl (map fst tds'changed))
     in loop
  where
    withStub (TdDatA name params _) k = do
      index <- newIndex
      let tag = TyTag {
                  ttId    = index,
                  ttArity = map (const Omnivariant) params,
                  ttQual  = minBound,
                  ttTrans = False
                }
      withTypes (name =:= TiDat tag params empty) k
    withStub _           k = k
    getEdge (TdSynA name _ ty)   = (name, tyConsOfType True ty)
    getEdge (TdAbsA name _ _ _)  = (name, S.empty)
    getEdge (TdDatA name _ alts) = (name, names) where
       names = S.unions [ tyConsOfType True ty | (_, Just ty) <- alts ]
    partition td (atds, stds, dtds) =
      case td of
        TdAbsA _ _ _ _ -> (td : atds, stds, dtds)
        TdSynA _ _ _   -> (atds, td : stds, dtds)
        TdDatA _ _ _   -> (atds, stds, td : dtds)

withTyDecC :: (?loc :: Loc, Monad m) =>
              TyDecC -> (TyDecC -> TC C m a) -> TC C m a
withTyDecC (TdAbsC name params) k = do
  index <- newIndex
  withTypes (name =:= TiAbs TyTag {
               ttId    = index,
               ttArity = map (const Invariant) params,
               ttQual  = minBound,
               ttTrans = False
             })
    (k $ TdAbsC name params)
withTyDecC (TdSynC name params rhs) k = do
  t' <- withTVs params $ \params' -> TiSyn params' `liftM` tcType rhs
  withTypes (name =:= t')
    (k $ TdSynC name params rhs)
withTyDecC (TdDatC name params alts) k = do
  TiDat tag _ _ <- getType (QLid [] name)
  (params', alts') <-
    withTVs params $ \params' -> do
      alts' <- sequence
        [ case mt of
            Nothing -> return (cons, Nothing)
            Just t  -> do
              t' <- tcType t
              return (cons, Just t')
        | (cons, mt) <- alts ]
      return (params', alts')
  withTypes (name =:= TiDat tag params' (fromList alts')) $
    withVars (alts2env name params' tag alts') $
      (k $ TdDatC name params alts)

-- withTyDecA types an A type declaration, but in addition to
-- return (in CPS) a declaration, it returns a boolean that indicates
-- whether the type metadata has changed, which allows for iterating
-- to a fixpoint.
withTyDecA :: (?loc :: Loc, Monad m) =>
              TyDecA -> ((TyDecA, Bool) -> TC A m a) -> TC A m a
withTyDecA (TdAbsA name params variances quals) k = do
  index  <- newIndex
  quals' <- indexQuals name params quals
  withTypes (name =:= TiAbs TyTag {
               ttId    = index,
               ttArity = variances,
               ttQual  = quals',
               ttTrans = False
             })
    (k (TdAbsA name params variances quals, False))
withTyDecA (TdSynA name params rhs) k = do
  t' <- withTVs params $ \params' -> TiSyn params' `liftM` tcType rhs
  withTypes (name =:= t')
    (k (TdSynA name params rhs, False))
withTyDecA (TdDatA name params alts) k = do
  TiDat tag _ _ <- getType (QLid [] name)
  (params', alts') <-
    withTVs params $ \params' -> do
      alts' <- sequence
        [ case mt of
            Nothing -> return (cons, Nothing)
            Just t  -> do
              t' <- tcType t
              return (cons, Just t')
        | (cons, mt) <- alts ]
      return (params', alts')
  let t'      = foldl tyTupleT tyUnitT [ t | (_, Just t) <- alts' ]
      arity   = typeVariances params' t'
      qual    = typeQual params' t'
      changed = arity /= ttArity tag || qual /= ttQual tag
      tag'    = tag { ttArity = arity, ttQual = qual }
  withTypes (name =:= TiDat tag' params' (fromList alts')) $
    withVars (alts2env name params' tag' alts') $
      (k (TdDatA name params alts, changed))

unique :: Ord a => [a] -> Bool
unique  = loop S.empty where
  loop _    []     = True
  loop seen (x:xs) = x `S.notMember` seen && loop (S.insert x seen) xs

alts2env :: Lid -> [TyVar] -> TyTag -> [(Uid, Maybe (TypeT w))] -> G w
alts2env name params tag = fromList . map each where
  each (uid, Nothing) = (BCon uid, alls result)
  each (uid, Just t)  = (BCon uid, alls (t `tyArrT` result))
  alls t              = foldr tyAll t params
  result              = TyCon (QLid [] name) (map TyVar params) tag

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
                           (ttArity info))
  loop (TyVar tv)    = M.singleton tv 1
  loop (TyQu _ tv t) = M.delete tv (loop t)
  loop (TyMu tv t)   = M.delete tv (loop t)
  loop (TyC t)       = loopC t
  loop _             = error "Can't get TyA here"

  loopC :: TypeT C -> M.Map TyVar Variance
  loopC (TyCon _ ps _) = M.unionsWith (\/) (map loopC ps)
  loopC (TyVar _)      = M.empty
  loopC (TyQu _ _ t)   = loopC t
  loopC (TyMu _ t)     = loopC t
  loopC (TyA t)        = M.map (const Invariant) (loop t)
  loopC _              = error "Can't get TyC here"

typeQual :: [TyVar] -> TypeT A -> QualSet
typeQual d0 = qsFromList d0 . S.toList . loop where
  loop :: TypeT A -> S.Set (Either TyVar Q)
  loop (TyCon _ ts info)
                     = S.unions
                         [ case qual of
                             Right q -> S.singleton (Right q)
                             Left t  -> loop t
                         | qual <- qsToList ts (ttQual info) ]
  loop (TyVar tv)    = S.singleton (Left tv)
  loop (TyQu _ tv t) = S.delete (Left tv) (loop t)
  loop (TyMu tv t)   = S.delete (Left tv) (loop t)
  loop _             = S.empty

topSort :: forall node m a.
           (?loc :: Loc, Monad m, Ord node, Show node) =>
           (a -> (node, S.Set node)) -> [a] -> m [a]
topSort getEdge edges = do
  (_, w) <- RWS.execRWST visitAll S.empty S.empty
  return w
  where
    visitAll = mapM_ visit (M.keys graph)

    visit :: node -> RWS.RWST (S.Set node) [a] (S.Set node) m ()
    visit node = do
      stack <- RWS.ask
      tassert (not (node `S.member` stack)) $
        "unproductive cycle in type definitions, via type " ++ show node
      seen <- RWS.get
      if node `S.member` seen
        then return ()
        else do
          RWS.put (S.insert node seen)
          case M.lookup node graph of
            Just (succs, info) -> do
              RWS.local (S.insert node) $
                mapM_ visit succs
              RWS.tell [info]
            Nothing ->
              return ()

    graph :: M.Map node ([node], a)
    graph = M.fromList [ let (node, succs) = getEdge info
                          in (node, (S.toList succs, info))
                       | info <- edges ]

-- END type decl checking

tyConsOfType :: Bool -> Type i w -> S.Set Lid
tyConsOfType here (TyCon n ts _) =
  (case (here, n) of
    (True, QLid [] lid) -> S.singleton lid
    _                   -> S.empty)
  `S.union` S.unions (map (tyConsOfType here) ts)
tyConsOfType _    (TyVar _)        = S.empty
tyConsOfType here (TyQu _ _ ty)    = tyConsOfType here ty
tyConsOfType here (TyMu _ ty)      = tyConsOfType here ty
tyConsOfType here (TyC ty)         = tyConsOfType (not here) ty
tyConsOfType here (TyA ty)         = tyConsOfType (not here) ty

withLet :: (?loc :: Loc, Language w, Monad m) =>
           Let i -> (LetT -> TC w m a) -> TC w m a
withLet (LtC tl x mt e) k = intoC $ do
  (te, e') <- tcExprC e
  t' <- case mt of
    Just t  -> do
      t' <- tcType t
      tassert (te == t') $
        "Declared type for module " ++ show x ++ " : " ++ show t ++
        " doesn't match actual type " ++ show te
      return t'
    Nothing -> return te
  withVars (BVar x =:= t') .
    intoA .
      withVars (BVar x =:= ctype2atype t') .
        outofA .
          k $ LtC tl x (Just t') e'
withLet (LtA tl x mt e) k = intoA $ do
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
  withVars (BVar x =:= t') .
    intoC .
      withVars (BVar x =:= atype2ctype t') .
        outofC .
          k $ LtA tl x (Just t') e'
withLet (LtInt tl x t y) k = do
  ty <- intoC $ getVar (Var y)
  t' <- intoA $ tcType t
  tassert (ty == atype2ctype t') $
    "Declared type of interface " ++ show x ++ " :> " ++
    show t' ++ " not compatible with RHS type: " ++ show ty
  intoA .
    withVars (BVar x =:= t') .
      intoC .
        withVars (BVar x =:= atype2ctype t') .
          outofC .
            k $ LtInt tl x t' y

withDecl :: Monad m =>
            Decl i -> (DeclT -> TC C m a) -> TC C m a
withDecl (DcLet loc m)     k = withLet m (k . DcLet loc)
  where ?loc = loc
withDecl (DcTyp loc td)    k = withTyDec td (k . DcTyp loc)
  where ?loc = loc
withDecl (DcAbs loc at ds) k = withAbsTy at ds (k .  DcAbs loc at)
  where ?loc = loc

withDecls :: Monad m => [Decl i] -> ([DeclT] -> TC C m a) -> TC C m a
withDecls []     k = k []
withDecls (d:ds) k = withDecl d $ \d' ->
                       withDecls ds $ \ds' ->
                         k (d':ds')

withAbsTy :: (?loc :: Loc, Monad m) =>
             AbsTy -> [Decl i] -> ([DeclT] -> TC C m a) -> TC C m a
withAbsTy at ds k0 = case at of
  AbsTyC tl tds ->
    withTyDec (TyDecC tl tds) $ \_ ->
      withDecls ds $ \ds' -> do
        mapCont absDecl tds $ \tags' ->
          k0 (foldr replaceTyTags ds' tags')
    where
      absDecl (TdDatC name params _) k = do
        tag <- getTypeTag "abstract-with-end" (QLid [] name)
        tassert (length params == length (ttArity tag)) $
          "abstype-with-end: " ++ show (length params) ++
          " given for type " ++ show name ++
          " which has " ++ show (length (ttArity tag))
        let tag' = tag
        withoutConstructors tag' .
          withReplacedTyTags tag' .
            withTypes (name =:= TiAbs tag') $
              k tag'
      absDecl _ _ = terr "(BUG) Can't abstract non-datatypes"
  AbsTyA tl atds -> 
    let (_, _, tds) = unzip3 atds in
    withTyDec (TyDecA tl tds) $ \_ ->
      withDecls ds $ \ds' -> intoA $ do
        mapCont absDecl atds $ \tags' ->
          outofA $ k0 (foldr replaceTyTags ds' tags')
    where
      absDecl (arity, quals, TdDatA name params _) k = do
        tag     <- getTypeTag "abstract-with-end" (QLid [] name)
        qualSet <- indexQuals name params quals
        tassert (length params == length (ttArity tag)) $
          "abstract-with-end: " ++ show (length params) ++
          " given for type " ++ show name ++
          " which has " ++ show (length (ttArity tag))
        tassert (all2 (<:) (ttArity tag) arity) $
          "abstract-with-end: declared arity for type " ++ show name ++
          ", " ++ show arity ++
          ", is more general than actual arity " ++ show (ttArity tag)
        tassert (ttQual tag <: qualSet) $ 
          "abstract-with-end: declared qualifier for type " ++ show name ++
          ", " ++ show qualSet ++
          ", is more general than actual qualifier " ++ show (ttQual tag)
        let tag' = TyTag (ttId tag) arity qualSet False
        withoutConstructors tag' .
          withReplacedTyTags tag' .
            withTypes (name =:= TiAbs tag') $
              k tag'
      absDecl _ _ = terr "(BUG) Can't abstract non-datatypes"

tcDecls :: Monad m => S -> [Decl i] -> m (S, [DeclT])
tcDecls gg ds = runTC gg $
                  withDecls ds $ \ds' -> do
                    gg' <- saveTC
                    return (gg', ds')

-- For adding types of primitives to the environment
addVal :: (Language w, Monad m) =>
          S -> BIdent -> Type i w -> m S
addVal gg x t = runTC gg $ do
  let ?loc = bogus
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
tcProg gg (Prog ds me) =
  runTC gg $
    withDecls ds $ \ds' -> do
      (t, e') <- case me of
                   Just e  -> do
                     (t, e') <- tcExprC e
                     return (t, Just e')
                   Nothing -> do
                     return (tyUnitT, Nothing)
      return (t, Prog ds' e')

env0 :: S
env0 = S g0 g0 i0 i0 0 where
  g0 :: G w
  g0  = BCon (Uid "()")    =:= tyUnitT =+=
        BCon (Uid "true")  =:= tyBoolT =+=
        BCon (Uid "false") =:= tyBoolT
  i0 :: I w
  i0  = Lid "unit" =:= TiDat tdUnit [] (
          Uid "()"    =:= Nothing
        ) =+=
        Lid "bool" =:= TiDat tdBool [] (
          Uid "true"  =:= Nothing =+=
          Uid "false" =:= Nothing
        )
