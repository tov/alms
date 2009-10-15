{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      FlexibleContexts,
      ImplicitParams,
      MultiParamTypeClasses,
      ScopedTypeVariables,
      TypeFamilies,
      TypeSynonymInstances,
      UndecidableInstances #-}
module Statics (
  S, env0,
  NewDefs(..), emptyNewDefs, TyInfo, tyInfoToDec,
  tcProg, tcDecls,
  addVal, addType, addExn, addMod
) where

import Util
import Syntax
import Loc
import Env as Env
import Ppr ()

import Data.Data (Typeable, Data)
import Data.Generics (everywhere, mkT, everywhereM, mkM)
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
              | TiExn TyTag (Env Uid (Maybe (TypeT w), ExnId))
  deriving (Data, Typeable, Show)

-- Type environments
type D = Env TyVar TyVar       -- tyvars in scope, with idempot. renaming

type V w     = Env BIdent (TypeT w) -- value env
type T w     = Env Lid (TyInfo w)   -- type env
data Level w = Level {
                 vlevel :: V w, -- values
                 tlevel :: T w  -- types
               }
  deriving (Typeable, Data)
data Both w  = Both (Level w) (Level (OtherLang w))
-- path env includes modules
type Scope w = PEnv Uid (Both w)
type E w = [Scope w]

emptyPath :: [Uid]
emptyPath  = []

instance GenEmpty (Level w) where
  genEmpty = Level empty empty
instance GenEmpty (Both w) where
  genEmpty = Both genEmpty genEmpty

instance GenExtend (Level w) (Level w) where
  Level ve te =+= Level ve' te' = Level (ve =+= ve') (te =+= te')
instance GenExtend (Level w) (V w) where
  level =+= ve' = level =+= Level ve' empty
instance GenExtend (Level w) (T w) where
  level =+= te' = level =+= Level empty te'
instance GenLookup (Level w) BIdent (TypeT w) where
  level =..= k = vlevel level =..= k
instance GenLookup (Level w) Lid (TyInfo w) where
  level =..= k = tlevel level =..= k

instance GenExtend (Both w) (Both w) where
  Both level other =+= Both level' other' =
    Both (level =+= level') (other =+= other')
instance GenExtend (Both w) (Level w) where
  Both level other =+= level' = Both (level =+= level') other
instance GenExtend (Both w) (V w) where
  both =+= ve' = both =+= Level ve' empty
instance GenExtend (Both w) (T w) where
  both =+= te' = both =+= Level empty te'
instance GenLookup (Both w) BIdent (TypeT w) where
  Both level _ =..= k = vlevel level =..= k
instance GenLookup (Both w) Lid (TyInfo w) where
  Both level _ =..= k = tlevel level =..= k

data S   = S {
             cEnv    :: E C,
             currIx  :: Integer
           }

-- collapse :: E w -> Scope w
-- collapse = foldr (flip (=+=)) genEmpty

-- The type checking monad
newtype TC w m a =
  TC { unTC :: M.R.ReaderT (TCEnv w) (M.S.StateT Integer m) a }
data TCEnv w = TCEnv (E w) (D, D)

instance GenLookup (TCEnv w) QUid (Scope w) where
  TCEnv env _ =..= k = env =..= k
instance GenLookup (TCEnv w) QLid (TyInfo w) where
  TCEnv env _ =..= k = env =..= k
instance GenLookup (TCEnv w) Ident (TypeT w) where
  TCEnv env _ =..= k = env =..= k
instance GenLookup (TCEnv w) TyVar TyVar where
  TCEnv _ (d, _) =..= k = d =..= k

instance GenExtend (TCEnv w) (Both w) where
  TCEnv env dd =+= env' = TCEnv (env =+= env') dd
instance GenExtend (TCEnv w) (Scope w) where
  TCEnv env dd =+= scope = TCEnv (env =+= scope) dd
instance GenExtend (TCEnv w) (Env Ident (TypeT w)) where
  TCEnv env dd =+= venv = TCEnv (env =+= venv) dd
instance GenExtend (TCEnv w) (Env Uid (Scope w)) where
  TCEnv env dd =+= menv = TCEnv (env =+= menv) dd
instance GenExtend (TCEnv w) (T w) where
  TCEnv env dd =+= tenv = TCEnv (env =+= tenv) dd
instance GenExtend (TCEnv w) (V w) where
  TCEnv env dd =+= venv = TCEnv (env =+= venv) dd
instance GenExtend (TCEnv w) D where
  TCEnv env (d, d') =+= tvs  = TCEnv env (d =+= tvs, d')

instance Monad m => Monad (TC w m) where
  m >>= k = TC (unTC m >>= unTC . k)
  return  = TC . return
  fail    = TC . fail

asksM :: M.R.MonadReader r m => (r -> m a) -> m a
asksM  = (M.R.ask >>=)

saveTC :: (Language w, Monad m) => Bool -> TC w m S
saveTC interactive = intoC $ do
  TCEnv env _ <- TC M.R.ask
  index       <- TC M.S.get
  let env' = if interactive
               then requalifyTypes [] env
               else env
  return S {
    cEnv   = env',
    currIx = index
  }

newtype WrapTC a m w = WrapTC { unWrapTC :: TC w m a }

runTC :: Monad m => S -> TC C m a -> m a
runTC s (TC m) = do
  let tc = TCEnv (cEnv s) (empty, empty)
      ix = currIx s
  M.S.evalStateT (M.R.runReaderT m tc) ix

switchE :: (Language' w, w ~ SameLang w) => E w -> E (OtherLang w)
switchE = map (fmap (\(Both level other) -> Both other level))

switchTC :: (Language' w, w ~ SameLang w) => TCEnv w -> TCEnv (OtherLang w)
switchTC (TCEnv env (d, d')) = TCEnv (switchE env) (d', d)

intoC :: Language' w => TC C m a -> TC w m a
intoC  = TC . M.R.withReaderT sw . unTC where
  sw tc = langCase tc id switchTC

intoA :: Language' w => TC A m a -> TC w m a
intoA  = TC . M.R.withReaderT sw . unTC where
  sw tc = langCase tc switchTC id

outofC :: Language' w => TC w m a -> TC C m a
outofC m = langCase (WrapTC m) unWrapTC (intoA . unWrapTC)

outofA :: Language' w => TC w m a -> TC A m a
outofA m = langCase (WrapTC m) (intoC . unWrapTC) unWrapTC

newIndex :: Monad m => TC w m Integer
newIndex  = TC $ do
  M.S.modify (+ 1)
  M.S.get

withTVs :: Monad m => [TyVar] -> ([TyVar] -> TC w m a) -> TC w m a
withTVs tvs m = TC $ do
  TCEnv env (d, dw) <- M.R.ask
  let (d', tvs') = foldr rename (d, []) tvs
      r'         = TCEnv env (d', dw)
  M.R.local (const r') (unTC (m tvs'))
    where
      rename :: TyVar -> (D, [TyVar]) -> (D, [TyVar])
      rename tv (d, tvs') =
        let tv' = case d =..= tv of
                    Nothing -> tv
                    Just _  -> tv `freshTyVar` unEnv d
        in (d =+= tv =:+= tv', tv':tvs')

withAny :: (Monad m, GenExtend (TCEnv w) e') =>
           e' -> TC w m a -> TC w m a
withAny e' = TC . M.R.local (=+= e') . unTC

withVars :: Monad m => V w -> TC w m a -> TC w m a
withVars  = withAny

withTypes :: Monad m => T w -> TC w m a -> TC w m a
withTypes = withAny

pushScope :: Monad m => TC C m a -> TC C m a
pushScope = TC . M.R.local push . unTC where
  push (TCEnv env dd) = TCEnv (genEmpty : env) dd

squishScope :: Monad m => TC C m a -> TC C m a
squishScope = TC . M.R.local squish . unTC where
  squish (TCEnv (e0:e1:es) dd) = TCEnv ((e1=+=e0):es) dd
  squish (TCEnv env        dd) = TCEnv env dd

askScope :: (Monad m, Language C) => TC C m (Scope C)
askScope  = do
  TCEnv env _ <- TC M.R.ask
  case env of
    scope:_ -> return scope
    []      -> return genEmpty

withoutConstructors :: forall m w a. Monad m =>
                       TyTag -> TC w m a -> TC w m a
withoutConstructors tag = TC . M.R.local clean . unTC where
  -- Note: only filters immediate scope -- should be right.
  clean (TCEnv env dd) = TCEnv (map eachScope env) dd
  eachScope      :: Scope w -> Scope w
  eachScope scope = genModify scope emptyPath fboth
  fboth          :: Both w -> Both w
  fboth (Both level other) 
                  = Both (flevel level) (flevel other)
  flevel         :: forall w'. Level w' -> Level w'
  flevel level    = level { vlevel = eachVe (vlevel level) }
  eachVe         :: forall w'. V w' -> V w'
  eachVe          = fromList . filter keep . toList
  keep           :: forall w'. (BIdent, TypeT w') -> Bool
  keep (Con _, TyCon _ [_, TyCon _ _ tag'] _) = tag' /= tag
  keep (Con _, TyCon _ _ tag')                = tag' /= tag
  keep _                                      = True

withReplacedTyTags :: forall w m a. (Language w, Monad m) =>
                      TyTag -> TC w m a -> TC w m a
withReplacedTyTags tag = intoC . TC . M.R.local reptc . unTC . outofC
  where
    reptc (TCEnv env dd) = TCEnv (map (fmap repboth) env) dd
    repboth (Both level other) = Both (r level) (r other)
    r a = replaceTyTags tag a

tryGetAny :: (Monad m, GenLookup (TCEnv w) k v, Show k) =>
             k -> TC w m (Maybe v)
tryGetAny k = TC $ asksM (return . (=..= k))

getAny :: (?loc :: Loc, Monad m, GenLookup (TCEnv w) k v, Show k) =>
          String -> k -> TC w m v
getAny msg k = do
  t <- tryGetAny k
  t |! msg ++ ": " ++ show k

getTV :: (?loc :: Loc, Monad m) => TyVar -> TC w m TyVar
getTV  = getAny "Free type variable"

getVar :: (?loc :: Loc, Monad m, Language w, w ~ SameLang w) =>
          Ident -> TC w m (Either (TypeT w) (TypeT (OtherLang w)))
getVar x = do
  t <- tryGetVar x
  t |! "Unbound variable: " ++ show x

tryGetVar :: (Monad m, Language w, w ~ SameLang w) =>
             Ident ->
             TC w m (Maybe (Either (TypeT w) (TypeT (OtherLang w))))
tryGetVar x = TC $ asksM get where
  get tce = case tce =..= x of
    Just t  -> return (Just (Left t))
    Nothing -> case view x of
      Left _  -> case switchTC tce =..= x of
        Just t  -> return (Just (Right t))
        Nothing -> return Nothing
      Right _ -> return Nothing

getType :: (?loc :: Loc, Monad m) => QLid -> TC w m (TyInfo w)
getType  = getAny "Unbound type constructor"

getTypeTag :: (?loc :: Loc, Monad m) => String -> QLid -> TC w m TyTag
getTypeTag who n = do
  ti <- getType n
  case ti of
    TiAbs td     -> return td
    TiSyn _ _    -> terr $
      who ++ " expects an abstract or data type, but " ++
      "got type synonym: " ++ show n
    TiDat td _ _ -> return td
    TiExn td _   -> return td

getModule :: (?loc :: Loc, Monad m) => QUid -> TC w m (Scope w)
getModule  = getAny "Unbound module identifier"

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
      TiExn td _ -> do
        checkLength 0
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
      txtx  <- getVar x
      exnix <- either (findExnId x) (intoA . findExnId x) txtx
      let e' = exId x `setExnId` exnix
      case txtx of
        Left tx  -> return (tx, e' *:* tx)
        Right tx -> return (atype2ctype tx, e' *:* tx)
    ExStr s   -> return (TyCon (qlid "string") [] tdString, exStr s)
    ExInt z   -> return (TyCon (qlid "int") [] tdInt, exInt z)
    ExFloat f -> return (TyCon (qlid "float") [] tdFloat, exFloat f)
    ExCase e clauses -> do
      (t0, e') <- tc e
      (t1:ts, clauses') <- liftM unzip . forM clauses $ \(xi, ei) -> do
        (_, xi', ti, ei') <- withPatt t0 xi $ tc ei
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
            g' <- makeG (bnvar b : seen) bs' ts'
            return (g' =+= bnvar b =:= t)
          makeG _    _       _       = return empty
      g'  <- makeG [] bs tfs
      (tas, e's) <- unzip `liftM` mapM (withVars g' . tc . bnexpr) bs
      zipWithM_ (\tf ta -> do
                   tassert (ta <: tf) $
                      "Actual type " ++ show ta ++
                      " does not agree with declared type " ++
                      show tf ++ " in let rec")
                tfs tas
      (t2, e2') <- withVars g' (tc e2)
      let b's = zipWith3 (\b tf e' -> b { bntype = tf, bnexpr = e' })
                         bs tfs e's
      return (t2, exLetRec b's e2')
    ExLetDecl d e2 -> do
      withDecl d $ \d' -> do
        (t2, e2') <- tc e2
        return (t2, exLetDecl d' e2')
    ExPair e1 e2  -> do
      (t1, e1') <- tc e1
      (t2, e2') <- tc e2
      return (TyCon (qlid "*") [t1, t2] tdTuple, exPair e1' e2')
    ExAbs x t e     -> do
      t' <- tcType t
      (_, x', te, e') <- withPatt t' x $ tc e
      return (tyArrT t' te, exAbs x' t' e')
    ExApp _ _     -> do
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
    ExPack mt1 t2 e -> do
      t2'      <- tcType t2
      (te, e') <- tc e
      t1'      <- case mt1 of
        Just t1 -> tcType t1
        Nothing -> return (makeExType te t2')
      case t1' of
        TyQu Exists tv t11' -> do
          te' <- tapply (tyAll tv t11') t2'
          tassert (te <: te') $
            "Could not pack type " ++ show te ++
            " (abstracting " ++ show t2 ++
            ") to get " ++ show t1'
          return (t1', exPack (Just t1') t2' e')
        _ -> tgot "Pack[-]" t1' "ex(istential) type"
    ExCast e1 mt ta -> do
      (t1, e1') <- tc e1
      t'  <- maybe (return t1) tcType mt
      ta' <- intoA $ tcType ta
      tassgot (castableType ta')
        "cast (:>)" t' "function type"
      tassert (t1 <: t') $
        "Mismatch in cast: declared type " ++ show t' ++
        " doesn't match actual type " ++ show t1
      t1 \/? atype2ctype ta' |!
        "Mismatch in cast: C type " ++ show t1 ++
        " is incompatible with A contract " ++ show t'
      return (t', exCast e1' (Just t') ta')

-- Remove all instances of t2 from t1, replacing with
-- a new type variable 
makeExType :: Language w => TypeT w -> TypeT w -> TypeT w
makeExType t1 t2 = TyQu Exists tv $ everywhere (mkT erase) t1 where
  tv       = freshTyVar (TV (Lid "a") qual) (ftv [t1, t2])
  erase t' = if t' == t2 then TyVar tv else t'
  qual     = langCase t2 (const Qu) qualifier

tcExprA :: Monad m => Expr i A -> TC A m (TypeT A, ExprT A)
tcExprA = tc where
  tc :: Monad m => Expr i A -> TC A m (TypeT A, ExprT A)
  tc e0 = let ?loc = getLoc e0 in case view e0 of
    ExId x -> do
      txtx  <- getVar x
      exnix <- either (findExnId x) (intoC . findExnId x) txtx
      let e' = exId x `setExnId` exnix
      case txtx of
        Left tx  -> return (tx, e' *:* tx)
        Right tx -> return (ctype2atype tx, e' *:* tx)
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
    ExLetDecl d e2 -> do
      intoC $
        withDecl d $ \d' ->
          outofC $ do
            (t2, e2') <- tc e2
            return (t2, exLetDecl d' e2')
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
    ExPack mt1 t2 e -> do
      t2'      <- tcType t2
      (te, e') <- tc e
      t1'      <- case mt1 of
        Just t1 -> tcType t1
        Nothing -> return (makeExType te t2')
      case t1' of
        TyQu Exists tv t11' -> do
          te' <- tapply (tyAll tv t11') t2'
          tassert (te <: te') $
            "Could not pack type " ++ show te ++
            " (abstracting " ++ show t2 ++
            ") to get " ++ show t1'
          return (t1', exPack (Just t1') t2' e')
        _ -> tgot "Pack[-]" t1' "ex(istential) type"
    ExCast e1 mt ta -> do
      (t1, e1') <- tc e1
      t'  <- maybe (return t1) tcType mt
      ta' <- tcType ta
      tassgot (castableType ta')
        "cast (:>)" t' "function type"
      tassgot (t1 <: t')
        "cast (:>)" t1 (show t')
      t1 \/? ta' |!
        "Mismatch in cast: types " ++ show t1 ++
        " and " ++ show t' ++ " are incompatible"
      return (ta', exCast e1' (Just t') ta')

  checkSharing :: (Monad m, ?loc :: Loc) =>
                  String -> V A -> Expr i A -> TC A m ()
  checkSharing name g e =
    forM_ (toList g) $ \(x, tx) ->
      case x of
        Var x' ->
          tassert (qualifier tx <: usage (J [] x') e) $
            "Affine variable " ++ show x' ++ " : " ++
            show tx ++ " duplicated in " ++ name ++ " body"
        _ -> return ()

  isUnworthy e =
    anyM (\x -> do
           mtx <- tryGetVar (fmap Var x)
           return $ case mtx of
             Just (Left tx) -> qualifier tx == Qa
             _              -> False)
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
          TypeT w -> Patt -> TC w m (D, V w, Patt)
tcPatt t x0 = case x0 of
  PaWild     -> return (empty, empty, PaWild)
  PaVar x    -> return (empty, Var x =:= t, PaVar x)
  PaCon u mx _ -> do
    case t of
      TyCon name ts tag -> do
        tcon <- getType name
        case tcon of
          TiDat tag' params alts | tag == tag' -> do
            case alts =..= u of
              Nothing -> tgot "Pattern" t ("constructor " ++ show u)
              Just mt -> case (mt, mx) of
                (Nothing, Nothing) ->
                  return (empty, empty, PaCon u Nothing Nothing)
                (Just t1, Just x1) -> do
                  let t1' = tysubsts params ts t1
                  (dx1, gx1, x1') <- tcPatt t1' x1
                  return (dx1, gx1, PaCon u (Just x1') Nothing)
                _ -> tgot "Pattern" t "different arity"
          TiExn tag' alts | tag == tag' -> do
            case alts =..= u of
              Nothing       -> tgot "Pattern" t ("constructor " ++ show u)
              Just (mt, ei) -> case (mt, mx) of
                (Nothing, Nothing) ->
                  return (empty, empty, PaCon u Nothing (Just ei))
                (Just t1, Just x1) -> do
                  (dx1, gx1, x1') <- tcPatt t1 x1
                  return (dx1, gx1, PaCon u (Just x1') (Just ei))
                _ -> tgot "Pattern" t "different arity"
          _ ->
            terr $ "Pattern " ++ show x0 ++ " for type not in scope"
      _ -> tgot "Pattern" t ("constructor " ++ show u)
  PaPair x y -> do
    case t of
      TyCon (J [] (Lid "*")) [tx, ty] td | td == tdTuple
        -> do
          (dx, gx, x') <- tcPatt tx x
          (dy, gy, y') <- tcPatt ty y
          tassert (isEmpty (gx -|- gy)) $
            "Pattern " ++ show x0 ++ " binds variable twice"
          tassert (isEmpty (dx -|- dy)) $
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
    tassert (isEmpty (gx -|- gy)) $
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
          tassert (dx =..= tv == Nothing) $
            "Pattern " ++ show x0 ++ " binds " ++ show tv ++ " twice"
          return (dx =+= tv =:+= tv', gx, PaPack tv' x')
      _ -> tgot "Pattern" t "existential type"

withPatt :: (?loc :: Loc, Monad m, Language w) =>
            TypeT w -> Patt -> TC w m (TypeT w, e) ->
            TC w m (V w, Patt, TypeT w, e)
withPatt t x m = do
  (d, g, x') <- tcPatt t x
  (t', e')   <- withAny d $ withVars g $ m
  -- tcType t'
  let escapees = S.fromList (range d) `S.intersection` M.keysSet (ftv t')
  tassert (S.null escapees) $
    "Type variable escaped existential: " ++ show (S.findMin escapees)
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
withTyDec (TyDecC tl tds0) k0 =
  intoC $
    withTyDecCs False tds0 $ \tds0' ->
      outofC $
        k0 (TyDecC tl tds0')
withTyDec (TyDecA tl tds0) k0 = intoA $ do
  intoA $
    withTyDecAs False tds0 $ \tds0' ->
      outofA $
        k0 (TyDecA tl tds0')
withTyDec (TyDecT tds0) k0 =
  intoA $
    withTyDecAs True tds0 $ \tds0' ->
      outofA $
        k0 (TyDecT tds0')

withTyDecCs :: (?loc :: Loc, Monad m) =>
               Bool -> [TyDecC] -> ([TyDecC] -> TC C m a) -> TC C m a
withTyDecCs trans tds0 k0 = do
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
    mapCont (withTyDecC trans) (atds ++ stds ++ dtds) $
      k0
  where
    withStub (TdDatC name params _) k = do
      index <- newIndex
      let tag = TyTag {
                  ttId    = index,
                  ttArity = map (const Invariant) params,
                  ttQual  = minBound,
                  ttTrans = trans
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

withTyDecC :: (?loc :: Loc, Monad m) =>
              Bool -> TyDecC -> (TyDecC -> TC C m a) -> TC C m a
withTyDecC trans (TdAbsC name params) k = do
  index <- newIndex
  withTypesTransC trans
      (name =:= TiAbs TyTag {
         ttId    = index,
         ttArity = map (const Invariant) params,
         ttQual  = minBound,
         ttTrans = trans
       })
    (k $ TdAbsC name params)
withTyDecC trans (TdSynC name params rhs) k = do
  t' <- withTVs params $ \params' -> TiSyn params' `liftM` tcType rhs
  withTypesTransC trans (name =:= t')
    (k $ TdSynC name params rhs)
withTyDecC trans (TdDatC name params alts) k = do
  TiDat tag _ _ <- getType (J [] name)
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
  withTypesTransC trans (name =:= TiDat tag params' (fromList alts')) $
    withVarsTransC trans (alts2env name params' tag alts') $
      (k $ TdDatC name params alts)

-- Add the given types to the current language tenv, and maybe the
-- other language tenv.
withTypesTransC :: Monad m => Bool -> T C -> TC C m a -> TC C m a
withTypesTransC False te k = withTypes te k
withTypesTransC True  te k =
  withTypes te $
    intoA $
      withTypes (fmap cinfo2ainfo te) $
        intoC $
          k
  where
    cinfo2ainfo (TiAbs tag)
      = TiAbs tag
    cinfo2ainfo (TiSyn tvs t)
      = TiSyn tvs (ctype2atype' tvs t)
    cinfo2ainfo (TiDat tag tvs rhs)
      = TiDat tag tvs (fmap (fmap (ctype2atype' tvs)) rhs)
    cinfo2ainfo (TiExn tag rhs)
      = TiExn tag (fmap (first (fmap ctype2atype)) rhs)
    ctype2atype' tvs = ctype2atype . tysubsts tvs (map (tyA . TyVar) tvs) 

-- Add the given types to the current language tenv, and maybe the
-- other language tenv.
withVarsTransC :: Monad m => Bool -> V C -> TC C m a -> TC C m a
withVarsTransC False te k = withVars te k
withVarsTransC True  te k =
  withVars te $
    intoA $
      withVars (fmap ctype2atype te) $
        intoC $
          k

withTyDecAs :: (?loc :: Loc, Monad m) =>
               Bool -> [TyDecA] -> ([TyDecA] -> TC A m a) -> TC A m a
withTyDecAs trans tds0 k0 = do
  tassert (unique (map tdaName tds0)) $
    "Duplicate type(s) in recursive type declaration"
  let (atds, stds0, dtds) = foldr partition ([], [], []) tds0
  stds <- topSort getEdge stds0
  mapCont_ withStub dtds $
    let loop =
          mapCont (withTyDecA trans) (atds ++ stds ++ dtds) $
            \tds'changed ->
              if any snd tds'changed
                then loop
                else outofA $ k0 (map fst tds'changed)
     in loop
  where
    withStub (TdDatA name params _) k = do
      index <- newIndex
      let tag = TyTag {
                  ttId    = index,
                  ttArity = map (const Omnivariant) params,
                  ttQual  = minBound,
                  ttTrans = trans
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

-- withTyDecA types an A type declaration, but in addition to
-- return (in CPS) a declaration, it returns a boolean that indicates
-- whether the type metadata has changed, which allows for iterating
-- to a fixpoint.
withTyDecA :: (?loc :: Loc, Monad m) =>
              Bool -> TyDecA -> ((TyDecA, Bool) -> TC A m a) -> TC A m a
withTyDecA trans (TdAbsA name params variances quals) k = do
  index  <- newIndex
  quals' <- indexQuals name params quals
  withTypesTransA trans
      (name =:= TiAbs TyTag {
         ttId    = index,
         ttArity = variances,
         ttQual  = quals',
         ttTrans = trans
       })
    (k (TdAbsA name params variances quals, False))
withTyDecA trans (TdSynA name params rhs) k = do
  t' <- withTVs params $ \params' -> TiSyn params' `liftM` tcType rhs
  withTypesTransA trans (name =:= t')
    (k (TdSynA name params rhs, False))
withTyDecA trans (TdDatA name params alts) k = do
  TiDat tag _ _ <- getType (J [] name)
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
  withTypesTransA trans (name =:= TiDat tag' params' (fromList alts')) $
    withVarsTransA trans (alts2env name params' tag' alts') $
      (k (TdDatA name params alts, changed))

-- Add the given types to the current language tenv, and maybe the
-- other language tenv.
withTypesTransA :: Monad m => Bool -> T A -> TC A m a -> TC A m a
withTypesTransA False te k = withTypes te k
withTypesTransA True  te k =
  withTypes te $
    intoC $
      withTypes (fmap ainfo2cinfo te) $
        intoA $
          k
  where
    ainfo2cinfo (TiAbs tag)
      = TiAbs tag
    ainfo2cinfo (TiSyn tvs t)
      = TiSyn tvs (atype2ctype' tvs t)
    ainfo2cinfo (TiDat tag tvs rhs)
      = TiDat tag tvs (fmap (fmap (atype2ctype' tvs)) rhs)
    ainfo2cinfo (TiExn tag rhs)
      = TiExn tag (fmap (first (fmap atype2ctype)) rhs)
    atype2ctype' tvs = atype2ctype . tysubsts tvs (map (tyC . TyVar) tvs) 

-- Add the given types to the current language tenv, and maybe the
-- other language tenv.
withVarsTransA :: Monad m => Bool -> V A -> TC A m a -> TC A m a
withVarsTransA False te k = withVars te k
withVarsTransA True  te k =
  withVars te $
    intoC $
      withVars (fmap atype2ctype te) $
        intoA $
          k

unique :: Ord a => [a] -> Bool
unique  = loop S.empty where
  loop _    []     = True
  loop seen (x:xs) = x `S.notMember` seen && loop (S.insert x seen) xs

alts2env :: Lid -> [TyVar] -> TyTag -> [(Uid, Maybe (TypeT w))] -> V w
alts2env name params tag = fromList . map each where
  each (uid, Nothing) = (Con uid, alls result)
  each (uid, Just t)  = (Con uid, alls (t `tyArrT` result))
  alls t              = foldr tyAll t params
  result              = TyCon (J [] name) (map TyVar params) tag

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

tyConsOfType :: Bool -> Type i w -> S.Set Lid
tyConsOfType here (TyCon n ts _) =
  (case (here, n) of
    (True, J [] lid) -> S.singleton lid
    _                -> S.empty)
  `S.union` S.unions (map (tyConsOfType here) ts)
tyConsOfType _    (TyVar _)        = S.empty
tyConsOfType here (TyQu _ _ ty)    = tyConsOfType here ty
tyConsOfType here (TyMu _ ty)      = tyConsOfType here ty
tyConsOfType here (TyC ty)         = tyConsOfType (not here) ty
tyConsOfType here (TyA ty)         = tyConsOfType (not here) ty

-- END type decl checking

withLet :: (?loc :: Loc, Monad m) =>
           Let i -> (LetT -> TC C m a) -> TC C m a
withLet (LtC tl x mt e) k = intoC $ do
  (te, e') <- tcExprC e
  t' <- case mt of
    Just t  -> do
      t' <- tcType t
      tassert (te == t') $
        "Declared type for function " ++ show x ++ " : " ++ show t ++
        " doesn't match actual type " ++ show te
      return t'
    Nothing -> return te
  withVars (Var x =:= t') .
    k $ LtC tl x (Just t') e'
withLet (LtA tl x mt e) k = intoA $ do
  (te, e') <- tcExprA e
  t' <- case mt of
    Just t  -> do
      t' <- tcType t
      tassert (qualifier t' == Qu) $
        "Declared type of function " ++ show x ++ " is not unlimited"
      tassert (te <: t') $
        "Declared type for function " ++ show x ++ " : " ++ show t' ++
        " is not subsumed by actual type " ++ show te
      return t'
    Nothing -> do
      tassert (qualifier te == Qu) $
        "Type of top-level function " ++ show x ++ " is not unlimited"
      return te
  withVars (Var x =:= t') .
    outofA .
      k $ LtA tl x (Just t') e'
withLet (LtInt tl x t y) k = do
  tyty <- getVar (fmap Var y)
  let ty = either id atype2ctype tyty
  t'   <- intoA $ tcType t
  tassert (ty == atype2ctype t') $
    "Declared type of interface " ++ show x ++ " :> " ++
    show t' ++ " not compatible with RHS type: " ++ show ty
  intoA .
    withVars (Var x =:= t') .
      outofA .
        k $ LtInt tl x t' y

withOpen :: (?loc :: Loc, Monad m) =>
            ModExp i -> (ModExpT -> TC C m a) -> TC C m a
withOpen b k = do
  (b', scope) <- tcModExp b
  let [scope'] = requalifyTypes [] [scope]
  withAny scope' $ k b'

withLocal :: (?loc :: Loc, Monad m) =>
             [Decl i] -> [Decl i] ->
             ([DeclT] -> [DeclT] -> TC C m a) -> TC C m a
withLocal ds0 ds1 k = do
  (scope, ds0', ds1') <-
    pushScope $
      withDecls ds0 $ \ds0' ->
        pushScope $
          withDecls ds1 $ \ds1' -> do
            scope <- askScope
            return (scope, ds0', ds1')
  pushScope .
    withAny scope .
      squishScope $
        k ds0' ds1'

withExn :: (?loc :: Loc, Monad m) =>
           ExnDec -> (ExnDec -> TC C m a) -> TC C m a
withExn d0 k0 = case d0 of
    ExnC _ n mt -> do
      index <- newIndex
      withExnId n mt C index $
        k0 d0
    ExnA _ n mt -> do
      index <- newIndex
      withExnId n mt A index $
        k0 d0

withExnId :: (?loc :: Loc, Monad m, Language w) =>
             Uid -> Maybe (Type i w) -> LangRep w -> Integer ->
             TC C m a -> TC C m a
withExnId n mt lang0 index k0 = case lang0 of
    C -> do
      t' <- gmapM tcType mt
      add t' LC .
        intoA .
          add (fmap ctype2atype t') LC .
            intoC $
              k0
    A -> intoA $ do
      t' <- gmapM tcType mt
      add t' LA .
        intoC $
          k0
 where
   add t lang k = do
     ti <- getType (qlid "exn")
     let env' = n =:= (t, ExnId index n lang)
     ti' <- case ti of
       TiExn tag env     -> return $ TiExn tag (env =+= env')
       _                 -> terr $ "Cannot extend exn type because " ++
                                   "exn is shadowed"
     withTypes (Lid "exn" =:= ti') .
       withVars (Con n =:= maybe tyExnT (`tyArrT` tyExnT) t) $
         k

findExnId :: (?loc::Loc, Monad m) =>
             Ident -> TypeT w -> TC w m (Maybe ExnId)
findExnId ident t = case view ident of
    Right (J [] uid) -> case t of
      TyCon _ [_, TyCon _ _ td'] td
        | td == tdArr && td' == tdExn -> getIdOf uid
      TyCon _ [] td
        | td == tdExn                 -> getIdOf uid
      _                               -> return Nothing
    _                                 -> return Nothing
  where
    getIdOf n = do
      ti <- getType (qlid "exn")
      case ti of
        TiExn _ alts -> return (fmap snd (alts =..= n))
        _            -> return Nothing

withMod :: (?loc :: Loc, Monad m) =>
           Uid -> ModExp i -> (ModExpT -> TC C m a) -> TC C m a
withMod x b k = do
  (b', scope) <- tcModExp b
  let [scope'] = requalifyTypes [x] [scope]
  withAny (x =:= scope') $ k b'

hideInvisible :: forall m. (Monad m) =>
                 Scope C -> TC C m (Scope C)
hideInvisible (PEnv me both) = do
  both' <- withAny both $ repairBoth both
  withAny both' $ do
    ((), me') <- mapAccumM
                   (\scope acc -> do
                      scope' <- hideInvisible scope
                      return (acc, scope'))
                   () me
    return (PEnv me' both')

  where
    repairBoth :: Both C -> TC C m (Both C)
    repairBoth (Both level other) = do
      level' <- everywhereM (mkM repair) level
      other' <- intoA $ everywhereM (mkM repair) other
      return (Both level' other')

    repair :: forall w. Monad m => TypeT w -> TC w m (TypeT w)
    repair t@(TyCon { tycon = name, tyinfo = tag }) = do
      mtd <- tryGetAny name
      return $ case mtd of
        Just (TiAbs tag')
          | tag' == tag  -> t
        Just (TiDat tag' _ _)
          | tag' == tag  -> t
        Just (TiSyn _ _) -> t
        Just (TiExn tag' _)
          | tag' == tag  -> t
        _                -> t { tycon = hide (tyinfo t) name }
    repair t = return t

    hide :: TyTag -> QLid -> QLid
    hide _   name@(J (Uid "?" : _) _) = name
    hide tag (J qs (Lid k)) =
      J (Uid "?":qs) (Lid (k ++ ':' : show (ttId tag)))

requalifyTypes :: [Uid] -> E C -> E C
requalifyTypes uids env = map (fmap repairBoth) env where
  repairBoth :: Both C -> Both C
  repairBoth (Both level other) =
    (Both (everywhere (mkT (repair :: TypeT C -> TypeT C)) level)
          (everywhere (mkT (repair :: TypeT A -> TypeT A)) other))

  repair :: TypeT w -> TypeT w
  repair t@(TyCon { }) = case tyConsInThisEnv -.- ttId (tyinfo t) of
    Nothing   -> t
    Just name -> t { tycon = name }
  repair t = t

  tyConsInThisEnv :: Env Integer QLid
  tyConsInThisEnv  = uids <...> foldr addToScopeMap empty env

  addToScopeMap :: Scope w -> Env Integer QLid -> Env Integer QLid
  addToScopeMap (PEnv ms (Both level other)) acc = 
    foldr (Env.unionWith chooseQLid) acc
      (makeLevelMap level :
       makeLevelMap other :
       [ uid <..> addToScopeMap menv empty
       | (uid, menv) <- toList ms ])

  makeLevelMap (Level _ ts) =
    fromList [ (ttId tag, J [] lid)
             | (lid, info) <- toList ts,
               tag <- tagOfTyInfo info ]

  tagOfTyInfo (TiAbs tag)     = [tag]
  tagOfTyInfo (TiSyn _ _)     = []
  tagOfTyInfo (TiDat tag _ _) = [tag]
  tagOfTyInfo (TiExn tag _)   = [tag]

  chooseQLid :: QLid -> QLid -> QLid
  chooseQLid q1@(J p1 _) q2@(J p2 _)
    | length p1 < length p2 = q1
    | otherwise             = q2

  (<..>) :: Functor f => p -> f (Path p k) -> f (Path p k)
  (<..>)  = fmap . (<.>)

  (<...>) :: Functor f => [p] -> f (Path p k) -> f (Path p k)
  (<...>) = flip $ foldr (<..>)

tcModExp :: (?loc :: Loc, Monad m) =>
             ModExp i -> TC C m (ModExpT, Scope C)
tcModExp (MeStrC tl ds) =
  pushScope $
    withDecls ds $ \ds' -> do
      scope <- askScope
      return (MeStrC tl ds', scope)
tcModExp (MeStrA tl ds) =
  pushScope $
    withDecls ds $ \ds' -> do
      scope <- askScope
      return (MeStrA tl ds', scope)
tcModExp (MeName n)   = do
  scope <- getModule n
  return (MeName n, scope)

withDecl :: Monad m =>
            Decl i -> (DeclT -> TC C m a) -> TC C m a
withDecl decl k =
  let ?loc = getLoc decl in
    case decl of
      DcLet loc m     ->  withLet m (k . DcLet loc)
      DcTyp loc td    ->  withTyDec td (k . DcTyp loc)
      DcAbs loc at ds ->  withAbsTy at ds (k .  DcAbs loc at)
      DcMod loc x b   ->  withMod x b (k . DcMod loc x)
      DcOpn loc b     ->  withOpen b (k . DcOpn loc)
      DcLoc loc d0 d1 ->  withLocal d0 d1 ((.) k . DcLoc loc)
      DcExn loc e     ->  withExn e (k . DcExn loc)

withDecls :: Monad m =>
             [Decl i] -> ([DeclT] -> TC C m a) -> TC C m a
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
        tag <- getTypeTag "abstract-with-end" (J [] name)
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
      withDecls ds $ \ds' ->
        intoA $ do
          mapCont absDecl atds $ \tags' ->
            outofA $ k0 (foldr replaceTyTags ds' tags')
    where
      absDecl (arity, quals, TdDatA name params _) k = do
        tag     <- getTypeTag "abstract-with-end" (J [] name)
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

tcDecls :: Monad m => Bool -> S -> [Decl i] -> m (S, NewDefs, [DeclT])
tcDecls interactive gg ds =
  runTC gg $
    pushScope $
      withDecls ds $ \ds' -> do
        new <- askNewDefs
        squishScope $ do
          gg' <- saveTC interactive
          return (gg', new, ds')

-- Info about new defs for printing in the repl:
data NewDefs = NewDefs {
                 newCTypes  :: T C,
                 newCValues :: V C,
                 newATypes  :: T A,
                 newAValues :: V A,
                 newModules :: [Uid]
               }
  deriving Show

emptyNewDefs :: NewDefs
emptyNewDefs  = (NewDefs empty empty empty empty [])

askNewDefs :: (Language w, Monad m) => TC w m NewDefs
askNewDefs  = intoC $ do
  scope <- askScope
  PEnv me (Both clevel alevel) <- hideInvisible scope
  return NewDefs {
           newCTypes  = tlevel clevel,
           newCValues = vlevel clevel,
           newATypes  = tlevel alevel,
           newAValues = vlevel alevel,
           newModules = domain me
         }

-- For adding types of primitives to the environment
addVal :: (Ident :>: k, Language w, Monad m) =>
          S -> k -> Type i w -> m S
addVal gg x t = runTC gg $ outofC $ do
  let ?loc = bogus
  t' <- tcType t
  withAny (x' =:= t') $ saveTC False
    where x' :: Ident = liftKey x

addType :: S -> Lid -> TyTag -> S
addType gg n td =
  let level :: Level w
      level  = Level empty (n =:= TiAbs td)
      both  :: Both C
      both   = Both level level in
    gg { cEnv = cEnv gg =+= both }

addExn :: (Language w, Monad m) =>
          S -> Uid -> Maybe (Type i w) -> LangRep w -> Integer -> m S
addExn gg n mt lang ix =
  runTC gg .
    withExnId n mt lang ix $
      saveTC False
  where ?loc = bogus

addMod :: (Monad m) => S -> Uid -> (S -> m S) -> m S
addMod gg0 x k = do
  let env = cEnv gg0
      gg1 = gg0 { cEnv = genEmpty : env }
  gg2 <- k gg1
  let scope:_ = cEnv gg2
      gg3    = S { currIx = currIx gg2,
                   cEnv   = env =+= x =:= scope }
  return gg3

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
env0  = S e0 0 where
  e0 :: E C
  e0  = genEmpty =+= both0 where
    both0  :: Both C
    both0   = Both level0 level0
    level0 :: Level w
    level0  = Level venv0 tenv0
    venv0  :: V w
    venv0   = Con (Uid "()")    -:- tyUnitT
    tenv0  :: T w
    tenv0   = Lid "unit" -:- TiDat tdUnit [] (
                Uid "()"    -:- Nothing
              ) -+-
              Lid "exn"  -:- TiExn tdExn empty

tyInfoToDec :: Language w => Lid -> TyInfo w -> TyDec
tyInfoToDec n ti0 = langCase ti0
  (\ti -> TyDecC True . return $ case ti of
     TiSyn ps rhs    -> TdSynC n ps (removeTyTags rhs)
     TiDat _ ps alts -> TdDatC n ps [ (uid, fmap removeTyTags mt)
                                          | (uid, mt) <- toList alts ]
     TiAbs tag       -> TdAbsC n (zipWith const tyvars (ttArity tag))
     TiExn _ alts    -> TdDatC (Lid "exn") []
                               [ (uid, fmap removeTyTags mt)
                               | (uid, (mt, _)) <- toList alts ])
  (\ti -> TyDecA True . return $ case ti of
     TiSyn ps rhs    -> TdSynA n ps (removeTyTags rhs)
     TiDat _ ps alts -> TdDatA n ps [ (uid, fmap removeTyTags mt)
                                          | (uid, mt) <- toList alts ]
     TiAbs tag       -> TdAbsA n (zipWith const tyvars (ttArity tag))
                               (ttArity tag)
                               (qsToList tyvars (ttQual tag))
     TiExn _ alts    -> TdDatA (Lid "exn") []
                               [ (uid, fmap removeTyTags mt)
                               | (uid, (mt, _)) <- toList alts ])
  where
    tyvars   = map (flip TV Qu . Lid) alphabet
    alphabet = map return ['a' .. 'z'] ++
               [ x ++ [y] | x <- alphabet, y <- ['a' .. 'z'] ]
