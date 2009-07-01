module Statics (
  GG(..), tcProg, tcMods, tcTyDec, tcType
) where

import Util
import Syntax
import Env as Env
import Ppr ()

import Control.Monad
import Data.List (elemIndex)
import qualified Data.Map as M
import qualified Data.Set as S

-- Get the usage (sharing) of a variable in an expression:
usage :: Var -> Expr i A -> Q
usage x e = case M.lookup x (fv e) of
  Just u | u > 1 -> Qu
  _              -> Qa

-- Type environments
type D   = S.Set TyVar
type I   = Env String TInfo
type G w = Env Var (TypeI w)
data GG  = GG {
             ggC :: G C,
             ggA :: G A,
             ggI :: I,
             ggN :: Integer
           }

-- Raise a type error
terr :: Monad m => String -> m a
terr s = fail $ "Type error: " ++ s

-- A type checking "assertion" raises a type error if the
-- asserted condition is false.
tassert :: Monad m => Bool -> String -> m ()
tassert True  _ = return ()
tassert False s = terr s

-- A common form of type error
tgot :: Monad m => String -> Type i w -> String -> m a
tgot who got expected = terr $ who ++ " got " ++ show got ++
                               " where " ++ expected ++ " expected"

-- Run a partial computation, and if it fails, substitute
-- the given failure message.
(|!) :: Monad m => Maybe a -> String -> m a
m |! s = case m of
  Just r  -> return r
  _       -> fail s
infix 1 |!

-- Check a type, at top-level (so we assume no ftvs)
tcType :: Monad m => I -> Type i w -> m (TypeI w)
tcType i = tcOpenType i S.empty

-- Check type for closed-ness and and defined-ness, and add info
tcOpenType :: Monad m => I -> D -> Type i w -> m (TypeI w)
tcOpenType i d0 = tc (d0, S.empty) where
  tc                     :: Monad m =>
                            (D, D) -> Type i w -> m (TypeI w)
  tc (d, _ ) (TyVar tv)   = do
    tassert (S.member tv d) $
      "Free type variable: " ++ show tv
    return (TyVar tv)
  tc (d, d') (TyCon n ts _) = case i =.= n of
    Nothing -> terr $ "Undefined type constructor: " ++ n
    Just ti -> do
      tassert (length ts == length (tiArity ti)) $
        "Type constructor " ++ n ++ " applied to " ++
        show (length ts) ++ " arguments where " ++
        show (length (tiArity ti)) ++ " expected"
      ts' <- mapM (tc (d, d')) ts
      return (TyCon n ts' ti)
  tc (d, d') (TyAll tv t) = TyAll tv `liftM` tc (S.insert tv d, d') t
  tc (d, d') (TyMu tv t)  = TyMu  tv `liftM` tc (S.insert tv d, d') t
  tc (d, d') (TyC t)      = TyC `liftM` tc (d', d) t
  tc (d, d') (TyA t)      = TyA `liftM` tc (d', d) t

-- Type check an expression
tcExprC :: Monad m => I -> G C -> Expr i C -> m (TypeI C, ExprI C)
tcExprC i = tc S.empty where
  tc :: Monad m => D -> G C -> Expr i C -> m (TypeI C, ExprI C)
  tc d g e0 = case expr' e0 of
    ExCon "()"    -> return (TyCon "unit" [] tiUnit, exCon "()")
    ExCon s
      | s `elem` constants -> terr $ "Constant must be applied: " ++ s
      | otherwise          -> terr $ "Unrecognized constant: " ++ s
    ExStr s       -> return (TyCon "string" [] tiString, exStr s)
    ExInt z       -> return (TyCon "int" [] tiInt, exInt z)
    ExIf e1 e2 e3 -> do
      (t1, e1') <- tc d g e1
      tassert (tyinfo t1 == tiBool) $
        "If condition was " ++ show t1 ++ " where bool expected"
      (t2, e2') <- tc d g e2
      (t3, e3') <- tc d g e3
      tassert (t2 == t3) $
        "Mismatch in if: " ++ show t2 ++ " /= " ++ show t3
      return (t2, exIf e1' e2' e3')
    ExCase e1 (xl, el) (xr, er) -> do
      (t1, e1') <- tc d g e1
      case t1 of
        TyCon "either" [txl, txr] ti | ti == tiEither -> do
          (tl, el') <- tc d (g =+= xl =:= txl) el
          (tr, er') <- tc d (g =+= xr =:= txr) er
          tassert (tl == tr) $
            "Mismatch in match: " ++ show tl ++ " /= " ++ show tr
          return (tl, exCase e1' (xl, el') (xr, er'))
        _ -> tgot "match" t1 "('a, 'b) either"
    ExLet x e1 e2 -> do
      (t1, e1') <- tc d g e1
      (t2, e2') <- tc d (g =+= x =:= t1) e2
      return (t2, exLet x e1' e2')
    ExLetRec bs e2 -> do
      tfs <- mapM (tcOpenType i d . bntype) bs
      let makeG seen (b:bs') (t:ts') = do
            tassert (bnvar b `notElem` seen) $
              "Duplicate binding in let rec: " ++ show (bnvar b)
            tassert (syntacticValue (bnexpr b)) $
              "Not a syntactic value in let rec: " ++ show (bnexpr b)
            g' <- makeG (bnvar b : seen) bs' ts'
            return (g' =+= bnvar b =:= t)
          makeG _    _       _       = return g
      g'  <- makeG [] bs tfs
      (tas, e's) <- unzip `liftM` mapM (tc d g' . bnexpr) bs
      zipWithM_ (\tf ta -> do
                   tassert (tf == ta) $
                      "Actual type " ++ show ta ++
                      " does not agree with declared type " ++
                      show tf ++ " in let rec")
                tfs tas
      (t2, e2') <- tc d g' e2
      let b's = zipWith3 (\b tf e' -> b { bntype = tf, bnexpr = e' })
                         bs tfs e's
      return (t2, exLetRec b's e2')
    ExVar x       -> do
      tx <- g =.= x |!
        "Unbound variable: " ++ show x
      return (tx, exVar x)
    ExPair e1 e2  -> do
      (t1, e1') <- tc d g e1
      (t2, e2') <- tc d g e2
      return (TyCon "*" [t1, t2] tiTuple, exPair e1' e2')
    ExLetPair (x, y) e1 e2 -> do
      tassert (x /= y) $ "Repeated variable in let pair: " ++ show x
      (t1, e1') <- tc d g e1
      case t1 of
        TyCon "*" [tx, ty] ti | ti == tiTuple
          -> do
               (t2, e2') <- tc d (g =+= x =:= tx =+= y =:= ty) e2
               return (t2, exLetPair (x, y) e1' e2')
        _ -> tgot "let" t1 "pair type"
    ExAbs x t e     -> do
      t' <- tcOpenType i d t
      (te, e') <- tc d (g =+= x =:= t') e
      return (TyCon "->" [t', te] tiArr, exAbs x t' e')
    ExApp e1 e2   -> case expr' e1 of
      ExCon s       -> do
        (t2, e2') <- tc d g e2
        t         <- tcCon s t2
        return (t, exApp (exCon s) e2')
      _             -> do
        (t1, e1') <- tc d g e1
        (t2, e2') <- tc d g e2
        let (tvs, body) = unfoldTyAll t1
        case body of
          TyCon "->" [ta, tr] ti | ti == tiArr -> do
            subst <- tryUnify tvs ta t2
            let ta' = subst ta
                tr' = subst tr
            tassert (ta' == t2) $
              "Mismatch in application: got " ++
              show t2 ++ " where " ++ show ta' ++ " expected"
            return (tr', exApp e1' e2')
          _ -> terr $ "Mismatch in application: got " ++
                       show t1 ++ " where function type expected"
    ExTAbs tv e   -> do
      (t, e') <- tc (S.insert tv d) g e
      return (TyAll tv t, exTAbs tv e')
    ExTApp e1 t2  -> do
      (t1, e1') <- tc d g e1
      t2'       <- tcOpenType i d t2
      case t1 of
        TyAll tv t1' -> return (tysubst tv t2' t1', exTApp e1' t2')
        _            -> tgot "type application" t1 "(for)all type"
    ExSeq e1 e2   -> do
      (_,  e1') <- tc d g e1
      (t2, e2') <- tc d g e2
      return (t2, exSeq e1' e2')
    ExCast e1 t ta -> do
      t'  <- tcOpenType i d t
      ta' <- tcOpenType i S.empty ta
      case t' of
        TyCon _ [_, _] ti | ti `elem` funtypes -> return ()
        _ -> tgot "cast (:>)" t' "function type"
      (t1, e1') <- tc d g e1
      tassert (t1 == t') $
        "Mismatch in cast: declared type " ++ show t' ++
        " doesn't match actual type " ++ show t1
      tassert (t1 == atype2ctype ta') $
        "Mismatch in cast: C type " ++ show t1 ++
        " is incompatible with A contract " ++ show t'
      return (t', exCast e1' t' ta')

tcExprA :: Monad m => I -> G A -> Expr i A -> m (TypeI A, ExprI A)
tcExprA i = tc S.empty where
  tc d g e0 = case expr' e0 of
    ExCon "()"    -> return (TyCon "unit" [] tiUnit, exCon "()")
    ExCon s
      | s `elem` constants -> terr $ "Constant must be applied: " ++ s
      | otherwise          -> terr $ "Unrecognized constant: " ++ s
    ExStr s       -> return (TyCon "string" [] tiString, exStr s)
    ExInt z       -> return (TyCon "int" [] tiInt, exInt z)
    ExIf e1 e2 e3 -> do
      (t1, e1') <- tc d g e1
      tassert (tyinfo t1 == tiBool) $
        "If condition was " ++ show t1 ++ " where bool expected"
      (t2, e2') <- tc d g e2
      (t3, e3') <- tc d g e3
      t <- t2 \/? t3
        |! "Mismatch in if: " ++ show t2 ++ " and " ++ show t3
      return (t, exIf e1' e2' e3')
    ExCase e1 (xl, el) (xr, er) -> do
      (t1, e1') <- tc d g e1
      case t1 of
        TyCon "either" [txl, txr] ti | ti == tiEither -> do
          tassert (qualifier txl <: usage xl el) $
            "Affine variable " ++ show xl ++ " : " ++
            show txl ++ " duplicated in match body"
          tassert (qualifier txr <: usage xr er) $
            "Affine variable " ++ show xr ++ " : " ++
            show txr ++ " duplicated in match body"
          (tl, el') <- tc d (g =+= xl =:= txl) el
          (tr, er') <- tc d (g =+= xr =:= txr) er
          t <- tl \/? tr
            |! "Mismatch in match: " ++ show tl ++ " and " ++ show tr
          return (t, exCase e1' (xl, el') (xr, er'))
        _ -> tgot "match" t1 "('a, 'b) either"
    ExLet x e1 e2 -> do
      (t1, e1') <- tc d g e1
      tassert (qualifier t1 <: usage x e2) $
        "Affine variable " ++ show x ++ " : " ++
        show t1 ++ " duplicated in let body"
      (t2, e2') <- tc d (g =+= x =:= t1) e2
      return (t2, exLet x e1' e2')
    ExLetRec bs e2 -> do
      tfs <- mapM (tcOpenType i d . bntype) bs
      let makeG seen (b:bs') (t:ts') = do
            tassert (bnvar b `notElem` seen) $
              "Duplicate binding in let rec: " ++ show (bnvar b)
            tassert (syntacticValue (bnexpr b)) $
              "Not a syntactic value in let rec: " ++ show (bnexpr b)
            tassert (qualifier t <: Qu) $
              "Affine type in let rec binding: " ++ show t
            g' <- makeG (bnvar b : seen) bs' ts'
            return (g' =+= bnvar b =:= t)
          makeG _    _       _       = return g
      g'  <- makeG [] bs tfs
      (tas, e's) <- unzip `liftM` mapM (tc d g' . bnexpr) bs
      zipWithM_ (\tf ta ->
                   tassert (ta <: tf) $
                      "Actual type " ++ show ta ++
                      " does not agree with declared type " ++
                      show tf ++ " in let rec")
                tfs tas
      (t2, e2') <- tc d g' e2
      let b's = zipWith3 (\b tf e' -> b { bntype = tf, bnexpr = e' })
                         bs tfs e's
      return (t2, exLetRec b's e2')
    ExVar x       -> do
      t <- g =.= x |!
        "Unbound variable: " ++ show x
      return (t, exVar x)
    ExPair e1 e2  -> do
      (t1, e1') <- tc d g e1
      (t2, e2') <- tc d g e2
      return (TyCon "*" [t1, t2] tiTuple, exPair e1' e2')
    ExLetPair (x, y) e1 e2 -> do
      tassert (x /= y) $
        "Repeated variable in let pair: " ++ show x
      (t1, e1') <- tc d g e1
      case t1 of
        TyCon "*" [tx, ty] ti | ti == tiTuple -> do
          tassert (qualifier tx <: usage x e2) $
            "Affine variable " ++ show x ++ " : " ++
            show tx ++ " duplicated in let body"
          tassert (qualifier ty <: usage y e2) $
            "Affine variable " ++ show y ++ " : " ++
            show ty ++ " duplicated in let body"
          (t2, e2') <- tc d (g =+= x =:= tx =+= y =:= ty) e2
          return (t2, exLetPair (x, y) e1' e2')
        _ -> terr $ "Let pair got non-pair type: " ++ show t1
    ExAbs x t e     -> do
      t' <- tcOpenType i d t
      tassert (qualifier t' <: usage x e) $
        "Affine variable " ++ show x ++ " : " ++
        show t' ++ " duplicated in lambda body"
      (te, e') <- tc d (g =+= x =:= t') e
      if unworthy g e0
        then return (TyCon "-o" [t', te] tiLol, exAbs x t' e')
        else return (TyCon "->" [t', te] tiArr, exAbs x t' e')
    ExApp e1 e2   -> case expr' e1 of
      ExCon s       -> do
        (t2, e2') <- tc d g e2
        t         <- tcCon s t2
        return (t, exApp (exCon s) e2')
      _             -> do
        (t1, e1') <- tc d g e1
        (t2, e2') <- tc d g e2
        let (tvs, body) = unfoldTyAll t1
        case body of
          TyCon _ [ta, tr] ti
              | ti `elem` funtypes -> do
            subst <- tryUnify tvs ta t2
            let ta' = subst ta
                tr' = subst tr
            tassert (t2 <: ta') $
              "Mismatch in application: got " ++
              show t2 ++ " where " ++ show ta' ++ " expected"
            return (tr', exApp e1' e2')
          _ -> terr $ "Mismatch in application: got " ++
                       show t1 ++ " where function type expected"
    ExTAbs tv e   -> do
      (t, e') <- tc (S.insert tv d) g e
      return (TyAll tv t, exTAbs tv e')
    ExTApp e1 t2  -> do
      t2'       <- tcOpenType i d t2
      (t1, e1') <- tc d g e1
      case t1 of
        TyAll tv t1' -> do
          tassert (qualifier t2' <: tvqual tv) $
            "Mismatch in type application: got " ++
            show (qualifier t2') ++
            " type for type variable " ++ show tv
          return (tysubst tv t2' t1', exTApp e1' t2')
        _            -> tgot "type application" t1 "(for)all type"
    ExSeq e1 e2   -> do
      (_,  e1') <- tc d g e1
      (t2, e2') <- tc d g e2
      return (t2, exSeq e1' e2')
    ExCast e1 t ta -> do
      t'  <- tcOpenType i d t
      ta' <- tcOpenType i d ta
      case t' of
        TyCon _ [_, _] ti | ti `elem` funtypes -> return ()
        _ -> terr $ "Cast requires a function type, but got" ++ show t'
      (t1, e1') <- tc d g e1
      tassert (t1 <: t') $
        "Mismatch in cast: got " ++ show t1 ++
        " where " ++ show t' ++ " expected"
      t1 \/? ta' |!
        "Mismatch in cast: types " ++ show t1 ++
        " and " ++ show t' ++ " are incompatible"
      return (ta', exCast e1' t' ta')

  unworthy g e =
    any (\x -> case g =.= x of
                 Just tx -> qualifier tx == Qa
                 Nothing -> False)
        (M.keys (fv e))

tcCon         :: (Monad m, Language w) =>
                 String -> TypeI w -> m (TypeI w)
tcCon "()"   _    = terr $ "Applied 0 arity constant: ()"
tcCon "unroll" t0 = do
  case tc t0 of
    Nothing -> terr $ "Nothing to unroll in: " ++ show t0
    Just tf -> return tf
  where
    tc (TyCon n ts0 ti) =
      let ts0' = map tc ts0
          each t Nothing   (ts, Nothing)  = (t:ts, Nothing)
          each t Nothing   (ts, Just ts') = (t:ts, Just (t:ts'))
          each t (Just t') (ts, _)        = (t:ts, Just (t':ts))
       in do
         ts0'' <- snd (foldr2 each ([], Nothing) ts0 ts0')
         return (TyCon n ts0'' ti)
    tc (TyAll tv t)  = TyAll tv `fmap` tc t
    tc (TyMu tv t)   = Just (tysubst tv (TyMu tv t) t)
    tc _             = Nothing
tcCon s      _    = terr $ "Unrecognized constant: " ++ s

-- Given a list of type variables tvs, an type t in which tvs
-- may be free, and a type t', tries to substitute for tvs in t
-- to produce a type that *might* unify with t'
tryUnify :: (Monad m, Language w) =>
             [TyVar] -> TypeI w -> TypeI w -> m (TypeI w -> TypeI w)
tryUnify [] _ _        = return id
tryUnify (tv:tvs) t t' =
  case findSubst tv t t' of
    tguess:_ -> do
                  let subst' = tysubst tv tguess
                  subst <- tryUnify tvs (subst' t) t'
                  return (subst . subst')
    _        -> terr $
                  "Cannot guess type application to unify " ++
                  show t ++ " and " ++ show t'

-- Given a type variable tv, type t in which tv may be free,
-- and a second type t', finds a plausible candidate to substitute
-- for tv to make t and t' unify.  (The answer it finds doesn't
-- have to be correct.
findSubst :: Language w => TyVar -> TypeI w -> TypeI w -> [TypeI w]
findSubst tv = fs where
  fs :: Language w => TypeI w -> TypeI w -> [TypeI w]
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

tcTyDec :: Monad m => GG -> TyDec -> m GG
tcTyDec gg (TdAbs name params quals) = do
  let ix = ggN gg + 1
  let each (Left tv) = case tv `elemIndex` map snd params of
        Nothing -> terr $ "unbound tyvar " ++ show tv ++
                          " in qualifier list for type " ++ name
        Just n  -> return (Left n)
      each (Right q) = return (Right q)
  quals' <- mapM each quals
  return gg {
    ggN = ix,
    ggI = ggI gg =+= name =:= TiAbs {
      tiId    = ix,
      tiArity = map fst params,
      tiQual  = quals',
      tiTrans = False
    }
  }

tcMod :: Monad m => GG -> Mod i -> m (GG, ModI)
tcMod gg (MdC x mt e) = do
  (te, e') <- tcExprC (ggI gg) (ggC gg) e
  t' <- case mt of
    Just t  -> do
      t' <- tcOpenType (ggI gg) S.empty t
      tassert (te == t') $
        "Declared type for module " ++ show x ++ " : " ++ show t ++
        " doesn't match actual type " ++ show te
      return t'
    Nothing -> return te
  return (gg { ggC = ggC gg =+= x =:= t',
               ggA = ggA gg =+= x =:= ctype2atype t' },
          MdC x (Just t') e')
tcMod gg (MdA x mt e) = do
  (te, e') <- tcExprA (ggI gg) (ggA gg) e
  t' <- case mt of
    Just t  -> do
      t' <- tcOpenType (ggI gg) S.empty t
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
  return (gg { ggC = ggC gg =+= x =:= atype2ctype t',
               ggA = ggA gg =+= x =:= t' },
          MdA x (Just t') e')
tcMod gg (MdInt x t y) = do
  case ggC gg =.= y of
    Nothing -> terr $ "RHS of interface is unbound variable: " ++ show y
    Just ty -> do
      t' <- tcOpenType (ggI gg) S.empty t
      tassert (ty == atype2ctype t') $
        "Declared type of interface " ++ show x ++ " :> " ++
        show t' ++ " not compatible with RHS type: " ++ show ty
      return (gg { ggC = ggC gg =+= x =:= atype2ctype t',
                   ggA = ggA gg =+= x =:= t' },
              MdInt x t' y)

tcMods :: Monad m => GG -> [Mod i] -> m (GG, [Mod TInfo])
tcMods gg0 ms0 = foldM each (gg0, []) ms0 where
  each (gg, ms) m = do
    (gg', m') <- tcMod gg m
    return (gg', ms ++ [m'])

-- Type check a program
--   mkBasis     -- The basis type envs
--   (Prog ms e) -- Program to check
tcProg :: Monad m => GG -> Prog i -> m (TypeI C, ProgI)
tcProg gg0 (Prog ms e) = do
  (gg, ms') <- tcMods gg0 ms
  (t, e')   <- tcExprC (ggI gg) (ggC gg) e
  return (t, Prog ms' e')
