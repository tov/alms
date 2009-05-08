module Statics (
  GG(..), tcProg
) where

import Util
import Syntax
import Env as Env
import Ppr ()

import qualified Data.Map as M
import qualified Data.Set as S

-- Get the usage (sharing) of a variable in an expression:
usage :: Var -> Expr A -> Q
usage x e = case M.lookup x (fv e) of
  Just u | u > 1 -> Qu
  _              -> Qa

-- Type environments
type D   = S.Set TyVar
type G w = Env Var (Type w)
data GG  = GG { ggC :: G C, ggA :: G A }

-- Raise a type error
terr :: Monad m => String -> m a
terr s = fail $ "Type error: " ++ s

-- A type checking "assertion" raises a type error if the
-- asserted condition is false.
tassert :: Monad m => Bool -> String -> m ()
tassert True  _ = return ()
tassert False s = terr s

-- A common form of type error
tgot :: Monad m => String -> Type w -> String -> m a
tgot who got expected = terr $ who ++ " got " ++ show got ++
                               " where " ++ expected ++ " expected"

-- Run a partial computation, and if it fails, substitute
-- the given failure message.
(|!) :: Monad m => Maybe a -> String -> m a
m |! s = case m of
  Just r  -> return r
  _       -> fail s
infix 1 |!

-- Type check an expression
tcExprC :: Monad m => G C -> Expr C -> m (Type C)
tcExprC = tc S.empty where
  tc d g e0 = case expr' e0 of
    ExCon "()"    -> return (tyGround "unit")
    ExCon s
      | s `elem` constants -> terr $ "Constant must be applied: " ++ s
      | otherwise          -> terr $ "Unrecognized constant: " ++ s
    ExStr _       -> return (tyGround "string")
    ExInt _       -> return (tyGround "int")
    ExIf e1 e2 e3 -> do
      t1 <- tc d g e1
      tassert (t1 == tyGround "bool") $
        "If condition was " ++ show t1 ++ " where bool expected"
      t2 <- tc d g e2
      t3 <- tc d g e3
      tassert (t2 == t3) $
        "Mismatch in if: " ++ show t2 ++ " /= " ++ show t3
      return t2
    ExCase e1 (xl, el) (xr, er) -> do
      t1 <- tc d g e1
      case t1 of
        TyCon "either" [txl, txr] -> do
          tl <- tc d (g =+= xl =:= txl) el
          tr <- tc d (g =+= xr =:= txr) er
          tassert (tl == tr) $
            "Mismatch in match: " ++ show tl ++ " /= " ++ show tr
          return tl
        _ -> tgot "match" t1 "('a, 'b) either"
    ExLet x e1 e2 -> do
      t1 <- tc d g e1
      tc d (g =+= x =:= t1) e2
    ExVar x       -> do
      g =.= x |!
        "Unbound variable: " ++ show x
    ExPair e1 e2  -> do
      t1 <- tc d g e1
      t2 <- tc d g e2
      return (tyPair t1 t2)
    ExLetPair (x, y) e1 e2 -> do
      tassert (x /= y) $ "Repeated variable in let pair: " ++ show x
      t1 <- tc d g e1
      case t1 of
        TyCon "*" [tx, ty]
          -> tc d (g =+= x =:= tx =+= y =:= ty) e2
        _ -> tgot "let" t1 "pair type"
    ExAbs x t e     -> do
      tcType d t
      te <- tc d (g =+= x =:= t) e
      return (tyArr t te)
    ExApp e1 e2   -> case expr' e1 of
      ExCon s       -> tc d g e2 >>= tcCon s
      _             -> do
        t1 <- tc d g e1
        t2 <- tc d g e2
        let (tvs, body) = unfoldTyAll t1
        case body of
          TyCon "->" [ta, tr] -> do
            subst <- tryUnify tvs ta t2
            let ta' = subst ta
                tr' = subst tr
            tassert (ta' == t2) $
              "Mismatch in application: got " ++
              show t2 ++ " where " ++ show ta' ++ " expected"
            return tr'
          _ -> terr $ "Mismatch in application: got " ++
                       show t1 ++ " where function type expected"
    ExTAbs tv e   -> do
      t  <- tc (S.insert tv d) g e
      return (TyAll tv t)
    ExTApp e1 t2  -> do
      t1 <- tc d g e1
      case t1 of
        TyAll tv t1' -> return (tysubst tv t2 t1')
        _            -> tgot "type application" t1 "(for)all type"
    ExSeq e1 e2   -> do
      tc d g e1
      tc d g e2
    ExCast e1 t ta -> do
      tcType d t
      tcType S.empty ta
      case t of
        TyCon n [_, _] | n `elem` funtypes -> return ()
        _ -> tgot "cast (:>)" t "function type"
      t1 <- tc d g e1
      tassert (t1 == t) $
        "Mismatch in cast: declared type " ++ show t ++
        " doesn't match actual type " ++ show t1
      tassert (t1 == atype2ctype ta) $
        "Mismatch in cast: C type " ++ show t1 ++
        " is incompatible with A contract " ++ show t
      return t

tcExprA :: Monad m => G A -> Expr A -> m (Type A)
tcExprA = tc S.empty where
  tc d g e0 = case expr' e0 of
    ExCon "()"    -> return (tyGround "unit")
    ExCon s
      | s `elem` constants -> terr $ "Constant must be applied: " ++ s
      | otherwise          -> terr $ "Unrecognized constant: " ++ s
    ExStr _       -> return (tyGround "string")
    ExInt _       -> return (tyGround "int")
    ExIf e1 e2 e3 -> do
      t1 <- tc d g e1
      tassert (t1 <: tyGround "bool") $
        "If condition was " ++ show t1 ++ " where bool expected"
      t2 <- tc d g e2
      t3 <- tc d g e3
      t2 \/? t3
        |! "Mismatch in if: " ++ show t2 ++ " and " ++ show t3
    ExCase e1 (xl, el) (xr, er) -> do
      t1 <- tc d g e1
      case t1 of
        TyCon "either" [txl, txr] -> do
          tassert (qualifier txl <: usage xl el) $
            "Affine variable " ++ show xl ++ " : " ++
            show txl ++ " duplicated in match body"
          tassert (qualifier txr <: usage xr er) $
            "Affine variable " ++ show xr ++ " : " ++
            show txr ++ " duplicated in match body"
          tl <- tc d (g =+= xl =:= txl) el
          tr <- tc d (g =+= xr =:= txr) er
          tl \/? tr
            |! "Mismatch in match: " ++ show tl ++ " and " ++ show tr
        _ -> tgot "match" t1 "('a, 'b) either"
    ExLet x e1 e2 -> do
      t1 <- tc d g e1
      tassert (qualifier t1 <: usage x e2) $
        "Affine variable " ++ show x ++ " : " ++
        show t1 ++ " duplicated in let body"
      tc d (g =+= x =:= t1) e2
    ExVar x       -> do
      g =.= x |!
        "Unbound variable: " ++ show x
    ExPair e1 e2  -> do
      t1 <- tc d g e1
      t2 <- tc d g e2
      return (tyPair t1 t2)
    ExLetPair (x, y) e1 e2 -> do
      tassert (x /= y) $
        "Repeated variable in let pair: " ++ show x
      t1 <- tc d g e1
      case t1 of
        TyCon "*" [tx, ty] -> do
          tassert (qualifier tx <: usage x e2) $
            "Affine variable " ++ show x ++ " : " ++
            show tx ++ " duplicated in let body"
          tassert (qualifier ty <: usage y e2) $
            "Affine variable " ++ show y ++ " : " ++
            show ty ++ " duplicated in let body"
          tc d (g =+= x =:= tx =+= y =:= ty) e2
        _ -> terr $ "Let pair got non-pair type: " ++ show t1
    ExAbs x t e     -> do
      tcType d t
      tassert (qualifier t <: usage x e) $
        "Affine variable " ++ show x ++ " : " ++
        show t ++ " duplicated in lambda body"
      te <- tc d (g =+= x =:= t) e
      if unworthy g e0
        then return (tyLol t te)
        else return (tyArr t te)
    ExApp e1 e2   -> case expr' e1 of
      ExCon s       -> tc d g e2 >>= tcCon s
      _             -> do
        t1 <- tc d g e1
        t2 <- tc d g e2
        let (tvs, body) = unfoldTyAll t1
        case body of
          TyCon n [ta, tr]
              | n `elem` funtypes -> do
            subst <- tryUnify tvs ta t2
            let ta' = subst ta
                tr' = subst tr
            tassert (t2 <: ta') $
              "Mismatch in application: got " ++
              show t2 ++ " where " ++ show ta' ++ " expected"
            return tr'
          _ -> terr $ "Mismatch in application: got " ++
                       show t1 ++ " where function type expected"
    ExTAbs tv e   -> do
      t  <- tc (S.insert tv d) g e
      return (TyAll tv t)
    ExTApp e1 t2  -> do
      t1 <- tc d g e1
      case t1 of
        TyAll tv t1' -> do
          tassert (qualifier t2 <: tvqual tv) $
            "Mismatch in type application: got " ++
            show (qualifier t2) ++
            " type for type variable " ++ show tv
          return (tysubst tv t2 t1')
        _            -> tgot "type application" t1 "(for)all type"
    ExSeq e1 e2   -> do
      tc d g e1
      tc d g e2
    ExCast e1 t ta -> do
      tcType d t
      tcType d ta
      case t of
        TyCon n [_, _] | n `elem` funtypes -> return ()
        _ -> terr $ "Cast requires a function type, but got" ++ show t
      t1 <- tc d g e1
      tassert (t1 <: t) $
        "Mismatch in cast: got " ++ show t1 ++
        " where " ++ show t ++ " expected"
      t1 \/? ta |!
        "Mismatch in cast: types " ++ show t1 ++
        " and " ++ show t ++ " are incompatible"
      return ta

  unworthy g e =
    any (\x -> case g =.= x of
                 Just tx -> qualifier tx == Qa
                 Nothing -> False)
        (M.keys (fv e))

tcCon         :: (Monad m, Language w) => String -> Type w -> m (Type w)
tcCon "()"   _    = terr $ "Applied 0 arity constant: ()"
tcCon "unroll" t0 = do
  case tc t0 of
    Nothing -> terr $ "Nothing to unroll in: " ++ show t0
    Just tf -> return tf
  where
    tc (TyCon n ts0) =
      let ts0' = map tc ts0
          each t Nothing   (ts, Nothing)  = (t:ts, Nothing)
          each t Nothing   (ts, Just ts') = (t:ts, Just (t:ts'))
          each t (Just t') (ts, _)        = (t:ts, Just (t':ts))
       in TyCon n `fmap` snd (foldr2 each ([], Nothing) ts0 ts0')
    tc (TyAll tv t)  = TyAll tv `fmap` tc t
    tc (TyMu tv t)   = Just (tysubst tv (TyMu tv t) t)
    tc _             = Nothing
tcCon s      _    = terr $ "Unrecognized constant: " ++ s

-- Given a list of type variables tvs, an type t in which tvs
-- may be free, and a type t', tries to substitute for tvs in t
-- to produce a type that *might* unify with t'
tryUnify :: (Monad m, Language w) =>
             [TyVar] -> Type w -> Type w -> m (Type w -> Type w)
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
findSubst :: Language w => TyVar -> Type w -> Type w -> [Type w]
findSubst tv = fs where
  fs :: Language w => Type w -> Type w -> [Type w]
  fs (TyVar tv') t' | tv == tv'
    = [t']
  fs (TyCon _ ts) (TyCon _ ts')
    = concat (zipWith fs ts ts')
  fs (TyAll tv0 t) (TyAll tv0' t') | tv /= tv0
    = [ tr | tr <- fs t t', tr /= TyVar tv0' ]
  fs (TyC t) (TyC t')
    = concat (zipWith fs (cgetas t) (cgetas t'))
  fs (TyA t) (TyA t')
    = concat (zipWith fs (agetcs t) (agetcs t'))
  fs _ _
    = []

-- Check type for closed-ness
tcType :: Monad m => D -> Type w -> m ()
tcType d0 = tc (d0, S.empty) where
  tc                     :: Monad m => (D, D) -> Type w -> m ()
  tc (d, _ ) (TyVar tv)   = tassert (S.member tv d) $
                              "Free type variable: " ++ show tv
  tc (d, d') (TyCon _ ts) = mapM_ (tc (d, d')) ts
  tc (d, d') (TyAll tv t) = tc (S.insert tv d, d') t
  tc (d, d') (TyMu tv t)  = tc (S.insert tv d, d') t
  tc (d, d') (TyC t)      = tc (d', d) t
  tc (d, d') (TyA t)      = tc (d', d) t

-- Build both initial environments
makeEnv0 :: [Mod] -> GG -> GG
makeEnv0 ms gw0 =
  let cenv = ggC gw0 =+= fromList (map each ms) where
        each (MdC x t _)   = (x, t)
        each (MdA x t _)   = (x, atype2ctype t)
        each (MdInt x t _) = (x, atype2ctype t)
      aenv = ggA gw0 =+= fromList (map each ms) where
        each (MdC x t _)   = (x, ctype2atype t)
        each (MdA x t _)   = (x, t)
        each (MdInt x t _) = (x, t)
   in GG { ggC = cenv, ggA = aenv }

-- Type check a module.  The boolean 're' tells whether to type check
-- in "re-type mode", which doesn't require module bodies to be syntactic
-- values.
tcMod :: Monad m => Bool -> GG -> Mod -> m ()
tcMod re gg (MdC x t e) = do
  te <- tcExprC (ggC gg) e
  tassert (re || syntacticValue e) $
    "Body of module " ++ show x ++ " not a syntactic value"
  tassert (te == t) $
    "Declared type for module " ++ show x ++ " : " ++ show t ++
    " doesn't match actual type " ++ show te
tcMod re gg (MdA x t e) = do
  te <- tcExprA (ggA gg) e
  tassert (qualifier t == Qu) $
    "Declared type of module " ++ show x ++ " is not unlimited"
  tassert (re || syntacticValue e) $
    "Body of module " ++ show x ++ " not a syntactic value"
  tassert (te <: t) $
    "Declared type for module " ++ show x ++ " : " ++ show t ++
    " is not subsumed by actual type " ++ show te
tcMod _  gg (MdInt x t y) = do
  case ggC gg =.= y of
    Nothing -> terr $ "RHS of interface is unbound variable: " ++ show y
    Just ty -> do
      tassert (ty == atype2ctype t) $
        "Declared type of interface " ++ show x ++ " :> " ++
        show t ++ " not compatible with RHS type: " ++ show ty

tcMods :: Monad m => Bool -> GG -> [Mod] -> m ()
tcMods re gg = each [] where
  each _    []     = return ()
  each seen (m:ms) = do
    tassert (modName m `notElem` seen) $
      "Duplicate module name: " ++ show (modName m)
    tcMod re gg m
    each (modName m : seen) ms

-- Type check a program
--   re          -- Are we re-type checking after translation?
--   mkBasis     -- The basis type envs
--   (Prog ms e) -- Program to check
tcProg :: Monad m => Bool -> GG -> Prog -> m (Type C)
tcProg re mkBasis (Prog ms e) = do
  let gg = makeEnv0 ms mkBasis
  tcMods re gg ms
  tcExprC (ggC gg) e
