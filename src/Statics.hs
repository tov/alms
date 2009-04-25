module Statics (
  GG(..), tcProg
) where

-- import Util
import Syntax
import Env as Env
import Ppr ()

import qualified Data.Map as M

-- Get the usage (sharing) of a variable in an expression:
usage :: Var -> Expr A -> Q
usage x e = case M.lookup x (fv e) of
  Just u | u > 1 -> Qu
  _              -> Qa

-- Type environments
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

-- Run a partial computation, and if it fails, substitute
-- the given failure message.
(|!) :: Monad m => Maybe a -> String -> m a
m |! s = case m of
  Just r  -> return r
  _       -> fail s
infix 1 |!

-- Type check an expression
tcExprC :: Monad m => G C -> Expr C -> m (Type C)
tcExprC g0 = tc g0 where
  tc g e0 = case expr' e0 of
    ExCon "()"    -> return (tyGround "unit")
    ExCon s
      | s `elem` constants -> terr $ "Constant must be applied: " ++ s
      | otherwise          -> terr $ "Unrecognized constant: " ++ s
    ExStr _       -> return (tyGround "string")
    ExInt _       -> return (tyGround "int")
    ExIf e1 e2 e3 -> do
      t1 <- tc g e1
      tassert (t1 == tyGround "bool") $
        "If condition was " ++ show t1 ++ " where bool expected"
      t2 <- tc g e2
      t3 <- tc g e3
      tassert (t2 == t3) $
        "Mismatch in if: " ++ show t2 ++ " /= " ++ show t3
      return t2
    ExLet x e1 e2 -> do
      t1 <- tc g e1
      tc (g =+= x =:= t1) e2
    ExVar x       -> do
      g =.= x |!
        "Unbound variable: " ++ show x
    ExPair e1 e2  -> do
      t1 <- tc g e1
      t2 <- tc g e2
      return (tyPair t1 t2)
    ExLetPair (x, y) e1 e2 -> do
      tassert (x /= y) $ "Repeated variable in let pair: " ++ show x
      t1 <- tc g e1
      case t1 of
        TyApp "*" [tx, ty]
          -> tc (g =+= x =:= tx =+= y =:= ty) e2
        _ -> terr $ "Let pair got non-pair type: " ++ show t1
    ExAbs x t e     -> do
      te <- tc (g =+= x =:= t) e
      return (tyArr t te)
    ExApp e1 e2   -> case expr' e1 of
      ExCon s       -> tc g e2 >>= tcCon s
      _             -> do
        t1 <- tc g e1
        t2 <- tc g e2
        case t1 of
          TyApp "->" [ta, tr] -> do
            tassert (ta == t2) $
              "Mismatch in application: got " ++
              show t2 ++ " where " ++ show ta ++ " expected"
            return tr
          _ -> terr $ "Mismatch in application: got " ++
                       show t1 ++ " where function type expected"
    ExSeq e1 e2   -> do
      tc g e1
      tc g e2
    ExCast e1 t   -> do
      case t of
        TyApp n [_, _] | n `elem` funtypes -> return ()
        _ -> terr $ "Cast requires a function type, but got" ++ show t
      t1 <- tc g e1
      tassert (t1 == atype2ctype t) $
        "Mismatch in cast: C type " ++ show t1 ++
        " is incompatible with A contract " ++ show t
      return t1

  tcCon "ref"  t = return (TyApp "ref" [t])
  tcCon "swap" t = case t of
                     TyApp "*" [TyApp "ref" [t0], t1] | t0 == t1
                       -> return t
                     _ -> terr $ "swap got " ++ show t ++
                                 " where (A ref * A) expected"
  tcCon "()"   _ = terr $ "Applied 0 arity constant: ()"
  tcCon s      _ = terr $ "Unrecognized constant: " ++ s

tcExprA :: Monad m => G A -> Expr A -> m (Type A)
tcExprA g0 = tc g0 where
  tc g e0 = case expr' e0 of
    ExCon "()"    -> return (tyGround "unit")
    ExCon s
      | s `elem` constants -> terr $ "Constant must be applied: " ++ s
      | otherwise          -> terr $ "Unrecognized constant: " ++ s
    ExStr _       -> return (tyGround "string")
    ExInt _       -> return (tyGround "int")
    ExIf e1 e2 e3 -> do
      t1 <- tc g e1
      tassert (t1 <: tyGround "bool") $
        "If condition was " ++ show t1 ++ " where bool expected"
      t2 <- tc g e2
      t3 <- tc g e3
      t2 \/? t3
        |! "Mismatch in if: " ++ show t2 ++ " and " ++ show t3
    ExLet x e1 e2 -> do
      t1 <- tc g e1
      tassert (qualifier t1 <: usage x e2) $
        "Affine variable " ++ show x ++ " : " ++
        show t1 ++ " duplicated in let body"
      tc (g =+= x =:= t1) e2
    ExVar x       -> do
      g =.= x |!
        "Unbound variable: " ++ show x
    ExPair e1 e2  -> do
      t1 <- tc g e1
      t2 <- tc g e2
      return (tyPair t1 t2)
    ExLetPair (x, y) e1 e2 -> do
      tassert (x /= y) $
        "Repeated variable in let pair: " ++ show x
      t1 <- tc g e1
      case t1 of
        TyApp "*" [tx, ty] -> do
          tassert (qualifier tx <: usage x e2) $
            "Affine variable " ++ show x ++ " : " ++
            show tx ++ " duplicated in let body"
          tassert (qualifier ty <: usage y e2) $
            "Affine variable " ++ show y ++ " : " ++
            show ty ++ " duplicated in let body"
          tc (g =+= x =:= tx =+= y =:= ty) e2
        _ -> terr $ "Let pair got non-pair type: " ++ show t1
    ExAbs x t e     -> do
      tassert (qualifier t <: usage x e) $
        "Affine variable " ++ show x ++ " : " ++
        show t ++ " duplicated in lambda body"
      te <- tc (g =+= x =:= t) e
      if unworthy g e0
        then return (tyLol t te)
        else return (tyArr t te)
    ExApp e1 e2   -> case expr' e1 of
      ExCon s       -> tc g e2 >>= tcCon s
      _             -> do
        t1 <- tc g e1
        t2 <- tc g e2
        case t1 of
          TyApp n [ta, tr]
              | n `elem` funtypes -> do
            tassert (t2 <: ta) $
              "Mismatch in application: got " ++
              show t2 ++ " where " ++ show ta ++ " expected"
            return tr
          _ -> terr $ "Mismatch in application: got " ++
                       show t1 ++ " where function type expected"
    ExSeq e1 e2   -> do
      tc g e1
      tc g e2
    ExCast e1 t   -> do
      case t of
        TyApp n [_, _] | n `elem` funtypes -> return ()
        _ -> terr $ "Cast requires a function type, but got" ++ show t
      t1 <- tc g e1
      t1 \/? t |!
        "Mismatch in cast: types " ++ show t1 ++
        " and " ++ show t ++ " are incompatible"
      return t

  unworthy g e =
    any (\x -> case g =.= x of
                 Just tx -> qualifier tx == Qa
                 Nothing -> False)
        (M.keys (fv e))

  tcCon "ref"  t = return (TyApp "ref" [t])
  tcCon "swap" t = case t of
                     TyApp "*" [TyApp "ref" [t0], t1]
                       -> return (TyApp "*"
                                        [TyApp "ref" [t1], t0])
                     _ -> terr $ "swap got " ++ show t ++
                                 " where (A ref * A) expected"
  tcCon "()"   _ = terr $ "Applied 0 arity constant: ()"
  tcCon s      _ = terr $ "Unrecognized constant: " ++ s

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

-- Type check a module
tcMod :: Monad m => GG -> Mod -> m ()
tcMod gg (MdC x t e) = do
  te <- tcExprC (ggC gg) e
  tassert (syntacticValue e) $
    "Body of module " ++ show x ++ " not a syntactic value"
  tassert (te == t) $
    "Declared type for module " ++ show x ++ " : " ++ show t ++
    " doesn't match actual type " ++ show te
tcMod gg (MdA x t e) = do
  te <- tcExprA (ggA gg) e
  tassert (qualifier t == Qu) $
    "Declared type of module " ++ show x ++ " is not unlimited"
  tassert (syntacticValue e) $
    "Body of module " ++ show x ++ " not a syntactic value"
  tassert (te <: t) $
    "Declared type for module " ++ show x ++ " : " ++ show t ++
    " is not subsumed by actual type " ++ show te
tcMod gg (MdInt x t y) = do
  case ggC gg =.= y of
    Nothing -> terr $ "RHS of interface is unbound variable: " ++ show y
    Just ty -> do
      tassert (ty == atype2ctype t) $
        "Declared type of interface " ++ show x ++ " :> " ++
        show t ++ " not compatible with RHS type: " ++ show ty

tcMods :: Monad m => GG -> [Mod] -> m ()
tcMods gg = each [] where
  each _    []     = return ()
  each seen (m:ms) = do
    tassert (modName m `notElem` seen) $
      "Duplicate module name: " ++ show (modName m)
    tcMod gg m
    each (modName m : seen) ms

tcProg :: Monad m => GG -> Prog -> m (Type C)
tcProg mkBasis (Prog ms e) = do
  let gg = makeEnv0 ms mkBasis
  tcMods gg ms
  tcExprC (ggC gg) e
