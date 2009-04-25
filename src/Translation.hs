module Translation (
  translate
) where

import Syntax
import Env

type MEnv = Env Var Mod

-- Translate a program by adding contracts.
-- Also performs some *trivial* optimizations.
translate :: Prog -> Prog
translate (Prog ms e) =
  Prog (map (transMod menv) ms)
       (transExpr menv (Var "*main*") e)
  where menv = fromList [ (modName m, m) | m <- ms ]

transMod :: MEnv -> Mod -> Mod
transMod menv (MdC x t e) =
  MdC x t (transExpr menv x e)
transMod menv (MdA x t e) =
  MdC x (atype2ctype t) (transExpr menv x e)
transMod menv (MdInt x t y)   =
  MdC x (atype2ctype t) $
    exLet' z (transExpr menv x (exVar y :: Expr C)) $
      a y x z t
    where z = y /./ "z"

transExpr :: Language w => MEnv -> Var -> Expr w -> Expr C
transExpr menv neg = te where
  tem menv' = transExpr menv' neg
  te e0 = case expr' e0 of
    ExCon s -> exCon s
    ExStr s -> exStr s
    ExInt z -> exInt z
    ExIf ec et ef -> exIf (te ec) (te et) (te ef)
    ExLet x e1 e2 -> exLet' x (te e1) (tem (menv =-= x) e2)
    ExVar x -> transVar (reifyLang1 e0) menv neg x
    ExPair e1 e2 -> exPair (te e1) (te e2)
    ExLetPair (x, y) e1 e2 -> exLetPair (x, y) (te e1)
                                (tem (menv =-= x =-= y) e2)
    ExAbs x t e -> exAbs' x (type2ctype t) (tem (menv =-= x) e)
    ExApp e1 e2 -> exApp (te e1) (te e2)
    ExSeq e1 e2 -> exSeq (te e1) (te e2)
    ExCast e1 t ta -> transCast (reifyLang1 e0) neg (te e1) t ta

type2ctype :: Language w => Type w -> Type C
type2ctype t = langCase t id atype2ctype

-- Get the LangRep from a term:
reifyLang1 :: Language w => f w -> LangRep w
reifyLang1 _ = reifyLang

-- How do we refer to a variable from a given language?
transVar :: LangRep w -> MEnv -> Var -> Var -> Expr C
transVar lang menv neg x =
  case (lang, menv =.= x) of
    (C, Just (MdA _ t _))   -> c neg x x t
    (C, Just (MdInt _ t _)) -> c neg x x t
    (A, Just (MdC _ t _))   -> a neg x x (ctype2atype t)
    _                       -> exVar x

-- Translate a cast ("dynamic promotion")
transCast :: LangRep w -> Var -> Expr C -> Type w -> Type A -> Expr C
transCast C neg e _ ta =
  exLet' y e $
    exLet' z (a neg neg y ta) $
      c neg neg z ta
    where y = neg /./ "y"
          z = neg /./ "z"
transCast A neg e t ta =
  exLet' y e $
    exLet' z (a neg neg y ta) $
      c neg neg z t
    where y = neg /./ "y"
          z = neg /./ "z"

-- Given negative and positive blame labels, the name of an A
-- language variable we wish to protect, and the A type the variable
-- should have, generates an expression that projects that variable.
--
-- This wrapper protects the positive party.
c :: Var -> Var -> Var -> Type A -> Expr C
c _   _   x (TyApp n []) | n `elem` transparent = exVar x
c neg pos x (TyApp "->" [s1, s2]) =
  exAbs' y (atype2ctype s1) $
    exLet' z (exApp (exVar x) (a pos neg y s1)) $
      c neg pos z s2
  where y = x /./ "y"
        z = x /./ "z"
c neg pos x (TyApp "-o" [s1, s2]) =
  exLet u createContract $
    exAbs y (atype2ctype s1) $
      exSeq (checkContract u neg "applied one-shot function twice") $
        exLet' z (exApp (exVar x) (a pos neg y s1)) $
          c neg pos z s2
  where u = x /./ "u"
        y = x /./ "y"
        z = x /./ "z"
c neg _   x _ =
  exLet' u createContract $
    exAbs' y tyUnit $
      exSeq (checkContract u neg "passed one-shot value twice") $
        exVar x
  where u = x /./ "u"
        y = x /./ "y"

-- Given negative and positive blame labels, the name of a C
-- language variable we wish to protect, and the A type the variable
-- should have, generates an expression that projects that variable.
--
-- This wrapper protects the negative party.
a :: Var -> Var -> Var -> Type A -> Expr C
a _   _   x (TyApp n [])       | n `elem` transparent = exVar x
a neg pos x (TyApp n [s1, s2]) | n `elem` funtypes =
  exAbs' y (atype2ctype s1) $
    exLet' z (exApp (exVar x) (c pos neg y s1)) $
      a neg pos z s2
  where y = x /./ "y"
        z = x /./ "z"
a _   _   x _ = exApp (exVar x) exUnit

-- Generate an expression to create an initial (blessed) cell
createContract :: Expr C
createContract = exApp (exCon "ref")
                       (exAbs (Var "_") tyUnit exUnit)

-- Given a variable containing a reference cell, generate code
-- to check it
checkContract :: Var -> Var -> String -> Expr C
checkContract x who what =
  exLetPair (d, f) (exApp (exCon "swap")
                          (exPair (exVar x)
                                  (blameFun (show who) what))) $
    exApp (exVar f) exUnit
  where d = x /./ "d"
        f = x /./ "f"

-- Generate a function that raises blame
blameFun :: String -> String -> Expr C
blameFun who what =
  exAbs (Var "_") tyUnit $
    exApp (exApp (exVar (Var "#blame"))
                 (exStr who))
          (exStr what)

-- Sort of a gensym -- safe in the context where we use it.
(/./)      :: Var -> String -> Var
Var v /./ s = Var (v ++ '#' : s)

tyUnit :: Type C
tyUnit  = tyGround "unit"

exUnit :: Expr C
exUnit  = exCon "()"

----
---- To make our code cleaner, we have two constructors
---- that perform trivial reduction on the fly:
----

-- Constructs a let expression, but with a special case:
--
--   exLet' x e (exVar x)  ==  e
--
-- This is always safe to do.
exLet' :: Var -> Expr w -> Expr w -> Expr w
exLet' v e1 e2 = case expr' e2 of
  ExVar v' | v == v' -> e1
  _                  -> exLet v e1 e2

-- Constructs a lambda expression, but with a special case:
--
--    exAbs' x t (exApp (exVar f) (exVar x))  ==  exVar f
--
-- This eta-contraction is always safe, because f has no effect
exAbs' :: Var -> Type w -> Expr w -> Expr w
exAbs' x t e = case expr' e of
  ExApp e1 e2 -> case (expr' e1, expr' e2) of
    (ExVar f, ExVar x') |
      x == x' && x /= f -> exVar f
    _                   -> exAbs x t e
  _           -> exAbs x t e

