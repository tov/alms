module Translation (
  translate, transDecls, MEnv, MEnvT
) where

import Syntax
import Env

type MEnv i = Env Lid (Mod i)
type MEnvT  = MEnv TyTag

-- Parties to contracts are module names, but it's worth
-- keeping them separate from regular variables.
newtype Party = Party { unParty :: Lid }

-- Translate a program by adding contracts.
translate :: MEnvT -> ProgT -> ProgT
translate menv0 (Prog ds e) =
  Prog ds' (transExpr menv (Party (Lid "*main*")) e)
  where (menv, ds') = transDecls menv0 ds

transDecls :: MEnvT -> [DeclT] -> (MEnvT, [DeclT])
transDecls menv = foldl each (menv, []) where
  each (env, ds) (DcMod m)      = let (env', m') = transMod env m
                                   in (env', ds ++ [DcMod m'])
  each (env, ds) (DcTyp td)     = (env, ds ++ [DcTyp td])
  each (env, ds) (DcAbs at ds0) = let (env', ds0') = transDecls env ds0
                                   in (env', ds ++ [DcAbs at ds0'])

transMod :: MEnvT -> ModT -> (MEnvT, ModT)
transMod menv m@(MdC x (Just t) e) =
  (menv =+= x =:= m,
   MdC x (Just t) (transExpr menv (Party x) e))
transMod menv m@(MdA x (Just t) e) =
  (menv =+= x =:= m,
   MdC x (Just (atype2ctype t)) (transExpr menv (Party x) e))
transMod menv m@(MdInt x t y)      =
  (menv =+= x =:= m,
   MdC x (Just (atype2ctype t)) $
     exLetVar' z (transExpr menv (Party x) (exVar y :: ExprT C)) $
       ac (Party y) (Party x) z t)
    where z = y /./ "z"
transMod menv m                  =
  (menv =+= modName m =:= m, m)

transExpr :: Language w => MEnvT -> Party -> ExprT w -> ExprT C
transExpr menv neg = te where
  tem menv' = transExpr menv' neg
  te e0 = case expr' e0 of
    ExId i  -> case i of
      Con k -> exCon k
      Var x -> transVar (reifyLang1 e0) menv neg x
    ExStr s -> exStr s
    ExInt z -> exInt z
    ExCase e1 clauses -> exCase (te e1)
                                [ (xi, tem (menv =--= pv xi) ei)
                                | (xi, ei) <- clauses ]
    ExLetRec bs e2 -> let rec = tem (foldl (=-=) menv (map bnvar bs))
                      in exLetRec
                           [ Binding x (type2ctype t) (rec e)
                           | Binding x t e <- bs ]
                           (rec e2)
    ExPair e1 e2 -> exPair (te e1) (te e2)
    ExAbs x t e -> exAbs x (type2ctype t) (tem (menv =--= pv x) e)
    ExApp e1 e2 -> exApp (te e1) (te e2)
    ExTAbs tv e -> exTAbs tv (te e)
    ExTApp e1 t2 -> exTApp (te e1) (type2ctype t2)
    ExCast e1 t ta -> transCast neg (te e1) t ta

type2ctype :: Language w => TypeT w -> TypeT C
type2ctype t = langCase t id atype2ctype

-- Get the LangRep from a term:
reifyLang1 :: Language w => f w -> LangRep w
reifyLang1 _ = reifyLang

-- How do we refer to a variable from a given language?
transVar :: LangRep w -> MEnvT -> Party -> Lid -> ExprT C
transVar lang menv neg x =
  case (lang, menv =.= x) of
    (C, Just (MdC _ (Just t) _)) -> cc neg (Party x) x t
    (C, Just (MdA _ (Just t) _)) -> ca neg (Party x) x t
    (C, Just (MdInt _ t _))      -> ca neg (Party x) x t
    (A, Just (MdC _ (Just t) _)) -> ac neg (Party x) x (ctype2atype t)
    _                            -> exVar x

-- Translate a cast ("dynamic promotion")
--
--  - In C, given (e : t :> ta), we know that e follows t, but we have
--    no reason to believe it follows ta, nor does its context.  Thus,
--    we protect in both directions by ta.
--
--  - In A, given (e : t :> ta), we know from A's type system that e
--    follows t and the context follows ta.  Thus, we need ensure that
--    e follows ta and that the context follows t.
--
transCast :: Language w =>
             Party -> ExprT C -> TypeT w -> TypeT A -> ExprT C
transCast neg e t' ta =
  exLetVar' y e $
    exLetVar' z (ac neg pos y ta) $   -- protect the value
      langCase t'
        (\_ -> ca neg pos z ta)    -- protect the context, or
        (\t -> ca neg pos z t)     -- protect the context
  where y = unParty neg /./ "y"
        z = unParty neg /./ "z"
        pos = neg /^/ "(:>)"

-- Given negative and positive blame labels, the name of an A
-- language variable we wish to protect, and the A type the variable
-- should have, generates an expression that projects that variable.
--
-- This wrapper protects the positive party and may blame the
-- negative party.
ca :: Party -> Party -> Lid -> TypeT A -> ExprT C
ca neg pos x (TyCon _ [s1, s2] td) | td == tdArr =
  exAbsVar' y (atype2ctype s1) $
    exLetVar' z (exApp (exVar x) (ac pos neg y s1)) $
      ca neg pos z s2
  where y = x /./ "y"
        z = x /./ "z"
ca neg pos x (TyCon _ [s1, s2] td) | td == tdLol =
  exLetVar' u createContract $
    exAbsVar' y (atype2ctype s1) $
      exSeq (checkContract u neg "applied one-shot function twice") $
        exLetVar' z (exApp (exVar x) (ac pos neg y s1)) $
          ca neg pos z s2
  where u = x /./ "u"
        y = x /./ "y"
        z = x /./ "z"
ca neg pos x (TyAll tv t) =
  exTAbs' tv' $
    exLetVar' u (exTApp (exVar x) (TyVar tv')) $
      ca neg pos u (tysubst tv (TyVar tv' `asTypeOf` t) t)
  where tv' = TV (tvname tv /./ "v") Qu
        u   = tvname tv /./ "u"
ca neg _   x ta | qualifier ta <: Qu = exVar x
                | otherwise =
  exLetVar' u createContract $
    exAbsVar' y tyUnitT $
      exSeq (checkContract u neg "passed one-shot value twice") $
        exVar x
  where u = x /./ "u"
        y = x /./ "y"

-- Given negative and positive blame labels, the name of a C
-- language variable we wish to protect, and the A type the variable
-- should have, generates an expression that projects that variable.
--
-- This wrapper protects the negative party and may blame the
-- positive party.
ac :: Party -> Party -> Lid -> TypeT A -> ExprT C
ac neg pos x (TyCon _ [s1, s2] td) | td `elem` funtypes =
  exAbsVar' y (atype2ctype s1) $
    exLetVar' z (exApp (exVar x) (ca pos neg y s1)) $
      ac neg pos z s2
  where y = x /./ "y"
        z = x /./ "z"
ac neg pos x (TyAll tv t) =
  exTAbs' tv' $
    exLetVar' u (exTApp (exVar x) (TyVar tv')) $
      ac neg pos u (tysubst tv (TyVar tv' `asTypeOf` t) t)
  where tv' = TV (tvname tv /./ "v") Qu
        u   = tvname tv /./ "u"
ac _   _   x ta | qualifier ta <: Qu = exVar x
                | otherwise = exApp (exVar x) exUnit

-- Given negative and positive blame labels, the name of a C
-- language variable we wish to protect, and the C type the variable
-- should have, generates an expression that projects that C modules
-- from each other.  This only generates coercions when the C type
-- has an A type embedded in it.
--
-- This isn't necessary for soundness, but is necessary to place
-- the blame on the correct C module.
--
-- This wrapper protects either party and may blame either party.
cc :: Party -> Party -> Lid -> TypeT C -> ExprT C
cc neg pos x (TyCon _ [s1, s2] td) | td == tdArr =
  exAbsVar' y s1 $
    exLetVar' z (exApp (exVar x) (cc pos neg y s1)) $
      cc neg pos z s2
  where y = x /./ "y"
        z = x /./ "z"
cc neg _   x (TyA ta) | not (qualifier ta <: Qu) =
  exLetVar' u createContract $
    exAbsVar' y tyUnitT $
      exSeq (checkContract u neg "passed one-shot value twice") $
        exApp (exVar x) exUnit
  where y = x /./ "y"
        u = x /./ "u"
cc neg pos x (TyAll tv t) =
  exTAbs' tv' $
    exLetVar' u (exTApp (exVar x) (TyVar tv')) $
      cc neg pos u (tysubst tv (TyVar tv' `asTypeOf` t) t)
  where tv' = TV (tvname tv /./ "v") Qu
        u   = tvname tv /./ "u"
cc _   _   x _ = exVar x

-- Generate an expression to create an initial (blessed) cell
createContract :: ExprT C
createContract = exApp (exTApp (exVar (Lid "#ref"))
                               (tyUnitT `tyArrT` tyUnitT))
                       (exAbs PaWild tyUnitT exUnit)

-- Given a variable containing a reference cell, generate code
-- to check it
checkContract :: Lid -> Party -> String -> ExprT C
checkContract x (Party who) what =
  exLetVar' f (exApp (exTApp (exVar (Lid "#modify"))
                             (tyUnitT `tyArrT` tyUnitT))
                     (exVar x `exPair` blameFun (show who) what)) $
    exApp (exVar f) exUnit
  where f = x /./ "f"

-- Generate a function that raises blame
blameFun :: String -> String -> ExprT C
blameFun who what =
  exAbs PaWild tyUnitT $
    exApp (exApp (exVar (Lid "#blame"))
                 (exStr who))
          (exStr what)

-- Sort of a gensym -- safe in the context where we use it.
(/./)      :: Lid -> String -> Lid
Lid v /./ s = Lid (v ++ '#' : s)

(/^/)      :: Party -> String -> Party
Party (Lid v) /^/ s = Party (Lid (v ++ s))

exUnit :: Expr i C
exUnit  = exCon (Uid "()")

----
---- To make our code cleaner, we have two constructors
---- that perform trivial reduction on the fly:
----

-- Constructs a let expression, but with a special case:
--
--   exLet' x e (exVar x)  ==  e
--
-- This is always safe to do.
exLet' :: Patt -> Expr i w -> Expr i w -> Expr i w
exLet' x e1 e2 = case (x, expr' e2) of
  (PaVar y, ExId (Var y')) | y == y' -> e1
  _                                  -> exLet x e1 e2

exLetVar' :: Lid -> Expr i w -> Expr i w -> Expr i w
exLetVar'  = exLet' . PaVar

-- Constructs a lambda expression, but with a special case:
--
--    exAbs' x t (exApp (exVar f) (exVar x))  ==  exVar f
--
-- This eta-contraction is always safe, because f has no effect
exAbs' :: Patt -> Type i w -> Expr i w -> Expr i w
exAbs' x t e = case expr' e of
  ExApp e1 e2 -> case (x, expr' e1, expr' e2) of
    (PaVar y, ExId (Var f), ExId (Var y')) |
      y == y' && y /= f -> exVar f
    _                   -> exAbs x t e
  _           -> exAbs x t e

exAbsVar' :: Lid -> Type i w -> Expr i w -> Expr i w
exAbsVar'  = exAbs' . PaVar

-- Construct a type-lambda expression, but with a special case:
--
--   exTAbs' tv (exTApp (exVar f) tv)  ==  exVar f
--
-- This should always be safe, because f has no effect
exTAbs' :: TyVar -> Expr i w -> Expr i w
exTAbs' tv e = case expr' e of
  ExTApp e1 t2 -> case (expr' e1, t2) of
    (ExId (Var f), TyVar tv') |
      tv == tv'  -> exVar f
    _            -> exTAbs tv e
  _            -> exTAbs tv e

