{-# LANGUAGE MultiParamTypeClasses, PatternGuards #-}
module Translation (
  translate, transDecls, MEnv, MEnvT
) where

import Syntax
import Env

type MEnv i = Env QLid (Let i)
type MEnvT  = MEnv TyTag

-- Parties to contracts are module names, but it's worth
-- keeping them separate from regular variables.
newtype Party = Party Ident

-- Translate a program by adding contracts.
translate :: MEnvT -> ProgT -> ProgT
translate menv0 (Prog ds e) =
  Prog ds' (transExpr menv (party (Uid "*Main*")) `fmap` e)
  where (menv, ds') = transDecls menv0 ds

transDecls :: MEnvT -> [DeclT] -> (MEnvT, [DeclT])
transDecls menv = foldl each (menv, []) where
  each (env, ds) (DcLet loc m)      = let (env', m') = transLet env m
                                       in (env', ds ++ [DcLet loc m'])
  each (env, ds) (DcTyp loc td)     = (env, ds ++ [DcTyp loc td])
  each (env, ds) (DcAbs loc at ds0) = let (env', ds0') = transDecls env ds0
                                       in (env', ds ++ [DcAbs loc at ds0'])

transLet :: MEnvT -> LetT -> (MEnvT, LetT)
transLet menv m@(LtC tl x (Just t) e) =
  (menv =+= x =:= m,
   LtC tl x (Just t) (transExpr menv (party x) e))
transLet menv m@(LtA tl x (Just t) e) =
  (menv =+= x =:= m,
   LtC tl x (Just (atype2ctype t)) (transExpr menv (party x) e))
transLet menv m@(LtInt tl x t y)      =
  (menv =+= x =:= m,
   LtC tl x (Just (atype2ctype t)) $
     exLetVar' z (transExpr menv (party x) (exVar y :: ExprT C)) $
       ac (party y) (party x) z t)
    where z = y /./ "z"
transLet menv m                  =
  (menv =+= letName m =:= m, m)

transExpr :: Language w => MEnvT -> Party -> ExprT w -> ExprT C
transExpr menv neg = te where
  tem menv' = transExpr menv' neg
  te e0 = case view e0 of
    ExId i    -> case i of
      Con k   -> exCon k
      Var x   -> transVar (reifyLang1 e0) menv neg x
    ExStr s   -> exStr s
    ExInt z   -> exInt z
    ExFloat f -> exFloat f
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
    ExPack t1 t2 e -> exPack (type2ctype t1) (type2ctype t2) (te e)
    ExCast e1 t ta -> transCast neg (te e1) t ta

type2ctype :: Language w => TypeT w -> TypeT C
type2ctype t = langCase t id atype2ctype

-- Get the LangRep from a term:
reifyLang1 :: Language w => f w -> LangRep w
reifyLang1 _ = reifyLang

-- How do we refer to a variable from a given language?
transVar :: LangRep w -> MEnvT -> Party -> QLid -> ExprT C
transVar lang menv neg x =
  case (lang, menv =.= x) of
    (C, Just (LtC _ _ (Just t) _)) -> addName C x $ \x' -> cc neg (party x) x' t
    (C, Just (LtA _ _ (Just t) _)) -> addName A x $ \x' -> ca neg (party x) x' t
    (C, Just (LtInt _ _ t _))      -> addName A x $ \x' -> ca neg (party x) x' t
    (A, Just (LtC _ _ (Just t) _)) -> addName C x $ \x' -> ac neg (party x) x'
                                                       (ctype2atype t)
    _                              -> exVar x

addName :: LangRep w -> QLid -> (Lid -> ExprT C) -> ExprT C
addName lang name k =
  exLet' (PaVar name1)
         (exLet' (PaVar name2) (exVar name) (k name2))
    (exBVar name1)
  where
  name1 = Lid ("_1" ++ show name ++ "[" ++ show lang ++ "]")
  name2 = Lid ("_2" ++ show name ++ "[" ++ show lang ++ "]")

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
  where y   = neg /./ "y"
        z   = neg /./ "z"
        pos = neg /./ "(:>)"

-- Given negative and positive blame labels, the name of an A
-- language variable we wish to protect, and the A type the variable
-- should have, generates an expression that projects that variable.
--
-- This wrapper protects the positive party and may blame the
-- negative party.
ca :: Party -> Party -> Lid -> TypeT A -> ExprT C
ca neg pos x (TyCon _ [s1, s2] td) | td == tdArr =
  exAbsVar' y (atype2ctype s1) $
    exLetVar' z (exApp (exBVar x) (ac pos neg y s1)) $
      ca neg pos z s2
  where y = x /./ "y"
        z = x /./ "z"
ca neg pos x (TyCon _ [s1, s2] td) | td == tdLol =
  exLetVar' u createContract $
    exAbsVar' y (atype2ctype s1) $
      exSeq (checkContract u neg "applied one-shot function twice") $
        exLetVar' z (exApp (exBVar x) (ac pos neg y s1)) $
          ca neg pos z s2
  where u = x /./ "u"
        y = x /./ "y"
        z = x /./ "z"
ca neg pos x (TyCon _ [s1, s2] td) | td == tdTuple =
  exLet' (PaPair (PaVar y) (PaVar z)) (exBVar x) $
    exPair (ca neg pos y s1) (ca neg pos z s2)
  where y = x /./ "y"
        z = x /./ "z"
ca neg pos x (TyQu Forall tv t) =
  exTAbs' tv' $
    exLetVar' u (exTApp (exBVar x) (TyVar tv')) $
      ca neg pos u (tysubst tv (TyVar tv' `asTypeOf` t) t)
  where tv' = TV (tvname tv /./ "v") Qu
        u   = tvname tv /./ "u"
ca neg pos x (TyQu Exists _ t) =
  ca neg pos x t
ca _   _   x (TyCon _ _ td)
  | ttTrans td         = exBVar x
ca _   _   x (TyVar tv)
  | tvqual tv <: Qu    = exBVar x
ca _   _   x (TyC _)   = exBVar x
ca neg _   x ta
  | qualifier ta <: Qu = exAbs' PaWild tyUnitT (exBVar x)
  | otherwise          =
      exLetVar' u createContract $
        exAbs' PaWild tyUnitT $
          exSeq (checkContract u neg "passed one-shot value twice") $
            exBVar x
      where u = x /./ "u"

-- Given negative and positive blame labels, the name of a C
-- language variable we wish to protect, and the A type the variable
-- should have, generates an expression that projects that variable.
--
-- This wrapper protects the negative party and may blame the
-- positive party.
ac :: Party -> Party -> Lid -> TypeT A -> ExprT C
ac neg pos x (TyCon _ [s1, s2] td) | td `elem` funtypes =
  exAbsVar' y (atype2ctype s1) $
    exLetVar' z (exApp (exBVar x) (ca pos neg y s1)) $
      ac neg pos z s2
  where y = x /./ "y"
        z = x /./ "z"
ac neg pos x (TyCon _ [s1, s2] td) | td == tdTuple =
  exLet' (PaPair (PaVar y) (PaVar z)) (exBVar x) $
    exPair (ac neg pos y s1) (ac neg pos z s2)
  where y = x /./ "y"
        z = x /./ "z"
ac neg pos x (TyQu Forall tv t) =
  exTAbs' tv' $
    exLetVar' u (exTApp (exBVar x) (TyVar tv')) $
      ac neg pos u (tysubst tv (TyVar tv' `asTypeOf` t) t)
  where tv' = TV (tvname tv /./ "v") Qu
        u   = tvname tv /./ "u"
ac neg pos x (TyQu Exists _ t) =
  ac neg pos x t
ac _   _   x (TyCon _ _ td)
  | ttTrans td         = exBVar x
ac _   _   x (TyVar tv)
  | tvqual tv <: Qu    = exBVar x
ac _   _   x (TyC _)   = exBVar x
ac _   _   x _         = exApp (exBVar x) exUnit

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
    exLetVar' z (exApp (exBVar x) (cc pos neg y s1)) $
      cc neg pos z s2
  where y = x /./ "y"
        z = x /./ "z"
cc neg pos x (TyCon _ [s1, s2] td) | td == tdTuple =
  exLet' (PaPair (PaVar y) (PaVar z)) (exBVar x) $
    exPair (cc neg pos y s1) (cc neg pos z s2)
  where y = x /./ "y"
        z = x /./ "z"
cc neg _   x (TyA ta) | not (qualifier ta <: Qu) =
  exLetVar' u createContract $
    exAbs' PaWild tyUnitT $
      exSeq (checkContract u neg "passed one-shot value twice") $
        exApp (exBVar x) exUnit
  where u = x /./ "u"
cc neg pos x (TyQu Forall tv t) =
  exTAbs' tv' $
    exLetVar' u (exTApp (exBVar x) (TyVar tv')) $
      cc neg pos u (tysubst tv (TyVar tv' `asTypeOf` t) t)
  where tv' = TV (tvname tv /./ "v") Qu
        u   = tvname tv /./ "u"
cc neg pos x (TyQu Exists _ t) =
  cc neg pos x t
cc _   _   x _ = exBVar x

-- Generate an expression to create an initial (blessed) cell
createContract :: ExprT C
createContract = exApp (exTApp (exBVar (Lid "#ref"))
                               (tyUnitT `tyArrT` tyUnitT))
                       (exAbs PaWild tyUnitT exUnit)

-- Given a variable containing a reference cell, generate code
-- to check it
checkContract :: Lid -> Party -> String -> ExprT C
checkContract x (Party who) what =
  exLetVar' f (exApp (exTApp (exBVar (Lid "#modify"))
                             (tyUnitT `tyArrT` tyUnitT))
                     (exBVar x `exPair` blameFun (show who) what)) $
    exApp (exBVar f) exUnit
  where f = x /./ "f"

-- Generate a function that raises blame
blameFun :: String -> String -> ExprT C
blameFun who what =
  exAbs PaWild tyUnitT $
    exApp (exApp (exVar (qlid "#blame"))
                 (exStr who))
          (exStr what)

-- Sort of a gensym -- safe in the context where we use it.

infixl 4 /./

class Renamable a b where
  (/./) :: a -> String -> b

instance Renamable Lid Lid where
  Lid n /./ s = Lid (n ++ '#' : s)

instance Renamable Lid QLid where
  n /./ s = QLid [] (n /./ s)

instance Renamable QLid Lid where
  n /./ s = Lid ('_' : show n) /./ s

instance Renamable QUid Lid where
  n /./ s = Lid ('_' : show n) /./ s

instance Renamable QLid QLid where
  QLid uids lid /./ s = QLid uids (lid /./ s)

instance Renamable Party Lid where
  Party (Con n) /./ s = n /./ s
  Party (Var n) /./ s = n /./ s

instance Renamable Party Party where
  Party (Con (QUid ns n)) /./ s = party (QUid ns (Uid (show n ++ s)))
  Party (Var (QLid ns n)) /./ s = party (QLid ns (Lid (show n ++ s)))

class Culpable a        where party :: a -> Party
instance Culpable Ident where party = Party
instance Culpable QUid  where party = party . Con
instance Culpable QLid  where party = party . Var
instance Culpable Uid   where party = party . QUid []
instance Culpable Lid   where party = party . QLid []

exUnit :: Expr i C
exUnit  = exCon (quid "()")

----
---- To make our code cleaner, we have two constructors
---- that perform trivial reduction on the fly:
----

-- Constructs a let expression, but with a special case:
--
--   let x      = e in x        ==   e
--   let (x, y) = e in (x, y)   ==   e
--
-- This is always safe to do.
exLet' :: Patt -> Expr i w -> Expr i w -> Expr i w
exLet' x e1 e2 = case (x, view e2) of
  (PaVar y, ExId (Var (QLid [] y')))
    | y == y'                        -> e1
  (PaPair (PaVar y) (PaVar z), ExPair ey ez)
    | ExId (Var (QLid [] y')) <- view ey,
      ExId (Var (QLid [] z')) <- view ez,
      y == y' && z == z'             -> e1
  _                                  -> exLet x e1 e2

exLetVar' :: Lid -> Expr i w -> Expr i w -> Expr i w
exLetVar'  = exLet' . PaVar

-- Constructs a lambda expression, but with a special case:
--
--    exAbs' x t (exApp (exVar f) (exVar x))  ==  exVar f
--
-- This eta-contraction is always safe, because f has no effect
exAbs' :: Patt -> Type i w -> Expr i w -> Expr i w
exAbs' x t e = case view e of
  ExApp e1 e2 -> case (x, view e1, view e2) of
    (PaVar y, ExId (Var f), ExId (Var y')) |
      QLid [] y == y' && QLid [] y /= f 
              -> exVar f
    _         -> exAbs x t e
  _           -> exAbs x t e

exAbsVar' :: Lid -> Type i w -> Expr i w -> Expr i w
exAbsVar'  = exAbs' . PaVar

-- Construct a type-lambda expression, but with a special case:
--
--   exTAbs' tv (exTApp (exVar f) tv)  ==  exVar f
--
-- This should always be safe, because f has no effect
exTAbs' :: TyVar -> Expr i w -> Expr i w
exTAbs' tv e = case view e of
  ExTApp e1 t2 -> case (view e1, t2) of
    (ExId (Var f), TyVar tv') |
      tv == tv'  -> exVar f
    _            -> exTAbs tv e
  _            -> exTAbs tv e

