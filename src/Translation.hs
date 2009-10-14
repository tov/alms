{-# LANGUAGE
      FlexibleInstances,
      ImplicitParams,
      MultiParamTypeClasses,
      PatternGuards,
      RelaxedPolyRec #-}
module Translation (
  translate, translateDecls, TEnv, tenv0
) where

import Util
import Syntax

type TEnv = ()

tenv0 :: TEnv
tenv0  = ()

-- Parties to contracts are module names, but it's worth
-- keeping them separate from regular variables.
newtype Party = Party { unParty :: Ident }
type Trail    = [Uid]

-- Translate a program by adding contracts.
translate :: TEnv -> ProgT -> ProgT
translate _ (Prog ds e) =
  Prog (transDecls ds) (transExpr (party (Uid "*Main*")) `fmap` e)
    where ?trail = []

translateDecls :: TEnv -> [DeclT] -> (TEnv, [DeclT])
translateDecls tenv ds = (tenv, transDecls ds) where ?trail = []

transDecls :: (?trail :: Trail) => [DeclT] -> [DeclT]
transDecls = map transDecl

transDecl :: (?trail :: Trail) => DeclT -> DeclT
transDecl (DcLet loc m)      = DcLet loc (transLet m)
transDecl (DcTyp loc td)     = DcTyp loc td
transDecl (DcAbs loc at ds0) = DcAbs loc at (transDecls ds0)
transDecl (DcMod loc x b)    = DcMod loc x (transMod x b)
transDecl (DcOpn loc b)      = DcOpn loc (transOpen b)
transDecl (DcLoc loc d0 d1)  = let (d0', d1') = transLocal d0 d1
                                in DcLoc loc d0' d1'

transLet :: (?trail :: Trail) => LetT -> LetT
transLet (LtC tl x mt e) =
   LtC tl x mt (transExpr (getNeg x) e)
transLet (LtA tl x mt e) =
   LtC tl x (fmap atype2ctype mt) (transExpr (getNeg x) e)
transLet (LtInt tl x t y)      =
   LtC tl x (Just ty) $
     exLetVar' z
         (transExpr (getNeg x) (exVar y *:* ty :: ExprT C)) $
       ac (party y) (getNeg x) z t
    where z  = y /./ "z"
          ty = atype2ctype t

transOpen :: (?trail :: Trail) => ModExpT -> ModExpT
transOpen b = transModExp b

transLocal :: (?trail :: Trail) =>
              [DeclT] -> [DeclT] -> ([DeclT], [DeclT])
transLocal ds0 ds1 = (transDecls ds0, transDecls ds1)

transMod :: (?trail :: Trail) =>
            Uid -> ModExpT -> ModExpT
transMod x b = transModExp b where ?trail = x : ?trail

transModExp :: (?trail :: Trail) => ModExpT -> ModExpT
transModExp (MeName n)     = MeName n
transModExp (MeStrC tl ds) = MeStrC tl (transDecls ds)
transModExp (MeStrA tl ds) = MeStrC tl (transDecls ds)

getNeg :: (?trail :: Trail, Culpable p) => p -> Party
getNeg def = case ?trail of
  []   -> party def
  p:ps -> party (J (reverse ps) p)

transExpr :: Language w => Party -> ExprT w -> ExprT C
transExpr neg = te where
  te e0 = case view e0 of
    ExId i    -> case view i of
      Right k  -> exCon k
      Left x   -> case exprType e0 of
                    Nothing         -> error $
                      "Cannot add contracts to variable if " ++
                      "type checking was skipped."
                    Just (Left tc)  -> transVar (reifyLang1 e0) tc neg x
                    Just (Right ta) -> transVar (reifyLang1 e0) ta neg x
    ExStr s   -> exStr s
    ExInt z   -> exInt z
    ExFloat f -> exFloat f
    ExCase e1 clauses -> exCase (te e1)
                                [ (xi, te ei)
                                | (xi, ei) <- clauses ]
    ExLetRec bs e2 -> exLetRec
                        [ Binding x (type2ctype t) (te e)
                        | Binding x t e <- bs ]
                        (te e2)
    ExLetDecl d e2 -> let ?trail = jpath (unParty neg) in
                      let d' = transDecl d in
                        exLetDecl d' (te e2)
    ExPair e1 e2 -> exPair (te e1) (te e2)
    ExAbs x t e -> exAbs x (type2ctype t) (te e)
    ExApp e1 e2 -> exApp (te e1) (te e2)
    ExTAbs tv e -> exTAbs tv (te e)
    ExTApp e1 t2 -> exTApp (te e1) (type2ctype t2)
    ExPack t1 t2 e -> exPack (fmap type2ctype t1) (type2ctype t2) (te e)
    ExCast e1 t ta -> transCast neg (te e1) t ta

type2ctype :: Language w => TypeT w -> TypeT C
type2ctype t = langCase t id atype2ctype

-- Get the LangRep from a term:
reifyLang1 :: Language w => f w -> LangRep w
reifyLang1 _ = reifyLang

-- How do we refer to a variable from a given language?
transVar :: (Language w') =>
            LangRep w -> TypeT w' -> Party -> QLid -> ExprT C
transVar lang_neg t_pos neg x =
  case (lang_neg, reifyLang1 t_pos) of
    (C, A) -> addName C x $ \x' -> ca neg (party x) x' t_pos
    (A, C) -> addName A x $ \x' -> ac neg (party x) x' (ctype2atype t_pos)
    (C, C)
      | J [] _ <- x  -> exVar x
      | otherwise    -> addName C x $ \x' -> cc neg (party x) x' t_pos
    (A, A) -> exVar x

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
             Party -> ExprT C -> Maybe (TypeT w) -> TypeT A -> ExprT C
transCast neg e mt' ta =
  exLetVar' y e $
    exLetVar' z (ac neg pos y ta) $   -- protect the value
      langCase (WMT mt')
        (\_ -> ca neg pos z ta)       -- protect the context, or
        (\(WMT mt) -> case mt of
           Just t  -> ca neg pos z t  -- protect the context
           Nothing -> error $
             "Cannot add contracts to cast expression if " ++
             "type checking was skipped")
  where y   = neg /./ "y"
        z   = neg /./ "z"
        pos = neg /./ "(:>)"

newtype WrapMaybeType w = WMT (Maybe (TypeT w))

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
ca _   _   x t
  | transparent t      = exBVar x
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
ac _   _   x t
  | transparent t      = exBVar x
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
createContract = exApp (exTApp (exVar (qlid "INTERNALS.ref"))
                               (tyUnitT `tyArrT` tyUnitT))
                       (exAbs PaWild tyUnitT exUnit)

-- Given a variable containing a reference cell, generate code
-- to check it
checkContract :: Lid -> Party -> String -> ExprT C
checkContract x (Party who) what =
  exLetVar' f (exApp (exTApp (exVar (qlid "INTERNALS.modify"))
                             (tyUnitT `tyArrT` tyUnitT))
                     (exBVar x `exPair` blameFun (show who) what)) $
    exApp (exBVar f) exUnit
  where f = x /./ "f"

-- Generate a function that raises blame
blameFun :: String -> String -> ExprT C
blameFun who what =
  exAbs PaWild tyUnitT $
    exApp (exApp (exVar (qlid "INTERNALS.blame"))
                 (exStr who))
          (exStr what)

-- Sort of a gensym -- safe in the context where we use it.

infixl 4 /./

class Renamable a b where
  (/./) :: a -> String -> b

instance Renamable Lid Lid where
  Lid n /./ s = Lid (n ++ '#' : s)

instance Renamable k k => Renamable k (Path p k) where
  n /./ s = J [] (n /./ s)

instance Show n => Renamable (Path Uid n) Lid where
  n /./ s = Lid ('_' : show n) /./ s

instance Renamable Party Lid where
  Party n /./ s = n /./ s

instance Renamable Party Party where
  Party (J ns (Con n)) /./ s = Party (J ns (Con (Uid (show n ++ s))))
  Party (J ns (Var n)) /./ s = Party (J ns (Var (Lid (show n ++ s))))

class Culpable a where party :: a -> Party
instance Culpable Lid where party = party . J ([] :: [Uid])
instance Culpable Uid where party = party . J ([] :: [Uid])
instance Culpable (Path Uid Lid) where party = party . fmap Var
instance Culpable (Path Uid Uid) where party = party . fmap Con
instance Culpable (Path Uid BIdent) where party = Party

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
  (PaVar y, ExId (J [] (Var y')))
    | y == y'                        -> e1
  (PaPair (PaVar y) (PaVar z), ExPair ey ez)
    | ExId (J [] (Var y')) <- view ey,
      ExId (J [] (Var z')) <- view ez,
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
    (PaVar y, ExId (J p (Var f)), ExId (J [] (Var y'))) |
      y == y' && J [] y /= J p f
              -> exVar (J p f)
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
    (ExId (J p (Var f)), TyVar tv') |
      tv == tv'  -> exVar (J p f)
    _            -> exTAbs tv e
  _            -> exTAbs tv e

