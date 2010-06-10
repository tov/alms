{-# LANGUAGE
      GeneralizedNewtypeDeriving,
      PatternGuards,
      ViewPatterns #-}
module Sigma (
  makeBangPatt, parseBangPatt, exSigma
) where

import Syntax
import Util

import qualified Control.Monad.State as CMS
import Data.Generics (Data, everywhere, mkT, extT)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable (Foldable, toList)

-- | To lift a binder to bind effect variables rather than
--   normal variables.  (Boolean specifies whether the result
--   should include the effect variables.)
exSigma :: Id i =>
           Bool ->
           (Patt i -> Expr i -> a) ->
           Patt i -> Expr i -> a
exSigma ret binder patt body =
  let (b_vars, b_code) = transform (dv patt) body in
  binder (ren patt) $
  exLet' (paVar r1 -:: b_vars) b_code $
  if ret
    then exPair (exBVar r1) (patt2expr (ren (flatpatt patt)))
    else exBVar r1

-- | To lift a binder to bind effect variables rather than
--   normal variables.
exAddSigma :: Id i =>
              Bool ->
              ([Lid i] -> Patt i -> Expr i -> a) ->
              S.Set (Lid i) -> Patt i -> Expr i -> a
exAddSigma ret binder env patt body =
  let env'             = dv patt
      (b_vars, b_code) = transform (env' `S.union` env) body
      vars = [ v | v <- b_vars, v `S.notMember` ren env' ]
   in binder vars (ren patt) $
      exLet' (paVar r1 -:: b_vars) b_code $
      if ret
        then exPair (exBVar r1) (patt2expr (ren (flatpatt patt))) +:: vars
        else exBVar r1 +:: vars

{-
---- The one variable case:

  (x is the variable name, y is the fresh state name)

  fun !(x:t) -> e     ===  fun y:t -> [[ e ]]
  let !x = e1 in e2   ===   let y = e1 in [[ e ]]

  [[ e1 x ]]  = let (r, y) = [[ e1 ]] in
                  r y
  [[ e1 e2 ]] = let (r1, y) = [[ e1 ]] in
                let (r2, y) = [[ e2 ]] in
                  (r1 r2, y)
  [[ x ]]     = (y, ())
  [[ v ]]     = (v, y)
  [[ match e with
     | p1 -> e1
     | ...
     | pk -> ek ]]
              = let (r, y) = [[ e ]] in
                match r with
                | p1 -> [[ e1 ]]
                | ...
                | pk -> [[ ek ]]
  [[ e [t] ]] = let (r, y) = [[ e ]] in
                  (r [t], y)
  [[ c e ]]   = let (r, y) = [[ e ]] in
                  (c r, y)

-- The pattern case (2):

  (p! is a renaming of p)

  fun !(p:t) -> e     ===   fun p!:t -> 
                            let (r1, e.vars) = e.code
                             in (r1, p!)
                            where e.env = dv p in
  let !p = e1 in e2   ===   let p! = e1 in
                            let (r1, e.vars) = e.code
                             in (r1, p!)
                            where e.env = dv p in

  e ::= e1 p2   | dv p2 `subseteq` dv e.env && dv p2 != empty

    e1.env  = e.env
    e.vars  = e1.vars `union` dv p2!
    e.code  = let (r1, e1.vars) = e1.code in
              let (r2, p2!)     = r1 p2! in
                (r2, e.vars)

  e ::= e1 e2

    e1.env  = e2.env = e.env
    e.vars  = e1.vars `union` e2.vars
    e.code  = let (r1, e1.vars) = e1.code in
              let (r2, e2.vars) = e2.code in
                (r1 r2, e.vars)

  e ::= x       | x `member` dv p

    e.vars  = x!
    e.code  = (x!, ())

  e ::= v

    e.vars  = fv v `intersect` env
    e.code  = let e.vars = e.vars! in
              (v, [ () | _ <- e.vars ])

  e ::= match p0 with
        | p1 -> e1
        | ...
        | pk -> ek
                | dv p0 `subseteq` dv e.env && dv p0 != empty

    if p1 is a bang pattern
      then e1.env  = e.env `union` dv p1
      else e1.env  = e.env - (dv p1 - dv p0)
    ...
    if pk is a bang pattern
      then ek.env  = e.env `union` dv pk
      else ek.env  = e.env - (dv pk - dv p0)

    e.vars  = e.env `intersection` (e1.vars `union` ... `union` ek.vars)
    e.code  = match p0! with
              | p1[p0!/p0] -> let (p0 - p1)! = ((), ..., ()) in
                              let (r2, e1.vars) = e1.code in (r2, e.vars)
              | ...
        (if pk is not a bang pattern then)
              | pk[p0!/p0] -> let (p0 - pk)! = ((), ..., ()) in
                              let (r2, e1.vars) = e1.code in (r2, e.vars)
        (else)
              | pk!        -> let (p0 - pk)! = ((), ..., ()) in
                              let (r2, e1.vars) = e1.code in (r2, e.vars)

  e ::= match e0 with
        | p1 -> e1
        | ...
        | pk -> ek

    e0.env  = e.env
    e1.env  = e.env - dv p1
    ...
    ek.env  = e.env - dv pk

    e.vars  = e.env `intersection`
                (e0.vars `union` e1.vars `union` ... `union` ek.vars)
    e.code  = let (r1, e0.vars) = e0.code in
              match r1 with
              | p1 -> let (r2, e1.vars) = e1.code in (r2, e.vars)
              | ...
              | pk -> let (r2, ek.vars) = ek.code in (r2, e.vars)

  e ::= let rec f1 = v1
            and ...
            and fk = vk
         in e1

    captured = { x `in` (fv v1 `union` ... `union` fv vk)
               | x! `in` e.env }

    e1.env  = e.env - { f1, ..., fk }
    e.vars  = e1.vars `union` captured!
    e.code  = let captured  = captured! in
              let captured! = ((), ..., ()) in
              let rec f1 = v1
                  and ...
                  and fk = vk
               in let (r1, e1.vars) = e1.code
                   in (r1, e.vars)

  e ::= e1[t]

    e1.env  = e.env
    e.vars  = e1.vars
    e.code  = let (r1, e1.vars) = e1.code in
                (r1[t], e.vars)

  e ::= let !p1 = e1 in e2

    e1.env  = e.env
    e2.env  = e.env `union` dv p1
    e.vars  = e1.vars `union` (e2.vars `intersection` e.env)
    e.code  = let (p1!, e1.vars) = e1.code in
              let (r2,  e2.vars) = e2.code in
                ((r2, p1!), e.vars)
    [assuming no shadowing]
-}

transform :: Id i => S.Set (Lid i) -> Expr i -> ([Lid i], Expr i)
transform env = loop where
  capture e1
    | vars <- [ v | J [] v <- M.keys (fv e1),
                    v `S.member` env ],
      code <- translate paVar (exBVar . ren) vars .
              kill (ren vars)
        = Just (ren vars, code)
    | otherwise
        = Nothing

  unop kont (e1_vars, e1_code)
    | Just (k_vars, k_code) <- capture (kont exUnit),
      vars <- k_vars `L.union` e1_vars,
      code <- k_code $
              exLet' (paVar r1 -:: e1_vars) e1_code $
                (kont (exBVar r1) +:: vars)
      = (vars, code)
  unop kont ([],      e1_code)
      = ([], kont e1_code +:: [])
  unop kont (e1_vars, e1_code)
    | vars <- e1_vars,
      code <- exLet' (paPair (paVar r1) (paVar r2)) e1_code $
                exPair (kont (exBVar r1)) (exBVar r2)
      = (vars, code)

  binder kont (e1_vars, e1_code)
    | Just (k_vars, k_code) <- capture (kont exUnit),
      vars <- k_vars `L.union` e1_vars,
      code <- k_code $
              kont $
              exLet' (paVar r1 -:: e1_vars) e1_code $
              (exBVar r1 +:: vars)
      = (vars, code)
    | vars <- e1_vars,
      code <- kont e1_code
      = (vars, code)

  binop kont e1 e2 =
    case (loop e1, loop e2) of
      (([],      e1_code), ([],      e2_code))
          -> ([], kont e1_code e2_code +:: [])
      (([],      e1_code), (e2_vars, e2_code))
        | syntacticValue e1_code,
          vars <- e2_vars,
          code <- exLet' (paVar r2 -:: e2_vars) e2_code $
                    kont e1_code (exBVar r2) +:: vars
          -> (vars, code)
      ((e1_vars, e1_code), ([],      e2_code))
        | syntacticValue e2_code,
          vars <- e1_vars,
          code <- exLet' (paVar r1 -:: e1_vars) e1_code $
                  kont (exBVar r1) e2_code +:: vars
          -> (vars, code)
      ((e1_vars, e1_code), (e2_vars, e2_code))
        | vars <- e1_vars `L.union` e2_vars,
          code <- exLet' (paVar r1 -:: e1_vars) e1_code $
                  exLet' (paVar r2 -:: e2_vars) e2_code $
                    kont (exBVar r1) (exBVar r2) +:: vars
          -> (vars, code)

  shadow vs e = transform (env `S.difference` vs) e

  loop e  = let (vars, e') = loop' e in (vars, e' <<@ e)

  loop' e = case view e of
    ExId (J [] (Var x))
      | x `S.member` env,
        vars <- [ren x]
        -> (vars, ren (exBVar x) +:+ [exUnit])

    ExCase e0 bs
      | Just p0 <- expr2patt env S.empty e0,
        not (dv p0 `disjoint` env),
        e0_vars <- toList (dv (ren p0)),
        e0_code <- ren e0,
        bs'  <-
          [ case parseBangPatt pj of
              Nothing  ->
                (renOnly (dv p0) pj,
                 shadow (dv pj `S.difference` dv p0) ej)
              Just pj' ->
                (ren pj',
                 transform (env `S.union` dv pj) ej)
          | N _ (CaClause pj ej) <- bs ],
        vars <- [ v | v <- foldl L.union e0_vars (map (fst . snd) bs'),
                      v `S.member` ren env ],
        code <- exCase e0_code $
                  [ caClause pj (kill (dv (ren p0) `S.difference` dv pj) $
                         exLet' (paVar r1 -:: ej_vars) ej_code $
                           (exBVar r1 +:: vars))
                  | (pj, (ej_vars, ej_code)) <- bs' ]
        -> (vars, code)

      | (e0_vars, e0_code) <- loop e0,
        bs'  <-
          [ case parseBangPatt pj of
              Nothing  -> (pj, shadow (dv pj) ej)
              Just pj' -> exAddSigma
                            (length bs == 1)
                            (\vars patt expr -> (patt, (vars, expr)))
                            env pj' ej
          | N _ (CaClause pj ej) <- bs ],
        vars <- foldl L.union e0_vars (map (fst . snd) bs'),
        code <- exLet' (paVar r1 -:: e0_vars) e0_code $
                exCase (exBVar r1) $
                  [ caClause pj
                             (exLet' (paVar r2 -:: ej_vars) ej_code $
                                exBVar r2 +:: vars)
                  | (pj, (ej_vars, ej_code)) <- bs' ]
        -> (vars, code)

    ExLetRec bs e1
        -> binder (exLetRec bs)
             (shadow (S.fromList (map (bnvar . dataOf) bs)) e1)

    ExLetDecl ds e1
        -> binder (exLetDecl ds) (loop e1)

    ExPair e1 e2
        -> binop exPair e1 e2

    ExApp e1 e2
      | Just p2 <- expr2patt env S.empty e2,
        not (dv p2 `disjoint` env),
        (e1_vars, e1_code) <- loop e1,
        vars <- e1_vars `L.union` toList (dv (ren p2)),
        (v1, f1) <- if null e1_vars
                      then (e1_code, id)
                      else (exBVar r1,
                            exLet' (paVar r1 -:: e1_vars) e1_code),
        code <- f1 $
                exLet' (paPair (paVar r2) (flatpatt (ren p2)))
                       (exApp v1 (ren e2)) $
                exBVar r2 +:: vars
        -> (vars, code)

      | otherwise
        -> binop exApp e1 e2

    ExTApp e1 t2
        -> unop (flip exTApp t2) (loop e1)

    ExPack mt t1 e2
        -> unop (exPack mt t1) (loop e2)

    ExCast e1 t2 b
        -> unop (flip (flip exCast t2) b) (loop e1)

    _ | Just (k_vars, k_code) <- capture e
        -> (k_vars, k_code $ e +:: k_vars)

      | vars <- []
        -> (vars, e +:: vars)

(+:+)   :: Id i => Expr i -> [Expr i] -> Expr i
(+:+)    = foldl exPair

(+::)   :: Id i => Expr i -> [Lid i] -> Expr i
e +:: vs = e +:+ map exBVar vs

(-:-)   :: Id i => Patt i -> [Patt i] -> Patt i
(-:-)    = foldl paPair

(-::)   :: Id i => Patt i -> [Lid i] -> Patt i
p -:: vs = p -:- map paVar vs

r1, r2 :: Id i => Lid i
r1 = lid "r1.!"
r2 = lid "r2.!"

{-
expr2vs :: Expr i -> Maybe [Lid i]
expr2vs e = case view e of
  ExId (J [] (Var l)) -> return [l]
  ExPair e1 e2
    | ExId (J [] (Var l)) <- view e2 -> do
      vs <- expr2vs e1
      return (vs ++ [l])
  _ -> mzero
-}

makeBangPatt :: Id i => Patt i -> Patt i
makeBangPatt p = paCon (J [] (uid "!")) (Just p)

parseBangPatt :: Id i => Patt i -> Maybe (Patt i)
parseBangPatt (dataOf -> PaCon (J [] (Uid i "!")) mp)
  | isTrivial i = mp
parseBangPatt _ = Nothing

{-
fbvSet :: Expr i -> S.Set (Lid i)
fbvSet e = S.fromList [ lid | J [] lid <- M.keys (fv e) ]
-}

disjoint :: Ord a => S.Set a -> S.Set a -> Bool
disjoint s1 s2 = S.null (s1 `S.intersection` s2)

-- | Transform an expression into a pattern, if possible, using only
--   the specified variables and type variables
expr2patt :: Id i =>
             S.Set (Lid i) -> S.Set (TyVar i) -> Expr i -> Maybe (Patt i)
expr2patt vs0 tvs0 e0 = CMS.evalStateT (loop e0) (vs0, tvs0) where
  loop e = case view e of
    ExId ident -> case view ident of
      Left (J [] l)     -> do
        sawVar l
        return (paVar l)
      Left (J _ _)      -> mzero
      Right qu          -> return (paCon qu Nothing)
    -- no string or integer literals
    ExPair e1 e2        -> do
      p1 <- loop e1
      p2 <- loop e2
      return (paPair p1 p2)
    ExApp e1 e2 |
      ExId ident <- view (snd (unfoldExTApp e1)),
      Right qu <- view ident
                        -> do
        p2 <- loop e2
        return (paCon qu (Just p2))
    ExTApp e1 _         -> loop e1
    ExPack Nothing (dataOf -> TyVar tv) e2 -> do
      sawTyVar tv
      p2 <- loop e2
      return (paPack tv p2)
    _                   -> mzero

  sawVar v    = do
    (vs, tvs) <- CMS.get
    if v `S.member` vs
      then CMS.put (v `S.delete` vs, tvs)
      else mzero

  sawTyVar tv = do
    (vs, tvs) <- CMS.get
    if tv `S.member` tvs
      then CMS.put (vs, tv `S.delete` tvs)
      else mzero

-- | Transform a pattern to an expression.
patt2expr :: Id i => Patt i -> Expr i
patt2expr p = case dataOf p of
  PaWild         -> exUnit
  PaVar l        -> exBVar l
  PaCon u Nothing
                 -> exCon u
  PaCon u (Just p2)
                 -> exApp e1 e2 where
    e1 = patt2expr (paCon u Nothing)
    e2 = patt2expr p2
  PaPair p1 p2   -> exPair e1 e2 where
    e1 = patt2expr p1
    e2 = patt2expr p2
  PaLit lt       -> exLit lt
  PaAs _ l       -> exBVar l
  PaPack a p2    -> exPack Nothing (tyVar a) (patt2expr p2)
  PaAnti a       -> antierror "exSigma" a

-- | Transform a pattern to a flattened pattern.
flatpatt :: Id i => Patt i -> Patt i
flatpatt p0 = case loop p0 of
                []   -> paUnit
                p:ps -> foldl paPair p ps
  where
  loop p = case dataOf p of
    PaWild         -> []
    PaVar l        -> [paVar l]
    PaCon _ Nothing
                   -> []
    PaCon _ (Just p2)
                   -> loop p2
    PaPair p1 p2   -> loop p1 ++ loop p2
    PaLit _        -> []
    PaAs _ l       -> [paVar l]
    PaPack a p2    -> [paPack a (flatpatt p2)]
    PaAnti a       -> antierror "exSigma" a

ren :: Data a => a -> a
ren = everywhere (mkT eachRaw `extT` eachRen) where
  eachRaw :: Lid Raw -> Lid Raw
  eachRen :: Lid Renamed -> Lid Renamed
  eachRaw = each; eachRen = each
  each (Lid _ s)   = lid (s ++ "!")
  each (LidAnti a) = LidAnti a

renOnly :: (Data a, Id i) => S.Set (Lid i) -> a -> a
renOnly set = everywhere (mkT each) where
  each l | l `S.member` set = lid (unLid l ++ "!")
         | otherwise        = l

{-
remove :: Data a => S.Set Lid -> a -> a
remove set = everywhere (mkT expr `extT` patt) where
  patt (PaVar v)
    | v `S.member` set = paUnit
  patt p               = p
  expr :: Ident -> Ident
  expr (J [] (Var v))
    | v `S.member` set = J [] (Con (Uid "()"))
  expr e               = e
  -}

kill :: (Id i, Foldable f) => f (Lid i) -> Expr i -> Expr i
kill  = translate paVar (const exUnit)

translate :: (Id i, Foldable f) =>
             (Lid i -> Patt i) -> (Lid i -> Expr i) ->
             f (Lid i) -> Expr i -> Expr i
translate mkpatt mkexpr set =
  case toList set of
    []   -> id
    v:vs -> exLet' (mkpatt v -:- map mkpatt vs)
                   (mkexpr v +:+ map mkexpr vs)

exUnit :: Id i => Expr i
exUnit  = exCon (quid "()")

paUnit :: Id i => Patt i
paUnit  = paCon (quid "()") Nothing

