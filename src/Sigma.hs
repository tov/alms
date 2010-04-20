{-# OPTIONS_GHC -fno-warn-unused-imports #-}
{-# LANGUAGE
      GeneralizedNewtypeDeriving,
      PatternGuards #-}
module Sigma (
  makeBangPatt, parseBangPatt, exSigma
) where

import Util
import Loc
import Syntax

import qualified Control.Monad.State as CMS
import Data.Generics (Data, everywhere, mkT)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Foldable (Foldable, toList)

-- | To lift a binder to bind effect variables rather than
--   normal variables.  (Boolean specifies whether the result
--   should include the effect variables.)
exSigma :: Bool ->
           (Patt -> Expr () -> a) ->
           Patt -> Expr () -> a
exSigma ret binder patt body =
  let (b_vars, b_code) = transform (pv patt) body in
  binder (ren patt) $
  exLet' (PaVar r1 -:: b_vars) b_code $
  if ret
    then exPair (exBVar r1) (patt2expr (ren (flatpatt patt)))
    else exBVar r1

-- | To lift a binder to bind effect variables rather than
--   normal variables.
exAddSigma :: Bool ->
              ([Lid] -> Patt -> Expr () -> a) ->
              S.Set Lid -> Patt -> Expr () -> a
exAddSigma ret binder env patt body =
  let env'             = pv patt
      (b_vars, b_code) = transform (env' `S.union` env) body
      vars = [ v | v <- b_vars, v `S.notMember` ren env' ]
   in binder vars (ren patt) $
      exLet' (PaVar r1 -:: b_vars) b_code $
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
                            where e.env = pv p in
  let !p = e1 in e2   ===   let p! = e1 in
                            let (r1, e.vars) = e.code
                             in (r1, p!)
                            where e.env = pv p in

  e ::= e1 p2   | pv p2 `subseteq` pv e.env && pv p2 != empty

    e1.env  = e.env
    e.vars  = e1.vars `union` pv p2!
    e.code  = let (r1, e1.vars) = e1.code in
              let (r2, p2!)     = r1 p2! in
                (r2, e.vars)

  e ::= e1 e2

    e1.env  = e2.env = e.env
    e.vars  = e1.vars `union` e2.vars
    e.code  = let (r1, e1.vars) = e1.code in
              let (r2, e2.vars) = e2.code in
                (r1 r2, e.vars)

  e ::= x       | x `member` pv p

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
                | pv p0 `subseteq` pv e.env && pv p0 != empty

    if p1 is a bang pattern
      then e1.env  = e.env `union` pv p1
      else e1.env  = e.env - (pv p1 - pv p0)
    ...
    if pk is a bang pattern
      then ek.env  = e.env `union` pv pk
      else ek.env  = e.env - (pv pk - pv p0)

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
    e1.env  = e.env - pv p1
    ...
    ek.env  = e.env - pv pk

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
    e2.env  = e.env `union` pv p1
    e.vars  = e1.vars
    e.code  = let (p1!, e1.vars) = e1.code in
              let (r2,  e2.vars) = e2.code in
                (r2, e.vars)
-}

transform :: S.Set Lid -> Expr () -> ([Lid], Expr ())
transform env = loop where
  capture e1
    | vars <- [ v | J [] v <- M.keys (fv e1),
                    v `S.member` env ],
      code <- translate PaVar (exBVar . ren) vars .
              kill (ren vars)
        = Just (ren vars, code)
    | otherwise
        = Nothing

  unop kont (e1_vars, e1_code)
    | Just (k_vars, k_code) <- capture (kont exUnit),
      vars <- k_vars `L.union` e1_vars,
      code <- k_code $
              exLet' (PaVar r1 -:: e1_vars) e1_code $
                (kont (exBVar r1) +:: vars)
      = (vars, code)
  unop kont ([],      e1_code)
      = ([], kont e1_code +:: [])
  unop kont (e1_vars, e1_code)
    | vars <- e1_vars,
      code <- exLet' (PaPair (PaVar r1) (PaVar r2)) e1_code $
                exPair (kont (exBVar r1)) (exBVar r2)
      = (vars, code)

  binder kont (e1_vars, e1_code)
    | Just (k_vars, k_code) <- capture (kont exUnit),
      vars <- k_vars `L.union` e1_vars,
      code <- k_code $
              kont $
              exLet' (PaVar r1 -:: e1_vars) e1_code $
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
          code <- exLet' (PaVar r2 -:: e2_vars) e2_code $
                    kont e1_code (exBVar r2) +:: vars
          -> (vars, code)
      ((e1_vars, e1_code), ([],      e2_code))
        | syntacticValue e2_code,
          vars <- e1_vars,
          code <- exLet' (PaVar r1 -:: e1_vars) e1_code $
                  kont (exBVar r1) e2_code +:: vars
          -> (vars, code)
      ((e1_vars, e1_code), (e2_vars, e2_code))
        | vars <- e1_vars `L.union` e2_vars,
          code <- exLet' (PaVar r1 -:: e1_vars) e1_code $
                  exLet' (PaVar r2 -:: e2_vars) e2_code $
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
        not (pv p0 `disjoint` env),
        e0_vars <- toList (pv (ren p0)),
        e0_code <- ren e0,
        bs'  <-
          [ case parseBangPatt pj of
              Nothing  ->
                (renOnly (pv p0) pj,
                 shadow (pv pj `S.difference` pv p0) ej)
              Just pj' ->
                (ren pj',
                 transform (env `S.union` pv pj) ej)
          | (pj, ej) <- bs ],
        vars <- [ v | v <- foldl L.union e0_vars (map (fst . snd) bs'),
                      v `S.member` ren env ],
        code <- exCase e0_code $
                  [ (pj, kill (pv (ren p0) `S.difference` pv pj) $
                         exLet' (PaVar r1 -:: ej_vars) ej_code $
                           (exBVar r1 +:: vars))
                  | (pj, (ej_vars, ej_code)) <- bs' ]
        -> (vars, code)

      | (e0_vars, e0_code) <- loop e0,
        bs'  <-
          [ case parseBangPatt pj of
              Nothing  -> (pj, shadow (pv pj) ej)
              Just pj' -> exAddSigma
                            (length bs == 1)
                            (\vars patt expr -> (patt, (vars, expr)))
                            env pj' ej
          | (pj, ej) <- bs ],
        vars <- foldl L.union e0_vars (map (fst . snd) bs'),
        code <- exLet' (PaVar r1 -:: e0_vars) e0_code $
                exCase (exBVar r1) $
                  [ (pj, exLet' (PaVar r2 -:: ej_vars) ej_code $
                           (exBVar r2 +:: vars))
                  | (pj, (ej_vars, ej_code)) <- bs' ]
        -> (vars, code)

    ExLetRec bs e1
        -> binder (exLetRec bs) (shadow (S.fromList (map bnvar bs)) e1)

    ExLetDecl ds e1
        -> binder (exLetDecl ds) (loop e1)

    ExPair e1 e2
        -> binop exPair e1 e2

    ExApp e1 e2
      | Just p2 <- expr2patt env S.empty e2,
        not (pv p2 `disjoint` env),
        (e1_vars, e1_code) <- loop e1,
        vars <- e1_vars `L.union` toList (pv (ren p2)),
        (v1, f1) <- if null e1_vars
                      then (e1_code, id)
                      else (exBVar r1,
                            exLet' (PaVar r1 -:: e1_vars) e1_code),
        code <- f1 $
                exLet' (PaPair (PaVar r2) (flatpatt (ren p2)))
                       (exApp v1 (ren e2)) $
                exBVar r2 +:: vars
        -> (vars, code)

      | otherwise
        -> binop exApp e1 e2

    ExTApp e1 t2
        -> unop (flip exTApp t2) (loop e1)

    ExPack mt t1 e2
        -> unop (exPack mt t1) (loop e2)

    ExCast e1 mt t2
        -> unop (flip (flip exCast mt) t2) (loop e1)

    _ | Just (k_vars, k_code) <- capture e
        -> (k_vars, k_code $ e +:: k_vars)

      | vars <- []
        -> (vars, e +:: vars)

(+:+)   :: Expr () -> [Expr ()] -> Expr ()
(+:+)    = foldl exPair

(+::)   :: Expr () -> [Lid] -> Expr ()
e +:: vs = e +:+ map exBVar vs

(-:-)   :: Patt -> [Patt] -> Patt
(-:-)    = foldl PaPair

(-::)   :: Patt -> [Lid] -> Patt
p -:: vs = p -:- map PaVar vs

r1, r2 :: Lid
r1 = Lid "r1.!"
r2 = Lid "r2.!"

{-
expr2vs :: Expr i -> Maybe [Lid]
expr2vs e = case view e of
  ExId (J [] (Var l)) -> return [l]
  ExPair e1 e2
    | ExId (J [] (Var l)) <- view e2 -> do
      vs <- expr2vs e1
      return (vs ++ [l])
  _ -> mzero
-}

makeBangPatt :: Patt -> Patt
makeBangPatt p = PaCon (Uid "!") (Just p) Nothing

parseBangPatt :: Patt -> Maybe Patt
parseBangPatt (PaCon (Uid "!") mp Nothing) = mp
parseBangPatt _                            = Nothing

{-
fbvSet :: Expr i -> S.Set Lid
fbvSet e = S.fromList [ lid | J [] lid <- M.keys (fv e) ]
-}

disjoint :: Ord a => S.Set a -> S.Set a -> Bool
disjoint s1 s2 = S.null (s1 `S.intersection` s2)

-- | Transform an expression into a pattern, if possible, using only
--   the specified variables and type variables
expr2patt :: S.Set Lid -> S.Set TyVar -> Expr i -> Maybe Patt
expr2patt vs0 tvs0 e0 = CMS.evalStateT (loop e0) (vs0, tvs0) where
  loop e = case view e of
    ExId (J [] (Var l)) -> do
      sawVar l
      return (PaVar l)
    ExId (J [] (Con u)) -> return (PaCon u Nothing (getExnId e))
    -- no string or integer literals
    ExPair e1 e2        -> do
      p1 <- loop e1
      p2 <- loop e2
      return (PaPair p1 p2)
    ExApp e1 e2 |
      ExId (J [] (Con l)) <- view (snd (unfoldExTApp e1))
                        -> do
        p2 <- loop e2
        return (PaCon l (Just p2) (getExnId e1))
    ExTApp e1 _          -> loop e1
    ExPack Nothing (TyVar tv) e2 -> do
      sawTyVar tv
      p2 <- loop e2
      return (PaPack tv p2)
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
patt2expr :: Patt -> Expr i
patt2expr PaWild         = exUnit
patt2expr (PaVar l)      = exBVar l
patt2expr (PaCon u Nothing exn)
                         = exBCon u `setExnId` exn
patt2expr (PaCon u (Just p) exn)
                         = exApp e1 e2 where
  e1 = patt2expr (PaCon u Nothing exn)
  e2 = patt2expr p
patt2expr (PaPair p1 p2) = exPair e1 e2 where
  e1 = patt2expr p1
  e2 = patt2expr p2
patt2expr (PaStr s)      = exStr s
patt2expr (PaInt z)      = exInt z
patt2expr (PaAs _ l)     = exBVar l
patt2expr (PaPack a p)   = exPack Nothing (TyVar a) (patt2expr p)

-- | Transform a pattern to a flattened pattern.
flatpatt :: Patt -> Patt
flatpatt p0 = case loop p0 of
                []   -> paUnit
                p:ps -> foldl PaPair p ps
  where
  loop PaWild         = []
  loop (PaVar l)      = [PaVar l]
  loop (PaCon _ Nothing _)
                      = []
  loop (PaCon _ (Just p) _)
                      = loop p
  loop (PaPair p1 p2) = loop p1 ++ loop p2
  loop (PaStr _)      = []
  loop (PaInt _)      = []
  loop (PaAs _ l)     = [PaVar l]
  loop (PaPack a p)   = [PaPack a (flatpatt p)]

ren :: Data a => a -> a
ren = everywhere (mkT each) where
  each (Lid s) = Lid (s ++ "!")

renOnly :: Data a => S.Set Lid -> a -> a
renOnly set = everywhere (mkT each) where
  each l | l `S.member` set = Lid (unLid l ++ "!")
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

kill :: Foldable f => f Lid -> Expr () -> Expr ()
kill  = translate PaVar (const exUnit)

translate :: Foldable f =>
             (Lid -> Patt) -> (Lid -> Expr ()) ->
             f Lid -> Expr () -> Expr ()
translate mkpatt mkexpr set =
  case toList set of
    []   -> id
    v:vs -> exLet' (mkpatt v -:- map mkpatt vs)
                   (mkexpr v +:+ map mkexpr vs)

exUnit :: Expr i
exUnit  = exBCon (Uid "()")

paUnit :: Patt
paUnit  = PaCon (Uid "()") Nothing Nothing

