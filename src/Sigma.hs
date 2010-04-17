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

-- | To lift a binder to bind effect variables rather than
--   normal variables.
exSigma :: Language w =>
           (Patt -> Expr () w -> a) ->
           Patt -> Expr () w -> a
exSigma binder patt body =
  let (b_vars, b_code) = transform (pv patt) body in
  binder (ren patt) $
  exLet' (PaVar r1 -:: b_vars) b_code $
  exPair (exBVar r1) (patt2expr (ren (flatpatt patt)))

-- | To lift a binder to bind effect variables rather than
--   normal variables.
exAddSigma :: Language w =>
              ([Lid] -> Patt -> Expr () w -> a) ->
              S.Set Lid -> Patt -> Expr () w -> a
exAddSigma binder env patt body =
  let env'             = pv patt
      (b_vars, b_code) = transform (env' `S.union` env) body
      vars = [ v | v <- b_vars, v `S.notMember` ren env' ]
   in binder vars (ren patt) $
      exLet' (PaVar r1 -:: b_vars) b_code $
      exPair (exBVar r1) (patt2expr (ren (flatpatt patt))) +:: vars

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

-- The pattern case:

  (p! is a renaming of p)

  fun !(p:t) -> e     ===   fun p:t -> [[ e ]](p)
  let !p = e1 in e2   ===   let y = e1 in [[ e ]](p)

  [[ e1 p2 ]](p)   | pv p2 `subseteq` pv p
                   = let (r1, p!)   = [[ e1 ]](p) in
                     let (r2, p2!) = r1 p2! in
                       (r2, p!)
  [[ e1 e2 ]](p)   = let (r1, y) = [[ e1 ]](p) in
                     let (r2, y) = [[ e2 ]](p) in
                       (r1 r2, y)
  [[ x ]](p)       | x `subseteq` pv p
                   = let p! = y in
                     (x!, p[()/x]!)
  [[ v ]](p)       = (v, y)
  [[ match e with
     | p1 -> e1
     | ...
     | pk -> ek ]](p)
              = let (r, y) = [[ e ]] in
                match r with
                | p1 -> [[ e1 ]](p)
                | ...
                | pk -> [[ ek ]](p)
  [[ e [t] ]] = let (r, y) = [[ e ]](p) in
                  (r [t], y)

  [[ slet p1 = e1 in e2 ]](p)
              = let (y1, y)       = [[ e1 ]](p) in
                let (r1, (y1, y)) = [[ e2 ]](p, p1) in
                  ((r1, y1), y)

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

  e ::= e1 p2   | pv p2 `subseteq` pv e.p && pv p2 != empty

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

  e ::= match e0 with
        | p1 -> e1
        | ...
        | pk -> ek

    e0.env  = e.env
    e1.env  = e.env - pv p1
    ...
    ek.env  = e.env - pv pk

    e.vars = e0.vars `union` e1.vars `union` ... `union` ek.vars
    e.code = let (r1, e0.vars) = e0.code in
             match r1 with
             | p1 -> let (r2, e1.vars) = e1.code in (r2, e.vars)
             | ...
             | pk -> let (r2, ek.vars) = ek.code in (r2, e.vars)

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
                ((r2, p1!), e.vars)
-}

transform :: Language w =>
              S.Set Lid -> Expr () w -> ([Lid], Expr () w)
transform env = loop where
  capture e1
    | v:vs <- [ v | J [] v <- M.keys (fv e1),
                    v `S.member` env ],
      patt <- PaVar v -:: vs,
      expr <- exUnit +:+ [ exUnit | _ <- vs ],
      vars <- ren (v:vs),
      code <- exLet' patt (patt2expr (ren patt)) .
              exLet' (ren patt) expr
        = Just (vars, code)
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
      | (e0_vars, e0_code) <- loop e0,
        bs'  <-
          [ case parseBangPatt pk of
              Nothing  -> (pk, shadow (pv pk) ek)
              Just pk' -> exAddSigma
                            (\vars patt expr -> (patt, (vars, expr)))
                            env pk' ek
          | (pk, ek) <- bs ],
        vars <- foldl L.union e0_vars (map (fst . snd) bs'),
        code <- exLet' (PaVar r1 -:: e0_vars) e0_code $
                exCase (exBVar r1) $
                  [ (pk, exLet' (PaVar r2 -:: ek_vars) ek_code $
                           (exBVar r2 +:: vars))
                  | (pk, (ek_vars, ek_code)) <- bs' ]
        -> (vars, code)

    ExLetRec bs e1
        -> unop (exLetRec bs) (shadow (S.fromList (map bnvar bs)) e1)

    ExLetDecl ds e1
        -> unop (exLetDecl ds) (loop e1)

    ExPair e1 e2
        -> binop exPair e1 e2

    ExApp e1 e2
      | Just p2 <- expr2patt env S.empty e2,
        not (pv p2 `disjoint` env),
        (e1_vars, e1_code) <- loop e1,
        vars <- e1_vars `L.union` S.toList (pv (ren p2)),
        code <- 
          if null e1_vars
            then exApp e1_code (ren e2)
            else exLet' (PaVar r1 -:: e1_vars) e1_code $
                 exLet' (PaPair (PaVar r2) (flatpatt (ren p2)))
                        (exApp (exBVar r1) (ren e2)) $
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

(+:+)   :: Expr () w -> [Expr () w] -> Expr () w
(+:+)    = foldl exPair

(+::)   :: Expr () w -> [Lid] -> Expr () w
e +:: vs = e +:+ map exBVar vs

(-:-)   :: Patt -> [Patt] -> Patt
(-:-)    = foldl PaPair

(-::)   :: Patt -> [Lid] -> Patt
p -:: vs = p -:- map PaVar vs

{-
exBang :: Language w =>
          (Patt -> Expr () w -> a) ->
          Patt -> Expr () w -> a
exBang binder patt body =
  binder (ren patt) $
  exLetVar' y (patt2expr (ren fp)) $
  exLet' (PaPair (PaVar r1) (ren fp)) (transform fp body) $
  exPair (exBVar r1) (patt2expr (ren patt))
  where fp = flatpatt patt

transform :: Language w => Patt -> Expr () w -> Expr () w
transform p = loop where
  vs     = pv p
  tvs    = ptv p
  loop e = (<<@ e) $ case view e of
    ExId (J [] (Var x))
      | x `S.member` vs
        -> exLet' (ren p) (exBVar y) $
             exPair (ren (exBVar x) <<@ e)
                    (patt2expr (ren (remove x p)))
    ExCase e1 [ (bp2, e2) ]
      | Just p2 <- parseBangPatt bp2
        -> exLet' (PaPair (PaVar y1) (PaVar y)) (loop e1) $
           exAddBang p (flip exLet' (exBVar y1)) p2 e2
    ExCase e1 bs
        -> r1 <-- e1 $ \v1 ->
           exCase v1 [ (pk, loop ek) | (pk, ek) <- bs ]
    ExLetRec bs e1
        -> exLetRec bs (loop e1)
    ExLetDecl ds e1
        -> exLetDecl ds (loop e1)
    ExPair e1 e2
        -> r1 <-- e1 $ \v1 ->
           r2 <-- e2 $ \v2 ->
           ret (exPair v1 v2)
    ExApp e1 e2
      | Just p2 <- expr2patt vs tvs e2,
        not (pv p2 `disjoint` vs)
        -> exLet' (PaPair (PaVar r1) (ren p)) (loop e1) $
           exLet' (PaPair (PaVar r2) (ren p2))
                  (exApp (exBVar r1) (ren e2) <<@ e) $
             exPair (exBVar r2) (patt2expr (ren p))
      | otherwise
        -> r1 <-- e1 $ \v1 ->
           r2 <-- e2 $ \v2 ->
           ret (exApp v1 v2)
    ExTApp e1 t2
        -> r1 <-- e1 $ \v1 ->
           ret (exTApp v1 t2)
    ExPack mt t1 e2
        -> r2 <-- e2 $ \v2 ->
           ret (exPack mt t1 v2)
    ExCast e1 mt t2
        -> r1 <-- e1 $ \v1 ->
           ret (exCast v1 mt t2)
    _   -> exPair e (exBVar y)
    where
      (r <-- e1) k =
        exLet' (PaPair (PaVar r) (PaVar y)) (loop e1) $
          (k (exBVar r) <<@ e)
      ret e1 = exPair e1 (exBVar y)
-}

r1, r2 :: Lid
r1 = Lid "r1.!"
r2 = Lid "r2.!"

{-
expr2vs :: Expr i w -> Maybe [Lid]
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
fbvSet :: Expr i w -> S.Set Lid
fbvSet e = S.fromList [ lid | J [] lid <- M.keys (fv e) ]
-}

disjoint :: Ord a => S.Set a -> S.Set a -> Bool
disjoint s1 s2 = S.null (s1 `S.intersection` s2)

-- | Transform an expression into a pattern, if possible, using only
--   the specified variables and type variables
expr2patt :: S.Set Lid -> S.Set TyVar -> Expr i w -> Maybe Patt
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
patt2expr :: Patt -> Expr i w
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

{-
renOnly :: Data a => S.Set Lid -> a -> a
renOnly set = everywhere (mkT each) where
  each l | l `S.member` set = Lid (unLid l ++ "!")
         | otherwise        = l

remove :: Lid -> Patt -> Patt
remove v = everywhere (mkT each) where
  each (PaVar v')
    | v == v'   = paUnit
  each p        = p
-}

exUnit :: Expr i w
exUnit  = exBCon (Uid "()")

paUnit :: Patt
paUnit  = PaCon (Uid "()") Nothing Nothing
