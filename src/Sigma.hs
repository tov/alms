{-# LANGUAGE
      GeneralizedNewtypeDeriving,
      PatternGuards #-}
module Sigma (
  makeBangPatt, parseBangPatt,
  exBang, exSigma, exSLet
) where

import Util
import Loc
import Syntax

import qualified Control.Monad.State as CMS
import Data.Generics (Data, everywhere, mkT)
import qualified Data.Set as S
-- import qualified Data.Map as M

-- | To lift a binder to bind effect variables rather than
--   normal variables.
exBang :: Language w =>
          (Patt -> Expr () w -> a) ->
          Patt -> Expr () w -> a
exBang binder patt body =
  binder (ren patt) $
  exLetVar' y (patt2expr (ren fp)) $
  exLet' (PaPair (PaVar r1) (ren fp)) (transform fp body) $
  exPair (exBVar r1) (patt2expr (ren patt))
  where fp = flatpatt patt

-- | To lift a binder to bind effect variables rather than
--   normal variables.
exAddBang :: Language w =>
          Patt ->
          (Patt -> Expr () w -> a) ->
          Patt -> Expr () w -> a
exAddBang env binder patt body =
  binder (ren patt) $
  exLetVar' y (exPair (exBVar y) (patt2expr (ren fp))) $
  exLet' (PaPair (PaVar r1) (PaPair (PaVar y) (ren fp)))
         (transform patt' body) $
  exPair (exPair (exBVar r1) (patt2expr (ren patt))) (exBVar y)
  where fp    = flatpatt patt
        patt' = PaPair (renOnly (pv fp) env) fp

-- | Make a lifted function
exSigma :: Language w => Patt -> Type () w -> Expr () w -> Expr () w
exSigma p t e  = exBang (flip exAbs' t) p e

-- | Make a lifted let
exSLet  :: Language w => Patt -> Expr () w -> Expr () w -> Expr () w
exSLet p e1 e2 = exBang (flip exLet' e1) p e2

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
-}

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

y, y1, r1, r2 :: Lid
y  = Lid "s.!"
y1 = Lid "s1.!"
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
patt2expr PaWild         = exCon (quid "()")
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
                []   -> PaCon (Uid "()") Nothing Nothing
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

remove :: Lid -> Patt -> Patt
remove v = everywhere (mkT each) where
  each (PaVar v')
    | v == v'   = PaCon (Uid "()") Nothing Nothing
  each p        = p

