module Dynamics (
  -- Static API
  E, addVal, addMod, NewValues,
  -- Dynamic API
  eval, addDecls, Result
) where

import Value
import Util
import Syntax
import Env
import Ppr (Ppr(..), hang, text, char, (<>))

import Data.IORef (newIORef, readIORef, writeIORef)
import qualified Control.Exception as Exn

--
-- Our semantic domains
--

type Result   = IO Value

type E        = [Scope]
type Scope    = PEnv Uid VE
type VE       = Env Lid (IO Value)

type D        = E -> Result
type DDecl    = E -> IO E

(=:!=) :: Ord v => v -> a -> Env v (IO a)
(=:!=)  = (=::=)

infix 6 =:!=

--
-- Evaluation
--

evalDecls :: [Decl i] -> DDecl
evalDecls  = (flip . foldM . flip) evalDecl

evalDecl :: Decl i -> DDecl
evalDecl (DcLet _ m)    = evalLet m
evalDecl (DcTyp _ _)    = return
evalDecl (DcAbs _ _ ds) = evalDecls ds
evalDecl (DcOpn _ b)    = evalOpen b
evalDecl (DcMod _ n b)  = evalMod n b
evalDecl (DcLoc _ d0 d1)= evalLocal d0 d1
evalDecl (DcExn _ _)    = return

evalLet :: Let i -> DDecl
evalLet (LtC _ x _ e)   env = do
  v <- valOf e env
  return (env =+= x =:!= v)
evalLet (LtA _ x _ e)   env = do
  v <- valOf e env
  return (env =+= x =:!= v)
evalLet (LtInt _ x _ y) env = do
  case env =..= y of
    Just v  -> return (env =+= x =:= v)
    Nothing -> fail $ "BUG! Unknown variable: " ++ show y

evalOpen :: ModExp i -> DDecl
evalOpen b env = do
  e <- evalModExp b env
  return (env =+= e)

evalMod :: Uid -> ModExp i -> DDecl
evalMod x b env = do
  e <- evalModExp b env
  return (env =+= x =:= e)

evalLocal :: [Decl i] -> [Decl i] -> DDecl
evalLocal ds ds'  env0 = do
  env1          <- evalDecls ds (genEmpty:env0)
  scope:_:env2  <- evalDecls ds' (genEmpty:env1)
  return (env2 =+= scope)

evalModExp :: ModExp i -> E -> IO Scope
evalModExp (MeStrC _ ds) env = do
  scope:_ <- evalDecls ds (genEmpty:env)
  return scope
evalModExp (MeStrA _ ds) env = do
  scope:_ <- evalDecls ds (genEmpty:env)
  return scope
evalModExp (MeName n)   env = do
  case env =..= n of
    Just scope -> return scope
    Nothing    -> fail $ "BUG! Unknown module: " ++ show n

eval :: E -> Prog i -> Result
eval env0 (Prog ds (Just e0)) = evalDecls ds env0 >>= valOf e0
eval env0 (Prog ds Nothing  ) = evalDecls ds env0 >>  return (vinj ())

-- The meaning of an expression
valOf :: Expr i w -> D
valOf e env = case view e of
  ExId ident -> case view ident of
    Left x     -> case env =..= x of
      Just v     -> v
      Nothing    -> fail $ "BUG! unbound identifier: " ++ show x
    Right c    -> case getExnId e of
      Nothing -> return (VaCon (jname c) Nothing)
      Just ei -> makeExn ei (exprType e)
  ExStr s    -> return (vinj s)
  ExInt z    -> return (vinj z)
  ExFloat f  -> return (vinj f)
  ExCase e1 clauses -> do
    v1 <- valOf e1 env
    let loop ((xi, ei):rest) = case bindPatt xi v1 env of
          Just env' -> valOf ei env'
          Nothing   -> loop rest
        loop []              =
          Exn.throw VExn {
            exnId    = eiPatternMatch,
            exnParam = Just (vinj (show v1, map (show . fst) clauses))
          }
    loop clauses
  ExLetRec bs e2         -> do
    let extend (envI, rs) b = do
          r <- newIORef (fail "Accessed let rec binding too early")
          return (envI =+= bnvar b =:= join (readIORef r), r : rs)
    (env', rev_rs) <- foldM extend (env, []) bs
    zipWithM_
      (\r b -> do
         v <- valOf (bnexpr b) env'
         writeIORef r (return v))
      (reverse rev_rs)
      bs
    valOf e2 env'
  ExLetDecl d e2         -> do
    env' <- evalDecl d env
    valOf e2 env'
  ExPair e1 e2           -> do
    v1 <- valOf e1 env
    v2 <- valOf e2 env
    return (vinj (v1, v2))
  ExAbs x _ e'           ->
    return (VaFun (FNAnonymous (ppr e))
                  (\v -> bindPatt x v env >>= valOf e'))
  ExApp e1 e2            -> do
    v1  <- valOf e1 env
    v2  <- valOf e2 env
    v1' <- force v1  -- Magic type application
    case v1' of
      VaFun _ f -> f v2
      VaCon c _ -> return (VaCon c (Just v2))
      _         -> fail $ "BUG! applied non-function " ++ show v1
                           ++ " to argument " ++ show v2
  ExTAbs _ e'            ->
    return (VaSus (hang (text "#<sus") 4 $ ppr e <> char '>')
                  (valOf e' env))
  ExTApp e' _            -> do
    v' <- valOf e' env
    case v' of
      VaSus _ f -> f
      VaCon _ _ -> return v'
      _         -> fail $ "BUG! type-applied non-typefunction: " ++ show v'
  ExPack _ _ e1          ->
    valOf e1 env
  ExCast e1 _ _          ->
    valOf e1 env

makeExn :: Monad m => 
           ExnId -> Maybe (Either (TypeT C) (TypeT A)) -> m Value
makeExn _  Nothing   = fail $ "BUG! Cannot construct exception " ++
                               "because type checking was skipped"
makeExn ei (Just tt) = return $ either makeWith makeWith tt
  where
    makeWith (TyCon _ _ td) | td == tdExn =
      vinj (VExn ei Nothing)
    makeWith _ =
      VaFun (FNAnonymous (ppr (eiName ei))) $ \v ->
        return (vinj (VExn ei (Just v)))

bindPatt :: Monad m => Patt -> Value -> E -> m E
bindPatt x0 v env = case x0 of
  PaWild       -> return env
  PaVar lid    -> return (env =+= lid =:!= (lid `nameFun` v))
  PaCon uid mx Nothing -> case (mx, v) of
    (Nothing, VaCon uid' Nothing)   | uid == uid' -> return env
    (Just x,  VaCon uid' (Just v')) | uid == uid' -> bindPatt x v' env
    _                                             -> perr
  PaCon _ mx (Just ei) -> case (mx, vprjM v) of
    (Nothing, Just (VExn ei' Nothing  )) | ei == ei' -> return env
    (Just x,  Just (VExn ei' (Just v'))) | ei == ei' -> bindPatt x v' env
    _                                                -> perr
  PaPair x y   -> case vprjM v of
    Just (vx, vy) -> bindPatt x vx env >>= bindPatt y vy
    Nothing       -> perr
  PaStr s      -> if v == vinj s
                    then return env
                    else perr
  PaInt z      -> if v == vinj z
                    then return env
                    else perr
  PaPack _ x   -> bindPatt x v env
  PaAs x lid   -> do
    env' <- bindPatt x v env
    return (env' =+= lid =:!= v)
  where perr = fail $
                 "Pattern match failure: " ++ show x0 ++
                 " does not match " ++ show v

---
--- helpful stuff
---

force :: Value -> IO Value
force (VaSus _ v) = v >>= force
force v           = return v

-- Add the given name to an anonymous function
nameFun :: Lid -> Value -> Value
nameFun (Lid x) (VaFun (FNAnonymous _) lam)
  | x /= "it"          = VaFun (FNNamed [text x]) lam
nameFun _       value  = value

collapse :: E -> Scope
collapse = foldr (flip (=+=)) genEmpty

-- Public API

type NewValues = Env Lid Value

addDecls :: E -> [Decl i] -> IO (E, NewValues)
addDecls env decls = do
  env' <- evalDecls decls (genEmpty : [collapse env])
  let PEnv _ ve : _ = env'
  mapAccumM (\v e -> v >>= \w -> return (e, w)) env' ve

addVal :: E -> Lid -> Value -> E
addVal e n v     = e =+= n =:= (return v :: IO Value)

addMod :: E -> Uid -> E -> E
addMod e n e' = e =+= n =:= collapse e'

