{-# LANGUAGE
      FlexibleInstances,
      MultiParamTypeClasses,
      QuasiQuotes #-}
-- | The dynamics of the interpreter
module Dynamics (
  -- * Static API
  E, addVal, addMod, addExn, NewValues,
  -- * Dynamic API
  eval, addDecls, Result,
  -- * Re-export to remove warning (!)
  -- | We need to import Quasi for the TH phase, but using it at the
  --   TH phase isn't sufficient to prevent an unused import warning.
  module Quasi
) where

import Quasi
import Value
import Util
import Syntax
import Env
import Ppr (Ppr(..), Doc, text, precApp, brackets)

import Data.IORef (newIORef, readIORef, writeIORef)
import Control.Exception (throw)

--
-- Our semantic domains
--

-- | The result of a computation
type Result   = IO Value

-- | The run-time environment is a stack of scopes which are, for our
--   purposes, abstract.  The interface merely allows us to bind new
--   values and modules in the top scope.
type E        = [Scope]
-- | Each scope binds paths of uppercase identifiers to flat value
--   and exn environments
type Scope    = PEnv Uid Level
-- | A level binds values and exceptions
data Level    = Level {
                  vlevel :: VE,
                  xlevel :: XE
                }
-- | We bind 'IO' 'Value's rather than values, so that we can use
-- 'IORef' to set up recursion
type VE       = Env Lid (IO Value)
-- | We associate exception names with their identity, since new
--   kinds of exceptions may be generated at run time.
type XE       = Env ExnName ExnId

-- | To distinguish exn names from path components.
newtype ExnName = ExnName Uid
  deriving (Eq, Ord)

instance GenEmpty Level where
  genEmpty = Level empty empty
instance GenLookup Level Lid (IO Value) where
  level =..= k = vlevel level =..= k
instance GenLookup Level ExnName ExnId where
  level =..= k = xlevel level =..= k
instance GenExtend Level Level where
  Level ve xe =+= Level ve' xe' = Level (ve =+= ve') (xe =+= xe')
instance GenExtend Level (Env Lid (IO Value)) where
  level =+= ve' = level =+= Level ve' empty
instance GenExtend Level (Env ExnName ExnId) where
  level =+= xe' = level =+= Level empty xe'

-- | Domain for the meaning of an expression:
type D        = E -> Result
-- | Domain for the meaning of a declaration:
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
evalDecl (DcLet _ x _ e) = evalLet x e
evalDecl (DcTyp _ _)     = return
evalDecl (DcAbs _ _ ds)  = evalDecls ds
evalDecl (DcOpn _ b)     = evalOpen b
evalDecl (DcMod _ n b)   = evalMod n b
evalDecl (DcLoc _ d0 d1) = evalLocal d0 d1
evalDecl (DcExn _ n mt)  = evalExn n mt

evalLet :: Patt -> Expr i -> DDecl
evalLet x e env = do
  v <- valOf e env
  case bindPatt x v env of
    Just env' -> return env'
    Nothing   -> throwPatternMatch v [show x] env

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
evalModExp (MeStr ds)   env = do
  scope:_ <- evalDecls ds (genEmpty:env)
  return scope
evalModExp (MeName n)   env = do
  case env =..= n of
    Just scope -> return scope
    Nothing    -> fail $ "BUG! Unknown module: " ++ show n

evalExn :: Uid -> Maybe (Type i) -> DDecl
evalExn u mt env = do
  case env =..= qlid "INTERNALS.Exn.exceptionIdCounter" of
    Just entry -> do
      VaFun _ f <- entry
      ix <- f vaUnit >>= vprjM
      return (addExn env (ExnId ix u mt))
    _ -> fail $ "BUG! Can't create new exception ID for: " ++ show u

eval :: E -> Prog i -> Result
eval env0 (Prog ds (Just e0)) = evalDecls ds env0 >>= valOf e0
eval env0 (Prog ds Nothing  ) = evalDecls ds env0 >>  return (vinj ())

-- The meaning of an expression
valOf :: Expr i -> D
valOf e env = case view e of
  ExId ident -> case view ident of
    Left x     -> case env =..= x of
      Just v     -> v
      Nothing    -> fail $ "BUG! unbound identifier: " ++ show x
    Right c    -> case isExn e of
      True  -> makeExn env c
      False -> return (VaCon (jname c) Nothing)
  ExLit lt   -> case lt of
    LtStr s   -> return (vinj s)
    LtInt z   -> return (vinj z)
    LtFloat f -> return (vinj f)
  ExCase e1 clauses -> do
    v1 <- valOf e1 env
    let loop ((xi, ei):rest) = case bindPatt xi v1 env of
          Just env' -> valOf ei env'
          Nothing   -> loop rest
        loop [] = throwPatternMatch v1 (map (show . fst) clauses) env
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
    return (VaFun (FNAnonymous [pprPrec (precApp + 1) e])
                  (\v -> bindPatt x v env >>= valOf e'))
  ExApp e1 e2            -> do
    v1  <- valOf e1 env
    v2  <- valOf e2 env
    v1' <- force v1  -- Magic type application
    case v1' of
      VaFun n f -> f v2 >>! nameApp n (pprPrec (precApp + 1) v2) 
      VaCon c _ -> return (VaCon c (Just v2))
      _         -> fail $ "BUG! applied non-function " ++ show v1
                           ++ " to argument " ++ show v2
  ExTAbs _ e'            ->
    return (VaSus (FNAnonymous [ppr e]) (valOf e' env))
  ExTApp e' t2           -> do
    v' <- valOf e' env
    case v' of
      VaSus n f -> f >>! nameApp n (brackets (ppr t2))
      VaCon _ _ -> return v'
      _         -> fail $ "BUG! type-applied non-typefunction: " ++ show v'
  ExPack _ _ e1          ->
    valOf e1 env
  ExCast e1 _ _          ->
    valOf e1 env
  ExAnti a               ->
    antifail "dynamics" a

makeExn :: Monad m => E -> QUid -> m Value
makeExn env c = do
  ei <- getExnId env c
  return $ case ei of
    ExnId { eiParam = Nothing }
      -> vinj (VExn ei Nothing)
    _ -> VaFun (FNAnonymous [ppr (eiName ei)]) $ \v ->
           return (vinj (VExn ei (Just v)))

getExnId :: Monad m => E -> QUid -> m ExnId
getExnId env c = case env =..= ExnName `fmap` c of
  Nothing -> fail $ "BUG! could not lookup exception: " ++ show c
  Just ei -> return ei

bindPatt :: Monad m => Patt -> Value -> E -> m E
bindPatt x0 v env = case x0 of
  [$pa| _ |] 
    -> return env
  [$pa| $lid:lid |]
    -> return (env =+= lid =:!= (lid `nameFun` v))
  PaCon (J _ uid) mx False
    -> case (mx, v) of
      (Nothing, VaCon uid' Nothing)   | uid == uid' -> return env
      (Just x,  VaCon uid' (Just v')) | uid == uid' -> bindPatt x v' env
      _                                             -> perr
  PaCon qu mx True
    -> do
      ei <- getExnId env qu
      case (mx, vprjM v) of
        (Nothing, Just (VExn ei' Nothing  )) | ei == ei' -> return env
        (Just x,  Just (VExn ei' (Just v'))) | ei == ei' -> bindPatt x v' env
        _                                                -> perr
  [$pa| ($x, $y) |]
    -> case vprjM v of
      Just (vx, vy) -> bindPatt x vx env >>= bindPatt y vy
      Nothing       -> perr
  [$pa| $str:s |]
    -> if v == vinj s
         then return env
         else perr
  [$pa| $int:z |]
    -> if v == vinj z
         then return env
         else perr
  [$pa| $float:f |]
    -> if v == vinj f
         then return env
         else perr
  PaPack _ x
    -> bindPatt x v env
  PaAs x lid
    -> do
      env' <- bindPatt x v env
      return (env' =+= lid =:!= v)
  [$pa| $anti:anti |]
    -> antifail "dynamics" anti
  where perr = fail $
                 "Pattern match failure: " ++ show x0 ++
                 " does not match " ++ show v

throwPatternMatch :: Value -> [String] -> E -> IO a
throwPatternMatch v ps env = do
  ei <- getExnId env (quid "INTERNALS.Exn.PatternMatch")
  throw VExn {
    exnId    = ei,
    exnParam = Just (vinj (show v, ps))
  }

---
--- helpful stuff
---

force :: Value -> IO Value
force (VaSus n v) = v >>= force . nameApp n (text "[_]")
force v           = return v

-- Add the given name to an anonymous function
nameFun :: Lid -> Value -> Value
nameFun (Lid x) (VaFun (FNAnonymous _) lam)
  | x /= "it"          = VaFun (FNNamed (text x)) lam
nameFun (Lid x) (VaSus (FNAnonymous _) lam)
  | x /= "it"          = VaSus (FNNamed (text x)) lam
nameFun _       value  = value

-- Get the name of an applied function
nameApp :: FunName -> Doc -> Value -> Value
nameApp fn arg (VaFun (FNAnonymous _) lam)
  = VaFun (FNAnonymous (funNameDocs fn ++ [ arg ])) lam
nameApp fn arg (VaSus (FNAnonymous _) lam)
  = VaSus (FNAnonymous (funNameDocs fn ++ [ arg ])) lam
nameApp _ _ value = value

collapse :: E -> Scope
collapse = foldr (flip (=+=)) genEmpty

-- Public API

-- | For printing in the REPL, 'addDecls' returns an environment
--   mapping any newly bound names to their values
type NewValues = (Env Lid Value, [ExnId])

-- | Interpret declarations by adding to the environment, potentially
--   with side effects
addDecls :: E -> [Decl i] -> IO (E, NewValues)
addDecls env decls = do
  env' <- evalDecls decls (genEmpty : [collapse env])
  let PEnv _ level : _ = env'
  vl' <- mapValsM id (vlevel level)
  return (env', (vl', range (xlevel level)))

-- | Bind a name to a value
addVal :: E -> Lid -> Value -> E
addVal e n v     = e =+= n =:= (return v :: IO Value)

-- | Bind a name to a module, which is represented as a nested
--   environment
addMod :: E -> Uid -> E -> E
addMod e n e' = e =+= n =:= collapse e'

-- | To register an exception ID.
addExn :: E -> ExnId -> E
addExn env exnid = env =+= ExnName (eiName exnid) =:= exnid

