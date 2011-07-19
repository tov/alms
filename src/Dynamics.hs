{-# LANGUAGE
      FlexibleInstances,
      MultiParamTypeClasses,
      QuasiQuotes,
      TemplateHaskell #-}
-- | The dynamics of the interpreter
module Dynamics (
  -- * Static API
  E, addVal, addMod, NewValues,
  -- * Dynamic API
  eval, addDecls, Result,
  -- * Re-export to remove warning (!)
  -- | We need to import Quasi for the TH phase, but using it at the
  --   TH phase isn't sufficient to prevent an unused import warning.
  module Meta.Quasi
) where

import Meta.Quasi
import Value
import Util
import AST
import Env
import Syntax.Ppr (Ppr(..), Doc, text, precApp)
import Error

import Prelude ()
import Data.IORef (newIORef, readIORef, writeIORef)

--
-- Our semantic domains
--

-- | The kind of identifiers used
type R        = Renamed

-- | The result of a computation
type Result   = IO Value

-- | The run-time environment is a stack of scopes which are, for our
--   purposes, abstract.  The interface merely allows us to bind new
--   values and modules in the top scope.
type E        = [Scope]
-- | Each scope binds paths of uppercase identifiers to flat value
--   and exn environments
type Scope    = PEnv (ModId R) Level
-- | A level binds values and exceptions
data Level    = Level {
                  vlevel :: !VE
                }
-- | We bind 'IO' 'Value's rather than values, so that we can use
-- 'IORef' to set up recursion
type VE       = Env (VarId R) (IO Value)

instance GenEmpty Level where
  genEmpty = Level Env.empty
instance GenLookup Level (VarId R) (IO Value) where
  level =..= k = vlevel level =..= k
instance GenExtend Level Level where
  Level ve =+= Level ve' = Level (ve =+= ve')
instance GenExtend Level (Env (VarId R) (IO Value)) where
  level =+= ve' = level =+= Level ve'

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

evalDecls :: [Decl R] -> DDecl
evalDecls  = (flip . foldM . flip) evalDecl

evalDecl :: Decl R -> DDecl
evalDecl [dc| let $x = $e |]                       = evalLet x e
evalDecl [dc| type $list:_ |]                      = return
evalDecl [dc| abstype $list:_ with $list:ds end |] = evalDecls ds
evalDecl [dc| open $b |]                           = evalOpen b
evalDecl [dc| module $mid:n = $b |]                = evalMod n b
evalDecl [dc| module type $sid:_ = $_ |]           = return
evalDecl [dc| local $list:d0 with $list:d1 end |]  = evalLocal d0 d1
evalDecl [dc| exception $cid:n of $opt:mt |]       = evalExn n mt
evalDecl [dc| $anti:a |]                           = $antifail

evalLet :: Patt R -> Expr R -> DDecl
evalLet x e env = do
  v <- valOf e env
  case bindPatt x v env of
    Just env' -> return env'
    Nothing   -> throwPatternMatch v [show x] env

evalOpen :: ModExp R -> DDecl
evalOpen b env = do
  e <- evalModExp b env
  return (env =+= e)

evalMod :: ModId R -> ModExp R -> DDecl
evalMod x b env = do
  e <- evalModExp b env
  return (env =+= x =:= e)

evalLocal :: [Decl R] -> [Decl R] -> DDecl
evalLocal ds ds'  env0 = do
  env1          <- evalDecls ds (genEmpty:env0)
  scope:_:env2  <- evalDecls ds' (genEmpty:env1)
  return (env2 =+= scope)

evalModExp :: ModExp R -> E -> IO Scope
evalModExp [meQ| struct $list:ds end |]  env = do
  scope:_ <- evalDecls ds (genEmpty:env)
  return scope
evalModExp [meQ| $qmid:n $list:_ |]      env = do
  case env =..= n of
    Just scope -> return scope
    Nothing    -> runtimeBug "evalModExp" $
      "Unknown module: ‘" ++ show n ++ "’"
evalModExp [meQ| $me1 : $_ |]            env = do
  evalModExp me1 env
evalModExp [meQ| $anti:a |]              _   = $antifail

evalExn :: ConId R -> Maybe (Type R) -> DDecl
evalExn _ _ env = return env

eval :: E -> Prog R -> Result
eval env0 [prQ| $list:ds in $e0 |] = evalDecls ds env0 >>= valOf e0
eval env0 [prQ| $list:ds        |] = evalDecls ds env0 >>  return (vinj ())

-- The meaning of an expression
valOf :: Expr R -> D
valOf e env = case e of
  [ex| $qvid:n |] -> case env =..= n of
      Just v     -> v
      Nothing    -> runtimeBug "valOf" $
        "unbound identifier: ‘" ++ show n ++ "’"
  [ex| $str:s |]    -> return (vinj s)
  [ex| $int:z |]    -> return (vinj z)
  [ex| $flo:f |]    -> return (vinj f)
  [ex| $char:c |]   -> return (vinj c)
  [ex| $antiL:a |]  -> $antifail
  [ex| $qcid:n $opt:me1 |]
                    -> do
    mv1 <- mapM (valOf <-> env) me1
    return (VaCon (jname n) mv1)
  [ex| `$uid:lab $opt:me1 |] -> do
    v1 <- maybe (return (vinj ())) (valOf <-> env) me1
    return (VaLab 0 lab v1)
  [ex| #$uid:lab $e1 |] -> do
    v1 <- valOf e1 env
    case v1 of
      VaLab n lab' v1' | lab == lab' -> return (VaLab (n + 1) lab v1')
      _                              -> return v1
  [ex| match $e1 with $list:clauses |] -> do
    let loop ([caQ| $xi → $ei |]:rest)                  v1 =
          case bindPatt xi v1 env of
            Just env' -> valOf ei env'
            Nothing   -> loop rest v1
        loop ([caQ| #$uid:lab $opt:mxi → $ei |]:rest)   v1 =
          case v1 of
            VaLab 0 lab' v1'
              | lab == lab'  -> case mxi of
                Nothing         -> valOf ei env
                Just xi         -> case bindPatt xi v1' env of
                  Just env'       -> valOf ei env'
                  Nothing         -> loop [] v1
            VaLab n lab' v1'
              | lab == lab'  -> loop rest (VaLab (n - 1) lab' v1')
            _                -> loop rest v1
        loop []                                         v1 =
          throwPatternMatch v1 (map (show . cafakepatt) clauses) env
        loop ([caQ| $antiC:a |]:_)                      _  = $antifail
    loop clauses =<< valOf e1 env
  [ex| let $x = $e1 in $e2 |]     -> do
    v1   <- valOf e1 env
    env' <- case bindPatt x v1 env of
      Just env' -> return env'
      Nothing   -> throwPatternMatch v1 [show x] env
    valOf e2 env'
  [ex| let rec $list:bs in $e2 |] -> do
    let extend (envI, rs) (N _ b) = do
          r <- newIORef $ throwBadLetRec (idName (bnvar b))
          return (envI =+= bnvar b =:= join (readIORef r), r : rs)
    (env', rev_rs) <- foldM extend (env, []) bs
    zipWithM_
      (\r (N _ b) -> do
         v <- valOf (bnexpr b) env'
         writeIORef r (return v))
      (reverse rev_rs)
      bs
    valOf e2 env'
  [ex| let $decl:d in $e2 |] -> do
    env' <- evalDecl d env
    valOf e2 env'
  [ex| ($e1, $e2) |] -> do
    v1 <- valOf e1 env
    v2 <- valOf e2 env
    return (vinj (v1, v2))
  [ex| fun $x -> $e' |] ->
    return .
      VaFun (FNAnonymous [pprPrec (precApp + 1) e]) $ \v ->
        case bindPatt x v env of
          Just env' -> valOf e' env'
          Nothing   -> throwPatternMatch v [show x] env
  [ex| $e1 $e2 |] -> do
    v1  <- valOf e1 env
    v2  <- valOf e2 env
    case v1 of
      VaFun n f -> f v2 >>! nameApp n (pprPrec (precApp + 1) v2) 
      VaCon c _ -> return (VaCon c (Just v2))
      _         -> runtimeBug "valOf" $
        "applied non-function ‘" ++ show v1 ++
        "’ to argument ‘" ++ show v2 ++ "’"
  [ex| ( $e1 : $_ ) |]           -> valOf e1 env
  [ex| ( $_ :> $_ ) |]           -> runtimeBug "valOf" $
      "TODO: Cast is unimplemented" -- XXX
  [ex| $anti:a |]                -> $antifail

bindPatt :: Monad m => Patt R -> Value -> E -> m E
bindPatt x0 v env = case x0 of
  [pa| _ |]
    -> return env
  [pa| $vid:l |]
    -> return (env =+= l =:!= (l `nameFun` v))
  [pa| $qcid:qu $opt:mx |]
    -> let u = jname qu in
       case (mx, v) of
      (Nothing, VaCon u' Nothing)   | u == u' -> return env
      (Just x,  VaCon u' (Just v')) | u == u' -> bindPatt x v' env
      _                                       -> perr
  [pa| `$uid:lab $opt:mx |]
    -> case v of
         VaLab 0 lab' v' | lab' == lab ->
             case mx of
              Nothing -> return env
              Just x  -> bindPatt x v' env
         _                             -> perr
  [pa| ($x, $y) |]
    -> case vprjM v of
      Just (vx, vy) -> bindPatt x vx env >>= bindPatt y vy
      Nothing       -> perr
  [pa| $str:s |]
    -> if v == vinj s
         then return env
         else perr
  [pa| $int:z |]
    -> if v == vinj z
         then return env
         else perr
  [pa| $float:f |]
    -> if v == vinj f
         then return env
         else perr
  [pa| $char:c |]
    -> if v == vinj c
         then return env
         else perr
  [pa| $x as $vid:l |]
    -> do
      env' <- bindPatt x v env
      return (env' =+= l =:!= v)
  [pa| $x : $_ |]
    -> bindPatt x v env
  [pa| ! $x |]
    -> bindPatt x v env
  [pa| $anti:a |]
    -> antifail "dynamics" a
  [pa| $antiL:a |]
    -> antifail "dynamics" a
  where perr = fail $
                 "BUG! In bindPat, pattern match failure should " ++
                 "raise PatternMatch exception, but didn’t!"

throwPatternMatch :: Value -> [String] -> E -> IO a
throwPatternMatch v ps _ =
  throw VExn {
    exnValue = VaCon (ident "PatternMatch") (Just (vinj (show v, ps)))
  }

throwBadLetRec :: String -> IO a
throwBadLetRec v =
  throw VExn {
    exnValue = VaCon (ident "UninitializedLetRec") (Just (vinj v))
  }

runtimeBug :: String -> String -> IO a
runtimeBug  = throwAlms <$$> almsBug DynamicsPhase

---
--- helpful stuff
---

-- Add the given name to an anonymous function
nameFun :: VarId R -> Value -> Value
nameFun n (VaFun (FNAnonymous _) lam)
  | idName n /= "it" || not (isTrivial (idTag n))
                 = VaFun (FNNamed (text (idName n))) lam
nameFun _ value  = value

-- Get the name of an applied function
nameApp :: FunName -> Doc -> Value -> Value
nameApp fn arg (VaFun (FNAnonymous _) lam)
  = VaFun (FNAnonymous (funNameDocs fn ++ [ arg ])) lam
nameApp _ _ value = value

collapse :: E -> Scope
collapse = foldr (flip (=+=)) genEmpty

-- Public API

-- | For printing in the REPL, 'addDecls' returns an environment
--   mapping any newly bound names to their values
type NewValues = Env (VarId R) Value

-- | Interpret declarations by adding to the environment, potentially
--   with side effects
addDecls :: E -> [Decl R] -> IO (E, NewValues)
addDecls env decls = do
  env' <- evalDecls decls (genEmpty : [collapse env])
  let PEnv _ level : _ = env'
  vl' <- mapValsM id (vlevel level)
  return (env', vl')

-- | Bind a name to a value
addVal :: E -> VarId R -> Value -> E
addVal e n v     = e =+= n =:= (return v :: IO Value)

-- | Bind a name to a module, which is represented as a nested
--   environment
addMod :: E -> ModId R -> E -> E
addMod e n e' = e =+= n =:= collapse e'

