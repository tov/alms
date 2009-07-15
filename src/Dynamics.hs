{-# LANGUAGE
      ExistentialQuantification,
      DeriveDataTypeable
    #-}
module Dynamics (
  E, Result,
  eval, evalDecls,
  Valuable(..),
  FunName(..), Value(..), vaInt, vaUnit
) where

import Util
import Syntax
import Env
import Ppr (Doc, text, Ppr(..), hang, sep, char, (<>), (<+>),
            parensIf, precCom, precApp)

import Data.Typeable (Typeable, cast)
import Data.IORef (newIORef, readIORef, writeIORef)

-- We represent function names in a way that makes pretty-printing
-- them nicer
data FunName = FNAnonymous Doc
             | FNNamed [Doc]

class Typeable a => Valuable a where
  veq          :: a -> a -> Bool
  veq _ _       = False

  veqDyn       :: Valuable b => a -> b -> Bool
  veqDyn a b    = maybe False (veq a) (vcast b)

  vpprPrec     :: Int -> a -> Doc
  vpprPrec _ _  = text "#<->"

  vppr         :: a -> Doc
  vppr          = vpprPrec 0

  vinj         :: a -> Value
  vinj a        = case cast a of
                    Just v  -> v
                    Nothing -> VaDyn a

  vprjM        :: Monad m => Value -> m a
  vprjM         = vcast

  vprj         :: Value -> a
  vprj          = maybe (error "BUG! vprj: coercion error") id . vprjM

  vpprPrecList :: Int -> [a] -> Doc
  vpprPrecList _ []     = text "nil"
  vpprPrecList p (x:xs) = parensIf (p > precApp) $
                            hang (text "cons" <+>
                                  vpprPrec (precApp + 1) x)
                                 1
                                 (vpprPrecList (precApp + 1) xs)

  vinjList     :: [a] -> Value
  vinjList []     = VaCon (Uid "Nil") Nothing
  vinjList (x:xs) = VaCon (Uid "Cons") (Just (vinj (x, xs)))

  vprjListM    :: Monad m => Value -> m [a]
  vprjListM (VaCon (Uid "Nil") Nothing) = return []
  vprjListM (VaCon (Uid "Cons") (Just v)) = do
    (x, xs) <- vprjM v
    return (x:xs)
  vprjListM _ = fail "vprjM: not a list"

vcast :: (Typeable a, Typeable b, Monad m) => a -> m b
vcast a = case cast a of
            Just r  -> return r
            Nothing -> case cast a of
              Just (VaDyn r) -> vcast r
              _              -> fail "BUG! vcast: coercion error"

-- A Value is either a function (with a name), or a Haskell
-- dynamic value with some typeclass operations
data Value = VaFun FunName (Value -> Result)
           | VaSus Doc Result
           | VaCon Uid (Maybe Value)
           | forall a. Valuable a => VaDyn a
  deriving Typeable

-- Construct an int value
vaInt  :: Integer -> Value
vaInt   = vinj

-- The unit value
vaUnit :: Value
vaUnit  = vinj ()

instance Ppr FunName where
  pprPrec _ (FNAnonymous doc) = hang (text "#<closure") 4 $
                                  doc <> char '>'
  pprPrec _ (FNNamed docs)    = hang (text "#<fn") 4 $
                                  sep docs <> char '>'

instance Ppr Value where
  pprPrec = vpprPrec

instance Eq Value where
  (==)    = veq

instance Show Value where
  showsPrec p v = shows (pprPrec p v)

--
-- Our semantic domains
--

type Result   = IO Value
type E        = Env Lid (IO Value)

type D        = E -> Result
type DDecl    = E -> IO E

-- Add the given name to an anonymous function
nameFun :: Lid -> Value -> Value
nameFun (Lid x) (VaFun (FNAnonymous _) lam)
  | x /= "it"          = VaFun (FNNamed [text x]) lam
nameFun _       value  = value

evalDecls :: [Decl i] -> DDecl
evalDecls  = (flip . foldM . flip) evalDecl

evalDecl :: Decl i -> DDecl
evalDecl (DcMod m)    = evalMod m
evalDecl (DcTyp _)    = return
evalDecl (DcAbs _ ds) = evalDecls ds

evalMod :: Mod i -> DDecl
evalMod (MdC x _ e)   env = do
  v <- valOf e env
  return (env =+= x =:= return v)
evalMod (MdA x _ e)   env = do
  v <- valOf e env
  return (env =+= x =:= return v)
evalMod (MdInt x _ y) env = do
  case env =.= y of
    Just v  -> return (env =+= x =:= v)
    Nothing -> fail $ "BUG! Unknown module: " ++ show y

eval :: E -> Prog i -> Result
eval env0 (Prog ds (Just e0)) = evalDecls ds env0 >>= valOf e0
eval env0 (Prog ds Nothing  ) = evalDecls ds env0 >>  return (vinj ())

-- The meaning of an expression
valOf :: Expr i w -> D
valOf e env = case expr' e of
  ExId (Var x)           -> case env =.= x of
    Just v  -> v
    Nothing -> fail $ "BUG! unbound identifier: " ++ show x
  ExId (Con c)           -> return (VaCon c Nothing)
  ExStr s                -> return (vinj s)
  ExInt z                -> return (vinj z)
  ExFloat f              -> return (vinj f)
  ExCase e1 clauses -> do
    v1 <- valOf e1 env
    let loop ((xi, ei):rest) = case bindPatt xi v1 env of
          Just env' -> valOf ei env'
          Nothing   -> loop rest
        loop []              =
          fail $ "Pattern match failure: " ++ show v1 ++
                 " matches none of " ++ show (map fst clauses)
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
  ExCast e1 _ _          ->
    valOf e1 env

bindPatt :: Monad m => Patt -> Value -> E -> m E
bindPatt x0 v env = case x0 of
  PaWild       -> return env
  PaVar lid    -> return (env =+= lid =:= return (lid `nameFun` v))
  PaCon uid mx -> case (mx, v) of
    (Nothing, VaCon uid' Nothing)   | uid == uid' -> return env
    (Just x,  VaCon uid' (Just v')) | uid == uid' -> bindPatt x v' env
    _                                             -> perr
  PaPair x y   -> case vprjM v of
    Just (vx, vy) -> bindPatt x vx env >>= bindPatt y vy
    Nothing       -> perr
  PaStr s      -> if v == vinj s
                    then return env
                    else perr
  PaInt z      -> if v == vinj z
                    then return env
                    else perr
  PaAs x lid   -> do
    env' <- bindPatt x v env
    return (env' =+= lid =:= return v)
  where perr = fail $
                 "Pattern match failure: " ++ show x0 ++
                 " does not match " ++ show v

force :: Value -> IO Value
force (VaSus _ v) = v >>= force
force v           = return v

instance Valuable a => Valuable [a] where
  veq a b  = length a == length b && all2 veq a b
  vpprPrec = vpprPrecList
  vinj     = vinjList
  vprjM    = vprjListM

instance Valuable Integer where
  veq        = (==)
  vpprPrec _ = text . show

instance Valuable Double where
  veq = (==)
  vpprPrec _ = text . show

instance Valuable () where
  veq        = (==)
  vinj ()    = VaCon (Uid "()") Nothing
  vprjM (VaCon (Uid "()") _) = return ()
  vprjM _                    = fail "vprjM: not a unit"

instance Valuable Bool where
  veq        = (==)
  vinj True  = VaCon (Uid "true") Nothing
  vinj False = VaCon (Uid "false") Nothing
  vprjM (VaCon (Uid "true") _)  = return True
  vprjM (VaCon (Uid "false") _) = return False
  vprjM _                       = fail "vprjM: not a bool"

instance Valuable Value where
  veq (VaCon c v) (VaCon d w) = c == d && v == w
  veq (VaDyn a)   b           = veqDyn a b
  veq _           _           = False
  vpprPrec p (VaFun n _)        = pprPrec p n
  vpprPrec _ (VaSus n _)        = n
  vpprPrec p (VaCon c Nothing)  = pprPrec p c
  vpprPrec p (VaCon c (Just v)) = parensIf (p > precApp) $
                                    pprPrec precApp c <+>
                                    vpprPrec (precApp + 1) v
  vpprPrec p (VaDyn v)          = vpprPrec p v

instance Valuable Char where
  veq            = (==)
  vpprPrec _     = text . show
  vpprPrecList _ = text . show
  vinjList       = VaDyn
  vprjListM      = vcast

instance (Valuable a, Valuable b) => Valuable (a, b) where
  veq (a, b) (a', b') = veq a a' && veq b b'
  vpprPrec p (a, b)   = parensIf (p > precCom) $
                          sep [vpprPrec precCom a <> char ',',
                               vpprPrec (precCom + 1) b]
  vinj (a, b) = VaDyn (vinj a, vinj b)
  vprjM v = case vcast v of
    Just (a, b) -> do
      a' <- vprjM a
      b' <- vprjM b
      return (a', b')
    Nothing -> fail "vprjM: not a pair"

instance (Valuable a, Valuable b) => Valuable (Either a b) where
  veq (Left a)  (Left a')  = veq a a'
  veq (Right b) (Right b') = veq b b'
  veq (Left _)  (Right _)  = False
  veq (Right _) (Left _)   = False
  vinj (Left v)  = VaCon (Uid "Left") (Just (vinj v))
  vinj (Right v) = VaCon (Uid "Right") (Just (vinj v))
  vprjM (VaCon (Uid "Left") (Just v))  = liftM Left (vprjM v)
  vprjM (VaCon (Uid "Right") (Just v)) = liftM Right (vprjM v)
  vprjM _                              = fail "vprjM: not a sum"

instance Valuable a => Valuable (Maybe a) where
  veq (Just a)  (Just a')  = veq a a'
  veq Nothing   Nothing    = True
  veq (Just _)  Nothing    = False
  veq Nothing   (Just _)   = False
  vinj (Just v) = VaCon (Uid "Some") (Just (vinj v))
  vinj Nothing  = VaCon (Uid "None") Nothing
  vprjM (VaCon (Uid "Some") (Just v))  = liftM Just (vprjM v)
  vprjM (VaCon (Uid "None") Nothing)   = return Nothing
  vprjM _                              = fail "vprjM: not an option"

