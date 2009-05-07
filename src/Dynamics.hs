{-# LANGUAGE
      ExistentialQuantification,
      DeriveDataTypeable
    #-}
module Dynamics (
  E, Result, eval,
  Valuable(..),
  FunName(..), Value(..), vaInt, vaUnit
) where

import Util
import Syntax
import Env
import Ppr (Doc, text, Ppr(..), hang, sep, char, (<>), (<+>),
            parensIf, precCom, precApp)

-- import Data.IORef (newIORef, readIORef, writeIORef)
import Data.Typeable (Typeable, cast)

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

  vpprPrecList :: Int -> [a] -> Doc
  vpprPrecList _ []     = text "nil"
  vpprPrecList p (x:xs) = parensIf (p > precApp) $
                            hang (text "cons" <+>
                                  vpprPrec (precApp + 1) x)
                                 1
                                 (vpprPrecList (precApp + 1) xs)

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
type E        = Env Var Value
type M        = Env Var (Either (Expr C) (Expr A))

type D        = M -> E -> Result

-- Add the given name to an anonymous function
nameFun :: Var -> Value -> Value
nameFun (Var x) (VaFun (FNAnonymous _) lam)
  | x /= "it"          = VaFun (FNNamed [text x]) lam
nameFun _       value  = value

eval :: E -> Prog -> Result
eval env0 (Prog ms e0) = valOf e0 menv env0 where
  menv = fromList (map each ms)
  each (MdC   x _ e') = (x, Left e')
  each (MdA   x _ e') = (x, Right e')
  each (MdInt x _ y)  = (x, Left (exVar y))

  -- The meaning of an expression
  valOf :: Expr w -> D
  valOf e m env = case expr' e of
    ExCon s                -> case env0 =.= Var s of
      Just v  -> return v
      Nothing -> fail $ "BUG! Unknown constant: " ++ s
    ExStr s                -> return (vinj s)
    ExInt z                -> return (vinj z)
    ExIf ec et ef         -> do
      c <- valOf ec m env
      if vprj c
        then valOf et m env
        else valOf ef m env
    ExLet x e1 e2          -> do
      v1 <- valOf e1 m env
      valOf e2 m $ env =+= x =:= nameFun x v1
    ExVar x        -> case env =.= x of
      Just v  -> return v
      Nothing -> case m =.= x of
        Just (Left e')  -> valOf e' m env0
        Just (Right e') -> valOf e' m env0
        Nothing -> fail $ "BUG! unbound variable: " ++ show x
    ExPair e1 e2           -> do
      v1 <- valOf e1 m env
      v2 <- valOf e2 m env
      return (vinj (v1, v2))
    ExLetPair (x, y) e1 e2 -> do
      v1 <- valOf e1 m env
      let (vx, vy) = vprj v1
      valOf e2 m $ env =+= x =:= nameFun x vx
                       =+= y =:= nameFun y vy
    ExAbs x _ e'           ->
      return (VaFun (FNAnonymous (ppr e))
                    (\v -> valOf e' m (env =+= x =:= v)))
    ExApp e1 e2            -> do
      v1  <- valOf e1 m env
      v2  <- valOf e2 m env
      v1' <- force v1  -- Magic type application
      case v1' of
        VaFun _ f -> f v2
        _         -> fail $ "BUG! applied non-function " ++ show v1
                             ++ " to argument " ++ show v2
    ExTAbs _ e'            ->
      return (VaSus (hang (text "#<sus") 4 $ ppr e <> char '>')
                    (valOf e' m env))
    ExTApp e' _            -> do
      v' <- valOf e' m env
      case v' of
        VaSus _ f -> f
        _         -> fail $ "BUG! type-applied non-typefunction: " ++ show v'
    ExSeq e1 e2            -> do
      valOf e1 m env
      valOf e2 m env
    ExCast e1 _ _          ->
      valOf e1 m env

force :: Value -> IO Value
force (VaSus _ v) = v >>= force
force v           = return v

instance Valuable a => Valuable [a] where
  veq a b  = length a == length b && all2 veq a b
  vpprPrec = vpprPrecList

instance Valuable Integer where
  veq        = (==)
  vpprPrec _ = text . show

instance Valuable () where
  veq        = (==)
  vpprPrec _ = text . show

instance Valuable Bool where
  veq        = (==)
  vpprPrec _ True  = text "true"
  vpprPrec _ False = text "false"

instance Valuable Value where
  veq (VaDyn a) b = veqDyn a b
  veq _         _ = False
  vpprPrec p (VaFun n _) = pprPrec p n
  vpprPrec _ (VaSus n _) = n
  vpprPrec p (VaDyn v)   = vpprPrec p v

instance Valuable Char where
  veq            = (==)
  vpprPrec _     = text . show
  vpprPrecList _ = text . show

instance (Valuable a, Valuable b) => Valuable (a, b) where
  veq (a, b) (a', b') = veq a a' && veq b b'
  vpprPrec p (a, b)   = parensIf (p > precCom) $
                          sep [vpprPrec (precCom + 1) a <> char ',',
                               vpprPrec (precCom + 1) b]

