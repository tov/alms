{-# LANGUAGE DeriveDataTypeable #-}
module BasisUtils (
  Entry, Nonce(..), Vinj(..),
  MkFun(..),
  fun, binArith, val, pval, pfun,
  typeC, typeA, primtype,
  vapp,
  (-:), (-::), (-=),
  basis2venv, basis2tenv
) where

import Util
import Dynamics
import Statics (S, env0, tcDecls, addVal, addTInfo)
import Env (Env, fromList)
import Syntax (Var(..), Type, TInfo(..), C, A)
import Parser (pt, pds)

import Data.Typeable (Typeable)
import Ppr (ppr, text, hang, char, (<>))

-- Basis entries are either values with names and types, or
-- abstract type constructors.
data Entry = ValEn {
               enName  :: String,
               enCType :: String,
               enAType :: String,
               enValue :: Value
             }
           | DecEn {
               enSrc   :: String
             }
           | TypEn {
               enName  :: String,
               enTInfo :: TInfo
             }

-- Type class for making Values out of Haskell functions
class MkFun r where
  mkFun :: Valuable v => FunName -> (v -> r) -> Value

-- Recursive case: accept one argument, then look for more
instance (Valuable v, MkFun r) => MkFun (v -> r) where
  mkFun n f = VaFun n $ \v ->
    vprjM v >>= return . mkFun (next v) . f
    where
      next v = case n of
        FNAnonymous doc -> FNAnonymous doc
        FNNamed docs    -> FNNamed (docs ++ [ppr v])

-- Base cases for various return types
instance Valuable r => MkFun (IO r) where
  mkFun n f = VaFun n $ \v -> vprjM v >>= f >>= return . vinj

instance MkFun Value where
  mkFun n f = VaFun n $ \v -> vprjM v >>= return . f

instance MkFun Integer  where mkFun = baseMkFun
instance MkFun Bool     where mkFun = baseMkFun
instance MkFun ()       where mkFun = baseMkFun
instance MkFun Nonce    where mkFun = baseMkFun
instance (Valuable a, MkFun a) =>
         MkFun [a]      where mkFun = baseMkFun
instance (Valuable a, Valuable b, MkFun a, MkFun b) =>
         MkFun (a, b)   where mkFun = baseMkFun

baseMkFun :: (Valuable a, Valuable b) => FunName -> (a -> b) -> Value
baseMkFun n f = VaFun n $ \v -> vprjM v >>= return . vinj . f

fun :: (MkFun r, Valuable v) =>
       String -> String -> String -> (v -> r) -> Entry
fun name cty aty f = ValEn name cty aty (mkFun (FNNamed [text name]) f)

val :: Valuable v => String -> String -> String -> v -> Entry
val name cty aty v = ValEn name cty aty (vinj v)

pval :: Valuable v => Int -> String -> String -> String -> v -> Entry
pval 0 name cty aty v = val name cty aty v
pval n name cty aty v = mkTyAbs (pval (n - 1) name cty aty v)

pfun :: (MkFun r, Valuable v) =>
        Int -> String -> String -> String -> (v -> r) -> Entry
pfun 0 name cty aty f = fun name cty aty f
pfun n name cty aty f = mkTyAbs (pfun (n - 1) name cty aty f)

mkTyAbs :: Entry -> Entry
mkTyAbs entry =
  let v     = enValue entry in
  entry { enValue =
            VaSus (hang (text "#<sus") 4 $ vppr v <> char '>')
                  (return v) }

typeC     :: String -> Entry
typeC      = DecEn . ("type[C] " ++)

typeA     :: String -> Entry
typeA      = DecEn . ("type[A] " ++)

primtype  :: String -> TInfo -> Entry
primtype   = TypEn

(-:), (-=) :: (a -> b) -> a -> b
(-:) = ($)
(-=) = ($)
(-::) :: (a -> a -> b) -> a -> b
f -:: x = f x x
infixl 5 -:, -::
infixr 0 -=

-- For nonce values (and printing them)
newtype Nonce = Nonce String
  deriving (Eq, Typeable)

instance Valuable Nonce where
  veq                  = (==)
  vpprPrec _ (Nonce s) = text ("#<" ++ s ++ ">")

-- For other arbitrary values:
newtype Vinj a = Vinj { unVinj :: a }
  deriving (Eq, Typeable)

instance (Eq a, Show a, Typeable a) => Valuable (Vinj a) where
  veq        = (==)
  vpprPrec _ = text . show

instance Show a => Show (Vinj a) where
  showsPrec p = showsPrec p . unVinj

-- Make binary arithmetic functions
binArith :: String -> (Integer -> Integer -> Integer) -> Entry
binArith name = fun name "int -> int -> int" "int -> int -> int"

vapp :: Valuable a => Value -> a -> IO Value
vapp  = \(VaFun _ f) x -> f (vinj x)
infixr 0 `vapp`

basis2venv :: Monad m => [Entry] -> m (Env Var (IO Value))
basis2venv es = return $
  fromList [ (Var s, return v)
           | ValEn { enName = s, enValue = v } <- es ]

basis2tenv :: Monad m => [Entry] -> m S
basis2tenv  = foldM each env0 where
  each gg0 (ValEn { enName = s, enCType = ct, enAType = at }) = do
    gg1 <- if null ct
      then return gg0
      else addVal gg0 (Var s) (pt ct :: Type () C)
    gg2 <- if null at
      then return gg1
      else addVal gg1 (Var s) (pt at :: Type () A)
    return gg2
  each gg0 (DecEn { enSrc = s }) =
    fst `liftM` tcDecls gg0 (pds s)
  each gg0 (TypEn { enName = s, enTInfo = i }) =
    return (addTInfo gg0 s i)
