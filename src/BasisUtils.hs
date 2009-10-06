{-# LANGUAGE
  FlexibleInstances
 #-}
module BasisUtils (
  Entry,
  MkFun(..), baseMkFun,
  fun, binArith, val, pval, pfun,
  typeC, typeA, primtype, src,
  submod,
  vapp,
  (-:), (-::), (-=),
  text, Uid(..),
  basis2venv, basis2tenv
) where

import Dynamics (E, addVal, addMod)
import Env (GenEmpty(..))
import Parser (pt, pds)
import Ppr (ppr, text, hang, char, (<>))
import Statics (S, env0, tcDecls, addVal, addType, addMod)
import Syntax
import Util
import Value (Valuable(..), FunName(..), Value(..))

-- A basis entry is one of:
-- -- a value with name and types
-- -- source of a declaration to eval
-- -- an abstract type constructor
-- -- a module
data Entry = ValEn {
               enName  :: Lid,
               enCType :: String,
               enAType :: String,
               enValue :: Value
             }
           | DecEn {
               enSrc   :: String
             }
           | TypEn {
               enName  :: Lid,
               enTyTag :: TyTag
             }
           | ModEn {
               enModName :: Uid,
               enEnts    :: [Entry]
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
instance MkFun Double   where mkFun = baseMkFun
instance MkFun Char     where mkFun = baseMkFun
instance MkFun Bool     where mkFun = baseMkFun
instance MkFun ()       where mkFun = baseMkFun
instance (Valuable a, MkFun a) =>
         MkFun [a]      where mkFun = baseMkFun
instance (Valuable a, Valuable b, MkFun a, MkFun b) =>
         MkFun (a, b)   where mkFun = baseMkFun

baseMkFun :: (Valuable a, Valuable b) => FunName -> (a -> b) -> Value
baseMkFun n f = VaFun n $ \v -> vprjM v >>= return . vinj . f

fun :: (MkFun r, Valuable v) =>
       String -> String -> String -> (v -> r) -> Entry
fun name cty aty f = ValEn (Lid name) cty aty (mkFun (FNNamed [text name]) f)

val :: Valuable v => String -> String -> String -> v -> Entry
val name cty aty v = ValEn (Lid name) cty aty (vinj v)

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

class TypeBuilder r where
  typeA :: String -> r
  typeC :: String -> r
  src   :: String -> r

instance TypeBuilder Entry where
  typeC      = DecEn . ("type[C] " ++)
  typeA      = DecEn . ("type[A] " ++)
  src        = DecEn

instance TypeBuilder r => TypeBuilder (String -> r) where
  typeC s    = typeC . (s ++) . ('\n' :)
  typeA s    = typeA . (s ++) . ('\n' :)
  src s      = src   . (s ++) . ('\n' :)

submod :: String -> [Entry] -> Entry
submod  = ModEn . Uid

primtype  :: String -> TyTag -> Entry
primtype   = TypEn . Lid

(-:), (-=) :: (a -> b) -> a -> b
(-:) = ($)
(-=) = ($)
(-::) :: (a -> a -> b) -> a -> b
f -:: x = f x x
infixl 5 -:, -::
infixr 0 -=

-- Make binary arithmetic functions
binArith :: String -> (Integer -> Integer -> Integer) -> Entry
binArith name = fun name "int -> int -> int" "int -> int -> int"

vapp :: Valuable a => Value -> a -> IO Value
vapp  = \(VaFun _ f) x -> f (vinj x)
infixr 0 `vapp`

basis2venv :: Monad m => [Entry] -> m E
basis2venv es = foldM add genEmpty es where
  add :: Monad m => E -> Entry -> m E
  add e (ValEn { enName = n, enValue = v })
          = return (Dynamics.addVal e n v)
  add e (ModEn { enModName = n, enEnts = es' })
          = Dynamics.addMod e n `liftM` basis2venv es'
  add e _ = return e

basis2tenv :: Monad m => [Entry] -> m S
basis2tenv  = foldM each env0 where
  each gg0 (ValEn { enName = n, enCType = ct, enAType = at }) = do
    gg1 <- if null ct
      then return gg0
      else Statics.addVal gg0 n (pt ct :: Type () C)
    gg2 <- if null at
      then return gg1
      else Statics.addVal gg1 n (pt at :: Type () A)
    return gg2
  each gg0 (DecEn { enSrc = s }) = do
    (gg1, _, _) <- tcDecls False gg0 (pds s)
    return gg1
  each gg0 (TypEn { enName = n, enTyTag = i }) =
    return (Statics.addType gg0 n i)
  each gg0 (ModEn { enModName = n, enEnts = es }) =
    Statics.addMod gg0 n $ \gg' -> foldM each gg' es

