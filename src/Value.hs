{-# LANGUAGE
      DeriveDataTypeable,
      ExistentialQuantification,
      MultiParamTypeClasses,
      PatternGuards,
      RankNTypes,
      ScopedTypeVariables
    #-}
module Value (
  Valuable(..),
  FunName(..), Value(..), vaInt, vaUnit,
  Vinj(..), VExn(..),
  enumTypeDecl,
  vinjData, vprjDataM
) where

import qualified Data.List as List
import qualified Data.Char as Char
import Data.Generics

import Util
import Syntax (Uid(..), LangRepMono(..))
import Ppr (Doc, text, Ppr(..), hang, sep, char, (<>), (<+>),
            parensIf, precCom, precApp)

import Foreign.C.Types (CInt)
import Data.Word (Word32, Word16)

import Control.Monad.State as M.S

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
data Value = VaFun FunName (Value -> IO Value)
           | VaSus Doc (IO Value)
           | VaCon Uid (Maybe Value)
           | forall a. Valuable a => VaDyn a
  deriving Typeable

-- We represent function names in a way that makes pretty-printing
-- them nicer
-- Construct an int value
vaInt  :: Integer -> Value
vaInt   = vinj

-- The unit value
vaUnit :: Value
vaUnit  = vinj ()

-- Ppr instances

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

instance Valuable a => Valuable [a] where
  veq a b  = length a == length b && all2 veq a b
  vpprPrec = vpprPrecList
  vinj     = vinjList
  vprjM    = vprjListM

instance Valuable Int where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinj . toInteger
  vprjM v    = vprjM v >>= \z -> return (fromIntegral (z :: Integer))

instance Valuable Word16 where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinj . toInteger
  vprjM v    = vprjM v >>= \z -> return (fromIntegral (z :: Integer))

instance Valuable Word32 where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinj . toInteger
  vprjM v    = vprjM v >>= \z -> return (fromIntegral (z :: Integer))

instance Valuable CInt where
  veq        = (==)
  vpprPrec _ = text . show
  vinj       = vinj . toInteger
  vprjM v    = vprjM v >>= \z -> return (fromIntegral (z :: Integer))

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
  vinj v = v
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
  -- for value debugging:
  {-
  vpprPrec p (VaCon c Nothing)  = char '[' <> pprPrec p c <> char ']'
  vpprPrec p (VaCon c (Just v)) = parensIf (p > precApp) $
                                    char '[' <> pprPrec precApp c <+>
                                    vpprPrec (precApp + 1) v <> char ']'
  vpprPrec p (VaDyn v)          = char '{' <> vpprPrec p v <> char '}'
  -}

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

-- For other arbitrary values:
newtype Vinj a = Vinj { unVinj :: a }
  deriving (Eq, Typeable, Data)

instance (Eq a, Show a, Data a) => Valuable (Vinj a) where
  veq        = (==)
  vpprPrec _ = text . show

instance Show a => Show (Vinj a) where
  showsPrec p = showsPrec p . unVinj


-- Exceptions

data VExn = VExn {
              exnName  :: Uid,
              exnParam :: Maybe Value,
              exnIndex :: Integer,
              exnLang  :: LangRepMono
            }
  deriving (Typeable, Eq)

instance Valuable VExn where
  veq          = (==)
  vpprPrec p e = text "exn:" <> vpprPrec p (VaCon (exnName e) (exnParam e))

-- nasty syb stuff

enumTypeDecl :: Data a => a -> String
enumTypeDecl a =
  case dataTypeRep ty of
    IntRep     -> add "int"
    FloatRep   -> add "float"
    StringRep  -> add "string"
    NoRep      -> name
    AlgRep cs  -> add (unwords (List.intersperse " | " (map showConstr cs)))
  where
    ty = dataTypeOf a
    add body = name ++ " = " ++ body
    name = case last (splitBy (=='.') (dataTypeName ty)) of
             c:cs -> Char.toLower c : cs
             _    -> error "(BUG!) bad type name in enumTypeDecl"


newtype Const a b = Const { unConst :: a }

vinjData :: Data a => a -> Value
vinjData = generic
    `ext1Q` (vinj . map vinjData)
    `ext1Q` (vinj . maybe Nothing (Just . vinjData))
    `extQ`  (vinj :: String -> Value)
    `extQ`  (vinj :: Value  -> Value)
    `extQ`  (vinj :: Bool   -> Value)
    `extQ`  (vinj :: Char   -> Value)
    where
  generic datum = case constrRep r of
      IntConstr    v -> vinj v
      StringConstr v -> vinj v
      FloatConstr  v -> vinj v
      AlgConstr    _ -> c (unConst (gfoldl k z datum))
    where
      r = toConstr datum
      k (Const Nothing)  x = Const (Just (vinjData x))
      k (Const (Just v)) x = Const (Just (vinj (v, vinjData x)))
      z = const (Const Nothing)
      c f = case (showConstr r, f) of
             (s, Just f') | isTuple s
               -> f'
             _ -> VaCon (Uid (showConstr r)) f

vprjDataM :: forall a m. (Data a, Monad m) => Value -> m a
vprjDataM = generic
    `ext1RT` (\x -> vprjM x >>= sequence . liftM vprjDataM)
    `ext1RT` (\x -> vprjM x >>= maybe (return Nothing) (liftM return)
                                         . liftM vprjDataM)
    `extRT` (vprjM :: Value -> m Int)
    `extRT` (vprjM :: Value -> m CInt)
    `extRT` (vprjM :: Value -> m Word32)
    `extRT` (vprjM :: Value -> m Word16)
    `extRT` (vprjM :: Value -> m Integer)
    `extRT` (vprjM :: Value -> m String)
    `extRT` (vprjM :: Value -> m Double)
    `extRT` (vprjM :: Value -> m Value)
    `extRT` (vprjM :: Value -> m Bool)
    `extRT` (vprjM :: Value -> m Char)
    where
  generic (VaCon (Uid uid) mfields0) = case readConstr ty uid of
      Nothing -> fail $ 
                   "(BUG) Couldn't find constructor: " ++ uid ++
                   " in " ++ show ty
      Just c  -> M.S.evalStateT (gunfold k z c) mfields0
    where
      k consmaker = do
        mfields <- M.S.get
        fields <- case mfields of
          Just fields -> return fields
          Nothing     -> fail "(BUG) ran out of fields"
        field <- case vprjM fields of
          Just (fields', field) -> do
            M.S.put (Just fields')
            return field
          Nothing -> do
            M.S.put Nothing
            return fields
        make  <- consmaker
        mrest <- M.S.get
        field' <- case mrest of
          Just rest -> do
            M.S.put Nothing
            return (vinj (rest, field))
          Nothing   ->
            return field
        datum <- vprjDataM field'
        return (make datum)
      z = return
  generic v@(VaDyn _) = case dataTypeRep ty of
    AlgRep (c:_) | t <- showConstr c, isTuple t
            -> generic (VaCon (Uid t) (Just v))
    IntRep       | Just i <- vprjM v,
                   Just d <- cast (i :: Integer)
            -> return d
    FloatRep     | Just f <- vprjM v,
                   Just d <- cast (f :: Double)
            -> return d
    StringRep    | Just s <- vprjM v,
                   Just d <- cast (s :: String)
            -> return d
    _       -> fail $ "(BUG) Can't project (VaDyn) " ++ show v ++
                      " as datatype: " ++ show ty
  generic v = fail $ "(BUG) Can't project " ++ show v ++
                     " as datatype: " ++ show ty
  ty = dataTypeOf (undefined :: a)

isTuple :: String -> Bool
isTuple ('(':',':r) | dropWhile (== ',') r == ")"
        = True
isTuple _ = False

newtype RT r m a = RT { unRT :: r -> m a }

extRT :: (Typeable a, Typeable b) =>
         (r -> m a) -> (r -> m b) -> r -> m a
m1 `extRT` m2 = unRT (maybe (RT m1) id (gcast (RT m2)))

ext1RT :: (Data d, Typeable1 t) =>
          (r -> m d) -> (forall e. Data e => r -> m (t e)) -> r -> m d
m1 `ext1RT` m2 = unRT (maybe (RT m1) id (dataCast1 (RT m2)))

{-
ext2RT :: (Data d, Typeable2 t) =>
          (r -> m d) ->
          (forall e e'. (Data e, Data e') => r -> m (t e e')) ->
          r -> m d
m1 `ext2RT` m2 = unRT (maybe (RT m1) id (dataCast2 (RT m2)))
-}
