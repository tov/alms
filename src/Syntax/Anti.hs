{-# LANGUAGE
      DeriveDataTypeable,
      TypeFamilies,
      TypeOperators #-}
module Syntax.Anti (
  Anti(..), MAnti(..), unAnti, unAntiM,
  GetAnti(..), antifail, antierror,
) where

import Viewable

import Data.Generics (Typeable, Data)

data Anti = Anti {
              anType :: String,
              anName :: String
            }
  deriving (Eq, Typeable, Data)

instance Show Anti where
  show (Anti ""   aid) = '$' : aid
  show (Anti atag aid) = '$' : atag ++ ':' : aid

class GetAnti a where
  getAnti :: a -> Anti

instance GetAnti Anti where
  getAnti = id

antifail :: (Monad m, GetAnti a) => String -> a -> m b
antifail who what = fail $ "BUG! " ++ who ++ ": encountered antiquote: "
                           ++ show (getAnti what)

antierror :: GetAnti a => String -> a -> b
antierror who what = error $ "BUG! " ++ who ++ ": encountered antiquote: "
                           ++ show (getAnti what)

data MAnti a = JA a
          | NA Anti
  deriving (Eq, Typeable, Data)

unAnti :: String -> MAnti a -> a
unAnti _   (JA a)  = a
unAnti who (NA an) = antierror who an

unAntiM :: Monad m => String -> MAnti a -> m a
unAntiM _   (JA a) = return a
unAntiM who (NA a) = antifail who a

instance Show a => Show (MAnti a) where
  showsPrec p (JA a) = showsPrec p a
  showsPrec p (NA a) = showsPrec p a

instance Viewable (MAnti a) where
  type View (MAnti a) = a
  view = unAnti "view"

instance Functor MAnti where
  fmap f (JA a) = JA (f a)
  fmap _ (NA a) = NA a
