{-# LANGUAGE TypeFamilies #-}
module AST.Notable (
  Notable(..), N(..), Located,
  LocNote(..), module Data.Loc
) where

import Data.Data

import Data.Loc
import Util.Viewable

class Notable note where
  newNote   :: note
  newN      :: a -> N note a
  newN       = N newNote
  locN      :: Relocatable note => Loc -> a -> N note a
  locN loc a = newN a `setLoc` loc

data N note a
  = N {
      noteOf :: !note,
      dataOf :: !a
    }
  deriving (Typeable, Data, Functor)

instance Eq a => Eq (N note a) where
  a == b  =  dataOf a == dataOf b

instance Ord a => Ord (N note a) where
  a `compare` b  =  dataOf a `compare` dataOf b

instance (Notable note, Bounded a) => Bounded (N note a) where
  minBound = newN minBound
  maxBound = newN maxBound

instance Locatable note => Locatable (N note a) where
  getLoc (N note _) = getLoc note

instance Relocatable note => Relocatable (N note a) where
  setLoc (N note val) loc = N (setLoc note loc) val

instance Viewable (N note a) where
  type View (N note a) = a
  view = dataOf

newtype LocNote i = LocNote { unLocNote :: Loc }
  deriving (Eq, Ord, Data, Typeable, Locatable, Relocatable)

instance Show (LocNote i) where
  showsPrec p = showsPrec p . unLocNote

type Located f i = N (LocNote i) (f i)

instance Notable (LocNote i) where
  newNote = LocNote bogus
