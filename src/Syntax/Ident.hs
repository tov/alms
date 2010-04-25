{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      TypeFamilies #-}
module Syntax.Ident (
  -- * Identifiers
  Path(..),
  Lid(..), Uid(..), BIdent(..),
  Ident, QLid, QUid,
  TyVar(..),
  isOperator, qlid, quid,
) where

import Env (Path(..), (:>:)(..))
import Util
import Viewable
import Syntax.Kind

import Data.Char (isAlpha, isDigit)
import Data.Generics (Typeable(..), Data(..))

-- IDENTIFIERS

-- | lowercase identifiers (variables, tycons)
newtype Lid = Lid { unLid :: String }
  deriving (Eq, Ord, Typeable, Data)

-- | uppercase identifiers (modules, datacons)
newtype Uid = Uid { unUid :: String }
  deriving (Eq, Ord, Typeable, Data)

-- | bare (unqualified) identifers
data BIdent = Var { unVar :: Lid }
            | Con { unCon :: Uid }
  deriving (Eq, Ord, Typeable, Data)

-- | path-qualified uppercase identifiers
type QUid  = Path Uid Uid
-- | path-qualified lowecase identifiers
type QLid  = Path Uid Lid
-- | path-qualified identifiers
type Ident = Path Uid BIdent

-- | Type variables include qualifiers
data TyVar = TV { tvname :: Lid, tvqual :: Q }
  deriving (Eq, Ord, Typeable, Data)

-- | Is the lowercase identifier an infix operator?
isOperator :: Lid -> Bool
isOperator lid = case show lid of
    '(':_ -> True
    _     -> False

-- | Sugar for generating AST for qualified lowercase identifers
qlid :: String -> QLid
qlid s = case reverse (splitBy (=='.') s) of
           []   -> J [] (Lid "")
           x:xs -> J (map Uid (reverse xs)) (Lid x)

-- | Sugar for generating AST for qualified uppercase identifers
quid :: String -> QUid
quid s = case reverse (splitBy (=='.') s) of
           []   -> J [] (Uid "")
           x:xs -> J (map Uid (reverse xs)) (Uid x)

instance Show Lid where
  showsPrec _ (Lid s) = case s of
    '_':_             -> (s++)
    c  :_ | isAlpha c -> (s++)
    c  :_ | isDigit c -> (s++)
    '*':_             -> ("( "++) . (s++) . (" )"++)
    _                 -> ('(':) . (s++) . (')':)

instance Show Uid where
  show = unUid

instance Show BIdent where
  show (Var x) = show x
  show (Con k) = show k

instance Show TyVar where
  show (TV x Qu) = "'" ++ show x
  show (TV x Qa) = "'<" ++ show x

instance Viewable (Path Uid BIdent) where
  type View Ident = Either QLid QUid
  view (J p (Var n)) = Left (J p n)
  view (J p (Con n)) = Right (J p n)

-- | Simple keys embed into path keyspace
instance (Ord p, (:>:) k k') =>
         (:>:) (Path p k) k'  where liftKey = J [] . liftKey

instance (:>:) BIdent Lid     where liftKey = Var
instance (:>:) BIdent Uid     where liftKey = Con
