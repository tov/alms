{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      TypeFamilies,
      TypeSynonymInstances #-}
module Syntax.Ident (
  -- * Identifiers
  Path(..),
  Lid(..), Uid(..), BIdent(..),
  Ident, QLid, QUid,
  TyVar(..), tvalphabet,
  isOperator, qlid, quid,
) where

import Env (Path(..), (:>:)(..))
import Util
import Viewable
import Syntax.Anti
import Syntax.Kind (QLit(..))

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
data TyVar = TV { tvname :: Lid, tvqual :: QLit }
  deriving (Eq, Ord, Typeable, Data)

tvalphabet :: [QLit -> TyVar]
tvalphabet  = map (TV . Lid) alphabet
  where
    alphabet = map return ['a' .. 'z'] ++
               [ x ++ [y] | x <- alphabet, y <- ['a' .. 'z'] ]

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
    '{':_             -> (s++)
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
  showsPrec _ (TV x Qu) = showString "'" . shows x
  showsPrec _ (TV x Qa) = showString "'<" . shows x

instance Viewable (Path Uid BIdent) where
  type View Ident = Either QLid QUid
  view (J p (Var n)) = Left (J p n)
  view (J p (Con n)) = Right (J p n)

-- | Simple keys embed into path keyspace
instance (Ord p, (:>:) k k') =>
         (:>:) (Path p k) k'  where liftKey = J [] . liftKey

instance (:>:) BIdent Lid     where liftKey = Var
instance (:>:) BIdent Uid     where liftKey = Con

---
--- Identifier antiquotes
---

instance Antible Char where
  injAntiList (Anti t a) =
    "$" ++ t ++ ":" ++ a
  prjAntiList s = do
    [ '$':t , n ] <- return $ splitBy (== ':') s
    return (Anti t n)
  dictOfList _  = error "dictOf: No AntiDict for String"
  injAnti _ = error "injAnti: Not defined for Char"
  prjAnti _ = error "prjAnti: Not defined for Char"
  dictOf _  = error "dictOf: Not defined for Char"

instance Antible Lid where
  injAnti = Lid . injAnti
  prjAnti = prjAnti . unLid
  dictOf  = const lidAntis

instance Antible Uid where
  injAnti = Uid . injAnti
  prjAnti = prjAnti . unUid
  dictOf  = const uidAntis

instance Antible TyVar where
  injAnti = flip TV Qu . injAnti
  prjAnti = prjAnti . tvname
  dictOf  = const tyVarAntis

instance Antible Ident where
  injAnti         = J [] . Var . injAnti
  prjAnti (J [] (Var l)) = prjAnti l
  prjAnti _              = Nothing
  dictOf                 = const idAntis

instance Antible QLid where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const qlidAntis

instance Antible QUid where
  injAnti          = J [] . injAnti
  prjAnti (J [] i) = prjAnti i
  prjAnti _        = Nothing
  dictOf           = const quidAntis
