{-# LANGUAGE
      DeriveDataTypeable,
      FlexibleInstances,
      MultiParamTypeClasses,
      TypeFamilies,
      TypeSynonymInstances #-}
module Syntax.Ident (
  -- * Identifiers
  Id(..),
  Path(..),
  Lid(..), Uid(..), BIdent(..),
  Ident, QLid, QUid,
  TyVar(..), tvUn, tvAf, tvalphabet,
  isOperator, qlid, quid,
  -- * Free and defined vars
  FvMap, Fv(..), Dv(..), ADDITIVE(..),
  (|*|), (|+|), (|-|), (|--|)
) where

import Env (Path(..), (:>:)(..))
import Util
import Viewable
import Syntax.Anti
import Syntax.Kind (QLit(..))

import Data.Char (isAlpha, isDigit)
import Data.Generics (Typeable(..), Data(..))
import qualified Data.Map as M
import qualified Data.Set as S

class Data i => Id i where
  stupidIdMethod :: i
instance Id () where
  stupidIdMethod = ()

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

tvUn, tvAf :: String -> TyVar
tvUn s = TV (Lid s) Qu
tvAf s = TV (Lid s) Qa

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


---
--- Free variables
---

-- | Our free variables function returns not merely a set,
-- but a map from names to a count of maximum occurrences.
type FvMap = M.Map QLid Integer

-- | The free variables analysis
class Fv a where
  fv :: a -> FvMap

-- | The defined variables analysis
class Dv a where
  qdv :: a -> S.Set QLid
  dv  :: a -> S.Set Lid

  qdv  = S.mapMonotonic (J []) . dv
  dv a = S.fromDistinctAscList [ v | J [] v <- S.toAscList (qdv a) ]

instance Fv a => Fv [a] where
  fv = foldr (|+|) M.empty . map fv

instance Dv a => Dv [a] where
  dv = S.unions . map dv

newtype ADDITIVE a = ADDITIVE [a]

instance Fv a => Fv (ADDITIVE a) where
  fv (ADDITIVE a) = foldr (|+|) M.empty (map fv a)

-- | Used by the free variables analysis
(|*|), (|+|) :: FvMap -> FvMap -> FvMap
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: FvMap -> QLid -> FvMap
(|-|)  = flip M.delete

(|--|) :: FvMap -> S.Set QLid -> FvMap
(|--|)  = S.fold M.delete

