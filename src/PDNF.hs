{-# LANGUAGE DeriveDataTypeable #-}
-- | Positive Disjunctive Normal Form
module PDNF (
  -- * Abstract representation
  PDNF,
  -- * Construction
  variable, conjunct, disjunct, disjoinClause, conjoinClause,
  -- * Queries
  isUnsat, isValid, support,
  -- ** Assignments
  Assignment, satisfies, findUnsat,
  -- * Resolution and substitution
  assume, replace, mapVars, mapVarsM, mapReplace, mapReplaceM,
  -- * To and from lists
  fromLists, fromListsUnsafe, toLists,
  -- * Tests
  tests
) where

import Syntax.POClass
import Util

import Prelude ()
import Data.Generics (Typeable, Data)
import Data.List (intersperse, nub, sort)
import qualified Data.Set as S
import qualified Test.QuickCheck as QC

-- | The type of a Positive DNF over some type 'a'
newtype PDNF a = PDNF { unPDNF :: [S.Set a] }
  deriving (Typeable, Data)

-- | Is the formula unsatisfiable?
-- O(1)
isUnsat :: PDNF a -> Bool
isUnsat  = null . unPDNF

-- | Is the formula valid?
isValid :: Eq a => PDNF a -> Bool
isValid  = (== [S.empty]) . unPDNF

-- | To update the formula to reflect an assumption about the
--   assignment for a particular variable.
assume  :: Ord a => Bool -> a -> PDNF a -> PDNF a
assume True  v formula = PDNF . normalize' $
  map (S.delete v) (unPDNF formula)
assume False v formula = PDNF $
  filter (S.notMember v) (unPDNF formula)

-- | To substitute a PDNF formula for a given variable in another
--   formula.
replace :: Ord a => a -> PDNF a -> PDNF a -> PDNF a
replace v (PDNF f1) (PDNF f2) = PDNF $
  normalize' $ concatMap eachClause f2
  where
  eachClause clause
    | v `S.member` clause = conjoinClause' (S.delete v clause) f1
    | otherwise           = [clause]

-- | To map every variable in a formula
mapVars :: (Ord a, Ord b) => (a -> b) -> PDNF a -> PDNF b
mapVars f  = PDNF . normalize' . map (S.map f) . unPDNF

-- | To map every variable in a formula, in an arbitrary monad
mapVarsM :: (Ord a, Ord b, Monad m) =>
            (a -> m b) -> PDNF a -> m (PDNF b)
mapVarsM f = liftM fromLists . mapM (mapM f) . toLists'

-- | To map every variable in a formula to a formula, possibly over
--   a different type
mapReplace :: (Ord a, Ord b) =>
              PDNF a -> (a -> PDNF b) -> PDNF b
mapReplace m k = bigVee [ bigWedge [ k var | var <- clause ]
                        | clause <- toLists' m ]

-- | To map every variable in a formula to a formula, possibly over
--   a different type, in an arbitrary monad
mapReplaceM :: (Ord a, Ord b, Monad m) =>
               PDNF a -> (a -> m (PDNF b)) -> m (PDNF b)
mapReplaceM m k = liftM bigVee (mapM (liftM bigWedge . mapM k) (toLists' m))

-- | To construct a formula of a single variable
variable :: a -> PDNF a
variable  = PDNF . return . S.singleton

-- | To find the support of a PDNF
support  :: Ord a => PDNF a -> S.Set a
support   = foldr S.union S.empty . unPDNF

-- | To construct a formula of one conjuction
conjunct :: Ord a => [a] -> PDNF a
conjunct  = PDNF . return . S.fromList

disjunct :: Ord a => [a] -> PDNF a
disjunct  = PDNF . map S.singleton . nub

instance Ord a => PO (PDNF a) where
  f1 \/ f2 = PDNF $ foldr disjoinClause' (unPDNF f1) (unPDNF f2)
  f1 /\ f2 = PDNF $
    normalize' [ clause1 `S.union` clause2
               | clause1 <- unPDNF f1
               , clause2 <- unPDNF f2 ]
  PDNF ant <: PDNF con
    = all (\clause -> any (`S.isSubsetOf` clause) con) ant

instance Bounded (PDNF a) where
  minBound = PDNF []
  maxBound = PDNF [S.empty]

instance Ord a => Eq (PDNF a) where
  f1 == f2 = compare f1 f2 == EQ

instance Ord a => Ord (PDNF a) where
  f1 `compare` f2 = toLists f1 `compare` toLists f2

-- | To add a clause to a formula
disjoinClause :: Ord a => [a] -> PDNF a -> PDNF a
disjoinClause c' = PDNF . disjoinClause' (S.fromList c') . unPDNF

-- | To distribute a clause over a formula
conjoinClause :: Ord a => [a] -> PDNF a -> PDNF a
conjoinClause c' = PDNF . conjoinClause' (S.fromList c') . unPDNF

disjoinClause' :: Ord a => S.Set a -> [S.Set a] -> [S.Set a]
disjoinClause' c' []     = [c']
disjoinClause' c' (c:cs) =
  if c' `S.isSubsetOf` c
    then disjoinClause' c' cs
  else if c `S.isSubsetOf` c'
    then c:cs
    else c:disjoinClause' c' cs

conjoinClause' :: Ord a => S.Set a -> [S.Set a] -> [S.Set a]
conjoinClause' c' cs = map (S.union c') cs

normalize' :: Ord a => [S.Set a] -> [S.Set a]
normalize'  = foldr disjoinClause' []

-- | To construct a PDNF.
fromLists :: Ord a => [[a]] -> PDNF a
fromLists  = foldr (\/) minBound . map conjunct

-- | To construct a PDNF quickly, assuming that no list is a superset
--   of an other list.
fromListsUnsafe :: Ord a => [[a]] -> PDNF a
fromListsUnsafe  = PDNF . map S.fromList

-- | To construct a canonical list of lists of variables.
toLists :: Ord a => PDNF a -> [[a]]
toLists  = sort . map S.toAscList . unPDNF

toLists' :: PDNF a -> [[a]]
toLists'  = map S.toList . unPDNF

instance (Eq a, Show a) => Show (PDNF a) where
  showsPrec _ pdnf
    | isValid pdnf = showString "#t"
    | isUnsat pdnf = showString "#f"
  showsPrec p (PDNF formula) =
    showParen (p > 5) $
      foldr (.) id $
        intersperse (showString " | ")
          [ foldr (.) id $
              intersperse (showString " & ") $
                [ showsPrec 6 lit
                | lit <- S.toList clause ]
          | clause <- formula ]

---
--- Assignments
---

-- | An assignment is a map from variables to booleans, represented
--   as a list of variables to map to true, with all others mapped
--   to false.
type Assignment a = [a]

-- | Does the given assignment satisfy the PDNF?
satisfies :: Ord a => PDNF a -> Assignment a -> Bool
satisfies pdnf vs = isValid (foldr (assume True) pdnf vs)

-- | Find an assignment that satisfies the first PDNF but not
--   the second.
findUnsat :: Ord a => PDNF a -> PDNF a -> [Assignment a]
findUnsat (PDNF f1) (PDNF f2) =
  [ S.toList clause
  | clause <- f1
  , not (any (`S.isSubsetOf` clause) f2) ]

---
--- Tests
---

assignFor :: Ord a => PDNF a -> QC.Gen (Assignment a)
assignFor pdnf =
  genSublist (S.toList (support pdnf))
    where
      genSublist :: [a] -> QC.Gen [a]
      genSublist lst = do
        let den = length lst
        num <- QC.choose (0, den `div` 2)
        let each rest elt = do
              pick <- QC.choose (1, den)
              return $ if pick > num
                then elt:rest
                else rest
        foldM each [] lst

instance (Ord a, QC.Arbitrary a) => QC.Arbitrary (PDNF a) where
  arbitrary = fromLists `fmap` QC.arbitrary
  shrink    = map fromLists . QC.shrink . toLists

prop_Impl :: PDNF Int -> PDNF Int -> QC.Property
prop_Impl f1 f2 =
  if f1 <: f2 then
    impl f1 f2
  else if f2 <: f1 then
    impl f2 f1
  else
    QC.classify True "counterexample" $
      not (null (findUnsat f1 f2))
  where impl f1' f2' =
          QC.classify True "implication" $
            QC.forAll (assignFor (f1' \/ f2')) $ \s ->
              satisfies f1' s QC.==> satisfies f2' s

prop_Disj :: PDNF Int -> PDNF Int -> Bool
prop_Disj f1 f2 = f1 <: f1 \/ f2

prop_Conj :: PDNF Int -> PDNF Int -> Bool
prop_Conj f1 f2 = f1 /\ f2 <: f1

prop_Replace :: PDNF Int -> Bool -> QC.Property
prop_Replace pdnf b =
  QC.forAll (QC.elements (S.toList (support pdnf))) $ \v ->
    replace v (if b then maxBound else minBound) pdnf == assume b v pdnf

tests :: IO ()
tests  = do
  QC.quickCheck prop_Replace
  QC.quickCheck prop_Impl
  QC.quickCheck prop_Disj
  QC.quickCheck prop_Conj
