-- | Positive Disjunctive Normal Form
module PDNF (
  -- * Abstract representation
  PDNF,
  -- * Construction
  variable, clause, disjoin, conjoin, disjoinClause, conjoinClause,
  -- * Resolution
  assume,
  -- * To and from lists
  fromLists, fromListsUnsafe, toLists
) where

import qualified Data.Set as S
import Data.List (intersperse)

-- | The type of a Positive DNF over some type 'a'
newtype PDNF a = PDNF { unPDNF :: [S.Set a] }

-- | Is the formula unsatisfiable?
isUnsat :: PDNF a -> Bool
isUnsat  = null . unPDNF

-- | Is the formula valid?
isValid :: Eq a => PDNF a -> Bool
isValid  = (== [S.empty]) . unPDNF

-- | To update the formula to reflect an assumption about the
--   assignment for a particular variable.
assume  :: Ord a => a -> Bool -> PDNF a -> PDNF a
assume v True  formula = PDNF . normalize' $
  map (S.delete v) (unPDNF formula)
assume v False formula = PDNF $
  filter (S.notMember v) (unPDNF formula)

-- | To construct a formula of a single variable
variable :: a -> PDNF a
variable  = PDNF . return . S.singleton

-- | To construct a formula of one conjuction
clause   :: Ord a => [a] -> PDNF a
clause    = PDNF . return . S.fromList

-- | To find the disjunction of two formulae
disjoin  :: Ord a => PDNF a -> PDNF a -> PDNF a
disjoin f = PDNF . foldr disjoinClause' (unPDNF f) . unPDNF where

-- | To add a clause to a formula
disjoinClause :: Ord a => [a] -> PDNF a -> PDNF a
disjoinClause c' = PDNF . disjoinClause' (S.fromList c') . unPDNF

disjoinClause' :: Ord a => S.Set a -> [S.Set a] -> [S.Set a]
disjoinClause' c' []     = [c']
disjoinClause' c' (c:cs) =
  if c' `S.isSubsetOf` c
    then disjoinClause' c' cs
  else if c `S.isSubsetOf` c'
    then c:cs
    else c:disjoinClause' c' cs

-- | To find the conjunction of two formulae
conjoin :: Ord a => PDNF a -> PDNF a -> PDNF a
conjoin f1 f2 = PDNF $
  normalize' [ clause1 `S.union` clause2
             | clause1 <- unPDNF f1
             , clause2 <- unPDNF f2 ]

normalize' :: Ord a => [S.Set a] -> [S.Set a]
normalize'  = foldr disjoinClause' []

-- | To distribute a clause over a formula
conjoinClause :: Ord a => [a] -> PDNF a -> PDNF a
conjoinClause c' = PDNF . conjoinClause' (S.fromList c') . unPDNF

conjoinClause' :: Ord a => S.Set a -> [S.Set a] -> [S.Set a]
conjoinClause' c' cs = map (S.union c') cs

-- | To construct a PDNF.
fromLists :: Ord a => [[a]] -> PDNF a
fromLists  = foldr disjoin minBound . map clause

-- | To construct a PDNF quickly, assuming that no list is a superset
--   of an other list.
fromListsUnsafe :: Ord a => [[a]] -> PDNF a
fromListsUnsafe  = PDNF . map S.fromList

toLists :: PDNF a -> [[a]]
toLists  = map S.toList . unPDNF

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

instance Bounded (PDNF a) where
  minBound = PDNF []
  maxBound = PDNF [S.empty]

instance Ord a => Eq (PDNF a) where
  f1 == f2 = f1 <= f2 && f2 <= f1

instance Ord a => Ord (PDNF a) where
  PDNF ant <= PDNF con
    = all (\clause -> any (`S.isSubsetOf` clause) con) ant

