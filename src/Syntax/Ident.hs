{-# LANGUAGE
      CPP,
      DeriveDataTypeable,
      FlexibleInstances,
      FunctionalDependencies,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      ScopedTypeVariables,
      TypeFamilies,
      TypeSynonymInstances,
      UndecidableInstances,
      UnicodeSyntax #-}
module Syntax.Ident (
  -- * Identifier classes
  Id(..), Raw(..), Renamed(..), renamed0,
  -- ** Dirty tricks
  trivialRename, trivialRename2,
  -- * Identifiers 
  Path(..),
  Lid(..), Uid(..), BIdent(..),
  Ident, QLid, QUid,
  TyVar(..), tvUn, tvAf,
  tvalphabet, freshName, freshNames,
  isOperator,
  lid, uid, renLid, renUid, qlid, quid,
  uidToLid, lidToUid,
  -- * Free and defined vars
  Occurrence, occToQLit,
  FvMap, Fv(..), Dv(..), ADDITIVE(..),
  (|*|), (|+|), (|-|), (|--|),
) where

import Env (Path(..), (:>:)(..))
import Util
import Syntax.Anti
import Syntax.Notable
import Syntax.Kind (QLit(..))
import qualified Syntax.Strings as Strings

import Prelude ()
import Data.Char (isAlpha, isDigit, toUpper, toLower)
import Data.Generics (Typeable(..), Data(..), everywhere, mkT)
import qualified Data.List as List
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Unsafe.Coerce

class Data i => Id i where
  -- The trivial identity tag, used when the identity tag is
  -- insufficient to distinguish different thing
  trivialId :: i
  -- Check for triviality
  isTrivial :: i -> Bool
  -- Compare two identifiers, given a secondary criterion to use if
  -- necessary
  compareId :: i -> i -> Ordering -> Ordering

data Raw = Raw_
  deriving (Data, Typeable, Show)

newtype Renamed = Ren_ Int
  deriving (Data, Typeable, Enum, Eq, Ord)

instance Show Renamed where
  showsPrec p (Ren_ z) = showsPrec p z

instance Id Raw where
  trivialId     = Raw_
  isTrivial     = const True
  compareId _ _ = id

instance Id Renamed where
  trivialId          = Ren_ 0
  isTrivial (Ren_ 0) = True
  isTrivial (Ren_ _) = False
  compareId (Ren_ 0) (Ren_ 0) next = next
  compareId (Ren_ 0) _        _    = LT
  compareId _        (Ren_ 0) _    = GT
  compareId (Ren_ a) (Ren_ b) _    = a `compare` b

renamed0 :: Renamed
renamed0  = Ren_ 1

-- | This is super dirty
trivialRename :: forall f i j. (Id i, Id j, Data (f i)) => f i -> f j
trivialRename  = Unsafe.Coerce.unsafeCoerce . everywhere (mkT each) where
  each :: i -> i
  each _ = Unsafe.Coerce.unsafeCoerce (trivialId :: j)

trivialRename2 :: forall f g h i j.
                 (Id i, Id j, Data (f (g i) (h i))) =>
                 f (g i) (h i) -> f (g j) (h j)
trivialRename2  = Unsafe.Coerce.unsafeCoerce . everywhere (mkT each) where
  each :: i -> i
  each _ = Unsafe.Coerce.unsafeCoerce (trivialId :: j)

-- IDENTIFIERS

-- | lowercase identifiers (variables, tycons)
data Lid i
  = Lid {
      lidUnique :: !i,
      unLid     :: !String
    }
  | LidAnti Anti
  deriving (Typeable, Data)

instance Id i => Eq (Lid i) where
  a == b = compare a b == EQ

instance Id i => Ord (Lid i) where
  Lid u1 s1 `compare` Lid u2 s2 = compareId u1 u2 (compare s1 s2)
  LidAnti a `compare` _         = antierror "Lid#compare" a
  _         `compare` LidAnti a = antierror "Lid#compare" a

-- | uppercase identifiers (modules, datacons)
data Uid i
  = Uid {
      uidUnique :: !i,
      unUid     :: !String
    }
  | UidAnti Anti
  deriving (Typeable, Data)

instance Id i => Eq (Uid i) where
  a == b = compare a b == EQ

instance Id i => Ord (Uid i) where
  Uid u1 s1 `compare` Uid u2 s2 = compareId u1 u2 (compare s1 s2)
  UidAnti a `compare` _         = antierror "Uid#compare" a
  _         `compare` UidAnti a = antierror "Uid#compare" a

-- | bare (unqualified) identifers
data BIdent i = Var { unVar :: !(Lid i) }
              | Con { unCon :: !(Uid i) }
  deriving (Eq, Ord, Typeable, Data)

-- | path-qualified uppercase identifiers
type QUid i = Path (Uid i) (Uid i)
-- | path-qualified lowecase identifiers
type QLid i = Path (Uid i) (Lid i)
-- | path-qualified identifiers
type Ident i = Path (Uid i) (BIdent i)

-- | Type variables include qualifiers
data TyVar i
  = TV {
      tvname :: !(Lid i),
      tvqual :: !QLit,
      tvloc  :: !Loc
    }
  | TVAnti Anti
  deriving (Eq, Ord, Typeable, Data)

instance Locatable (TyVar i) where
  getLoc TV { tvloc = loc } = loc
  getLoc _                  = bogus

instance Relocatable (TyVar i) where
  setLoc tv@TV { } loc = tv { tvloc = loc }
  setLoc tv        _   = tv

lid :: Id i => String -> Lid i
lid = Lid trivialId

uid :: Id i => String -> Uid i
uid = Uid trivialId

renLid :: i -> Lid i0 -> Lid i
renLid = Lid <$.> unLid

renUid :: i -> Uid i0 -> Uid i
renUid = Uid <$.> unUid

uidToLid :: Uid i -> Lid i
uidToLid (Uid ix s)  = Lid ix (mapHead toLower s)
uidToLid (UidAnti a) = antierror "uidToLid" a

lidToUid :: Lid i -> Uid i
lidToUid (Lid ix s)  = Uid ix (mapHead toUpper s)
lidToUid (LidAnti a) = antierror "lidToUid" a

tvUn, tvAf :: Id i => String -> TyVar i
tvUn s = TV (lid s) Qu bogus
tvAf s = TV (lid s) Qa bogus

-- | Is the lowercase identifier an infix operator?
isOperator :: Lid i -> Bool
isOperator l = case show l of
    '(':_ -> True
    _     -> False

-- | Sugar for generating AST for qualified lowercase identifers
qlid :: Id i => String -> QLid i
qlid s = case reverse (splitBy (=='.') s) of
           []   -> J [] (lid "")
           x:xs -> J (map uid (reverse xs)) (lid x)

-- | Sugar for generating AST for qualified uppercase identifers
quid :: Id i => String -> QUid i
quid s = case reverse (splitBy (=='.') s) of
           []   -> J [] (uid "")
           x:xs -> J (map uid (reverse xs)) (uid x)

instance Show (Lid i) where
  showsPrec _ (Lid _ s) =
    case s of
      '_':_             -> (s++)
      c  :_ | isAlpha c -> (s++)
      c  :_ | isDigit c -> (s++)
      _  :_ | head s == '*' || last s == '*'
                        -> ("( "++) . (s++) . (" )"++)
      _                 -> ('(':) . (s++) . (')':)
    {-
    . let z = Unsafe.Coerce.unsafeCoerce i :: Renamed in
         if z == Unsafe.Coerce.unsafeCoerce Raw_
           then id
           else showChar '[' . shows z . showChar ']'
  -}
  showsPrec p (LidAnti a) = showsPrec p a

instance Show (Uid i) where
  showsPrec _ (Uid _ s)   = (s++)
  showsPrec p (UidAnti a) = showsPrec p a

instance Show (BIdent i) where
  showsPrec p (Var x) = showsPrec p x
  showsPrec p (Con k) = showsPrec p k

instance Show (TyVar i) where
  showsPrec _ (TV x Qu _)  = showString Strings.unlimited . shows x
  showsPrec _ (TV x Qa _)  = showString Strings.affine . shows x
  showsPrec _ (TVAnti a)   = showString Strings.affine . shows a

instance Viewable (Path (Uid i) (BIdent i)) where
  type View (Ident i) = Either (QLid i) (QUid i)
  view (J p (Var n)) = Left (J p n)
  view (J p (Con n)) = Right (J p n)

-- | Simple keys embed into path keyspace
instance (Ord p, (:>:) k k') =>
         (:>:) (Path p k) k'  where liftKey = J [] . liftKey

instance Id i => (:>:) (BIdent i) (Lid i) where liftKey = Var
instance Id i => (:>:) (BIdent i) (Uid i) where liftKey = Con

---
--- Name generation
---

-- | Given a base name, produces the list of names starting with the
--   base name, then with a prime added, and then with numeric
--   subscripts increasing from 1.
namesFrom ∷ String → [String]
namesFrom s = [ c:n | n ← "" : map numberSubscript [0 ..], c ← s ]

-- | Given a natural number, represent it as a string of number
--   subscripts.
numberSubscript ∷ Int → String
numberSubscript 0  = [head Strings.digits]
numberSubscript n0
  | n0 < 0         = error "BUG! numberSubscript requires non-negative Int"
  | otherwise      = reverse $ List.unfoldr each n0 where
  each 0 = Nothing
  each n = Just (Strings.digits !! ones, rest)
             where (rest, ones) = n `divMod` 10

-- | Clear the primes and subscripts from the end of a name
clearScripts ∷ String → String
clearScripts n = case reverse (dropWhile (`elem` scripts) (reverse n)) of
  [] → n
  n' → n'
  where scripts = "'′" ++ Strings.unicodeDigits ++ Strings.asciiDigits

tvalphabet ∷ [String]
tvalphabet = namesFrom Strings.tvNames

-- | @freshName sugg qlit avoid cands@ attempts to generate a fresh
--   type variable name as follows:
--
--   * if @sugg@ is @Here n@, then it returns @n@ if @n@ is not in
--     @avoid@, and otherwise subscripts @n@ until if finds a fresh
--     name.
--
--   * Otherwise, return the first name from @cands@ that isn't in
--     @avoid@.
--
freshName ∷ Optional t ⇒ t String → [String] → [String] → String
freshName pn avoid cands = case coerceOpt pn of
  Just n
    | okay n    → n
    | otherwise → takeFrom (namesFrom (clearScripts n))
  Nothing       → takeFrom (cands ++ namesFrom "a")
  where
    avoidSet = S.fromList (Strings.normalizeChar <$$> avoid)
    takeFrom = head . filter okay
    okay n   = S.notMember (Strings.normalizeChar <$> n) avoidSet

-- | Like 'freshName', but produces a list of fresh names
freshNames ∷ Optional t ⇒ [t String] → [String] → [String] → [String]
freshNames []       _     _     = []
freshNames (pn:pns) avoid cands =
  let n' = freshName pn avoid cands
   in n' : freshNames pns (n':avoid) cands

---
--- FREE VARIABLES and OCCURRENCE ANALYSIS
---

-- | A count of maximum variables occurrences
type Occurrence = Int

-- | The qualifier bound for a given number of occurrences
occToQLit ∷ Occurrence → QLit
occToQLit n = if n > 1 then Qu else Qa

-- | Our free variables function returns not merely a set,
-- but a map from names to a count of maximum occurrences.
type FvMap i = M.Map (QLid i) Occurrence

-- | The free variables analysis
class Id i => Fv a i | a -> i where
  fv :: a -> FvMap i

-- | The defined variables analysis
class Id i => Dv a i | a -> i where
  qdv :: a -> S.Set (QLid i)
  dv  :: a -> S.Set (Lid i)

  qdv  = S.mapMonotonic (J []) . dv
  dv a = S.fromDistinctAscList [ v | J [] v <- S.toAscList (qdv a) ]

instance Fv a i => Fv [a] i where
  fv = foldr (|+|) M.empty . map fv

instance Dv a i => Dv [a] i where
  dv = S.unions . map dv

instance Fv a i => Fv (Maybe a) i where
  fv = maybe mempty fv

instance Dv a i => Dv (Maybe a) i where
  dv = maybe mempty dv

newtype ADDITIVE a = ADDITIVE [a]

instance Fv a i => Fv (ADDITIVE a) i where
  fv (ADDITIVE a) = foldr (|+|) M.empty (map fv a)

-- | Used by the free variables analysis
(|*|), (|+|) :: Id i => FvMap i -> FvMap i -> FvMap i
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: Id i => FvMap i -> QLid i -> FvMap i
(|-|)  = flip M.delete

(|--|) :: Id i => FvMap i -> S.Set (QLid i) -> FvMap i
(|--|)  = S.fold M.delete

