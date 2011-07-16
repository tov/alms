{-# LANGUAGE
      CPP,
      DeriveDataTypeable,
      FlexibleContexts,
      FlexibleInstances,
      FunctionalDependencies,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      ScopedTypeVariables,
      TypeFamilies,
      TypeSynonymInstances,
      UndecidableInstances,
      UnicodeSyntax #-}
module AST.Ident (
  -- * Identifier classes
  Id(..),
  -- ** Tags
  Tag(..), Raw(..), Renamed(..), renamed0,
  -- *** Dirty tricks
  trivialRename, trivialRename2,
  -- * Identifiers
  -- ** High level
  TypId(..), QTypId,
  VarId(..), QVarId,
  ConId(..), QConId,
  ModId(..), QModId,
  SigId(..), QSigId,
  TyVar(..), tvUn, tvAf,
  -- ** Low level
  Path(..),
  Lid(..), QLid,
  Uid(..), QUid,
  BIdent(..), Ident,
  -- *** Operations
  isOperator, uidToLid, lidToUid,
  -- * Fresh names
  tvalphabet, freshName, freshNames,
  -- * Free and defined vars
  Occurrence, occToQLit,
  FvMap, Fv(..), Dv(..), ADDITIVE(..),
  (|*|), (|+|), (|-|), (|--|),
) where

import Env (Path(..), (:>:)(..))
import Util
import AST.Anti
import AST.Notable
import AST.Kind (QLit(..))
import qualified Syntax.Strings as Strings

import Prelude ()
import Data.Char (isAlpha, isDigit, isUpper, toUpper, toLower)
import Data.Generics (Typeable(..), Typeable1, Data(..), everywhere, mkT)
import qualified Data.List as List
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Unsafe.Coerce

class (IsBogus i, Data i) => Tag i where
  -- The trivial identity tag, used when the identity tag is
  -- insufficient to distinguish different thing
  trivialId :: i
  trivialId  = bogus
  -- Check for triviality
  isTrivial :: i -> Bool
  isTrivial  = isBogus
  -- Compare two identifiers, given a secondary criterion to use if
  -- necessary
  compareId :: i -> i -> Ordering -> Ordering

data Raw = Raw_
  deriving (Data, Typeable, Show)

newtype Renamed = Ren_ Int
  deriving (Data, Typeable, Enum, Eq, Ord)

instance Bogus Raw where
  bogus     = Raw_

instance IsBogus Raw where
  isBogus _ = True

instance Tag Raw where
  compareId _ _ = id

instance Show Renamed where
  showsPrec p (Ren_ z) = showsPrec p z

instance Bogus Renamed where
  bogus   = Ren_ 0

instance IsBogus Renamed where
  isBogus (Ren_ 0) = True
  isBogus _        = False

instance Tag Renamed where
  compareId (Ren_ 0) (Ren_ 0) next = next
  compareId (Ren_ 0) _        _    = LT
  compareId _        (Ren_ 0) _    = GT
  compareId (Ren_ a) (Ren_ b) _    = a `compare` b

renamed0 :: Renamed
renamed0  = Ren_ 1

-- | This is super dirty
trivialRename :: forall f i j. (Tag i, Tag j, Data (f i)) => f i -> f j
trivialRename  = Unsafe.Coerce.unsafeCoerce . everywhere (mkT each) where
  each :: i -> i
  each _ = Unsafe.Coerce.unsafeCoerce (trivialId :: j)

trivialRename2 :: forall f g h i j.
                 (Tag i, Tag j, Data (f (g i) (h i))) =>
                 f (g i) (h i) -> f (g j) (h j)
trivialRename2  = Unsafe.Coerce.unsafeCoerce . everywhere (mkT each) where
  each :: i -> i
  each _ = Unsafe.Coerce.unsafeCoerce (trivialId :: j)

---
--- Generic identifiers
---

-- | A module path to an identifier
type Q a i = Path (ModId i) (a i)

-- | Generic identifiers and operations
class (Typeable1 a,
       Data (a Raw), Eq (a Raw), Ord (a Raw), Bogus (a Raw),
       Data (a Renamed), Eq (a Renamed), Ord (a Renamed), Bogus (a Renamed))
      ⇒
      Id a where
  idTag         ∷ a i → i
  idName        ∷ a i → String
  ident         ∷ Tag i ⇒ String → a i
  identT        ∷ i → String → a i
  qident        ∷ Tag i ⇒ String → Path (ModId i) (a i)
  renId         ∷ i' → a i → a i'
  --
  ident        = identT bogus
  qident s     = case reverse (splitBy (=='.') s) of
    []   -> J [] (ident "")
    x:xs -> J (map ident (reverse xs)) (ident x)
  renId        = identT <$.> idName

---
--- LOW-LEVEL IDENTIFIERS
---

--
-- Lowercase
--

-- | lowercase identifiers (variables, tycons)
data Lid i
  = Lid {
      lidUnique :: !i,
      unLid     :: !String
    }
  | LidAnti Anti
  deriving (Typeable, Data)

-- | path-qualified lowecase identifiers
type QLid i = Q Lid i

instance Tag i => Eq (Lid i) where
  a == b = compare a b == EQ

instance Tag i => Ord (Lid i) where
  Lid u1 s1 `compare` Lid u2 s2 = compareId u1 u2 (compare s1 s2)
  LidAnti a `compare` _         = antierror "Lid#compare" a
  _         `compare` LidAnti a = antierror "Lid#compare" a

instance Tag i => Bogus (Lid i) where
  bogus = Lid bogus "<bogus>"

instance Id Lid where
  idTag  = lidUnique
  idName = unLid
  identT = Lid

-- | Is the lowercase identifier an infix operator?
isOperator :: Lid i -> Bool
isOperator l = case show l of
    '(':_ -> True
    _     -> False

--
-- Uppercase
--

-- | uppercase identifiers (modules, datacons)
data Uid i
  = Uid {
      uidUnique :: !i,
      unUid     :: !String
    }
  | UidAnti Anti
  deriving (Typeable, Data)

-- | path-qualified uppercase identifiers
type QUid i = Q Uid i

instance Tag i => Eq (Uid i) where
  a == b = compare a b == EQ

instance Tag i => Ord (Uid i) where
  Uid u1 s1 `compare` Uid u2 s2 = compareId u1 u2 (compare s1 s2)
  UidAnti a `compare` _         = antierror "Uid#compare" a
  _         `compare` UidAnti a = antierror "Uid#compare" a

instance Tag i => Bogus (Uid i) where
  bogus = Uid bogus "<bogus>"

instance Id Uid where
  idTag  = uidUnique
  idName = unUid
  identT = Uid

--
-- Mixed upper and lower
--

uidToLid :: Uid i -> Lid i
uidToLid (Uid ix s)  = Lid ix (mapHead toLower s)
uidToLid (UidAnti a) = antierror "uidToLid" a

lidToUid :: Lid i -> Uid i
lidToUid (Lid ix s)  = Uid ix (mapHead toUpper s)
lidToUid (LidAnti a) = antierror "lidToUid" a

-- | Bare (unqualified) identifers of unknown sort
data BIdent i = Var { unVar :: !(Lid i) }
              | Con { unCon :: !(Uid i) }
  deriving (Eq, Ord, Typeable, Data)

-- | Path-qualified identifiers
type Ident i = Q BIdent i

instance Tag i => Bogus (BIdent i) where
  bogus = Var bogus

instance Id BIdent where
  idTag (Var n) = idTag n
  idTag (Con n) = idTag n
  idName (Var n) = idName n
  idName (Con n) = idName n
  identT i s =
    if isUpperIdentifier s
      then Con (identT i s)
      else Var (identT i s)
    where
    -- | Is the string an uppercase identifier?  (Special case: @true@ and
    --   @false@ are consider uppercase.)
    --   (This code is duplicated from Syntax.Lexer!)
    isUpperIdentifier "true"  = True
    isUpperIdentifier "false" = True
    isUpperIdentifier "()"    = True
    isUpperIdentifier (c:_)   = isUpper c
    isUpperIdentifier _       = False

---
--- Specific identifiers
---

-- | Type names
newtype TypId i = TypId { unTypId ∷ Lid i }
  deriving (Typeable, Data, Eq, Ord, Bogus)

-- | Variable names
newtype VarId i = VarId { unVarId ∷ Lid i }
  deriving (Typeable, Data, Eq, Ord, Bogus)

-- | Data constructor names
newtype ConId i = ConId { unConId ∷ Uid i }
  deriving (Typeable, Data, Eq, Ord, Bogus)

-- | Module names
newtype ModId i = ModId { unModId ∷ Uid i }
  deriving (Typeable, Data, Eq, Ord, Bogus)

-- | Module type names
newtype SigId i = SigId { unSigId ∷ Uid i }
  deriving (Typeable, Data, Eq, Ord, Bogus)

-- | Qualified type names
type QTypId i = Q TypId i
-- | Qualified variable names
type QVarId i = Q VarId i
-- | Qualified data constructor names
type QConId i = Q ConId i
-- | Qualified module names
type QModId i = Q ModId i
-- | Qualified module type names
type QSigId i = Q SigId i

instance Id TypId where
  idName = idName . unTypId
  idTag  = idTag  . unTypId
  identT = TypId <$$> identT

instance Id VarId where
  idName = idName . unVarId
  idTag  = idTag  . unVarId
  identT = VarId <$$> identT

instance Id ConId where
  idName = idName . unConId
  idTag  = idTag  . unConId
  identT = ConId <$$> identT

instance Id ModId where
  idName = idName . unModId
  idTag  = idTag  . unModId
  identT = ModId <$$> identT

instance Id SigId where
  idName = idName . unSigId
  idTag  = idTag  . unSigId
  identT = SigId <$$> identT

--
-- Type variables
--

-- | Type variables include qualifiers
data TyVar i
  = TV {
      tvname :: !(Lid i),
      tvqual :: !QLit,
      tvloc  :: !Loc
    }
  | TVAnti Anti
  deriving (Eq, Ord, Typeable, Data)

tvUn, tvAf :: Tag i => String -> TyVar i
tvUn s = TV (ident s) Qu bogus
tvAf s = TV (ident s) Qa bogus

instance Locatable (TyVar i) where
  getLoc TV { tvloc = loc } = loc
  getLoc _                  = bogus

instance Relocatable (TyVar i) where
  setLoc tv@TV { } loc = tv { tvloc = loc }
  setLoc tv        _   = tv

instance Tag i => Bogus (TyVar i) where
  bogus = TV bogus Qa bogus

instance Id TyVar where
  idName (TV n _ _)  = idName n
  idName (TVAnti a)  = antierror "idName" a
  idTag (TV n _ _)   = idTag n
  idTag (TVAnti a)   = antierror "idTag" a
  identT i n         = TV (identT i n) Qa bogus
  renId i (TV n q l) = TV (renId i n) q l
  renId _ (TVAnti a) = antierror "renId" a

---
--- 'Show' INSTANCES
---

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

instance Show (TypId i) where showsPrec p = showsPrec p . unTypId
instance Show (VarId i) where showsPrec p = showsPrec p . unVarId
instance Show (ConId i) where showsPrec p = showsPrec p . unConId
instance Show (ModId i) where showsPrec p = showsPrec p . unModId
instance Show (SigId i) where showsPrec p = showsPrec p . unSigId

instance Show (TyVar i) where
  showsPrec _ (TV x Qu _)  = showString Strings.unlimited . showString (unLid x)
  showsPrec _ (TV x Qa _)  = showString Strings.affine . showString (unLid x)
  showsPrec _ (TVAnti a)   = showString Strings.affine . shows a

instance Viewable (Path (ModId i) (BIdent i)) where
  type View (Path (ModId i) (BIdent i)) = Either (QLid i) (QUid i)
  view (J p (Var n)) = Left (J p n)
  view (J p (Con n)) = Right (J p n)

-- | Simple keys embed into path keyspace
instance (Ord p, (:>:) k k') =>
         (:>:) (Path p k) k'  where liftKey = J [] . liftKey

instance Tag i => (:>:) (BIdent i) (Lid i) where liftKey = Var
instance Tag i => (:>:) (BIdent i) (Uid i) where liftKey = Con

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
type FvMap i = M.Map (QVarId i) Occurrence

-- | The free variables analysis
class Tag i => Fv a i | a -> i where
  fv :: a -> FvMap i

-- | The defined variables analysis
class Tag i => Dv a i | a -> i where
  qdv :: a -> S.Set (QVarId i)
  dv  :: a -> S.Set (VarId i)

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
(|*|), (|+|) :: Tag i => FvMap i -> FvMap i -> FvMap i
(|*|) = M.unionWith (+)
(|+|) = M.unionWith max

(|-|) :: Tag i => FvMap i -> QVarId i -> FvMap i
(|-|)  = flip M.delete

(|--|) :: Tag i => FvMap i -> S.Set (QVarId i) -> FvMap i
(|--|)  = S.fold M.delete

