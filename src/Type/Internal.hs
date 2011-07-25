{-# LANGUAGE TypeFamilies #-}
-- | The internal representation of types, created by the type checker
--   from the syntactic types in 'AST.Type'.
module Type.Internal (
  -- * Data definitions
  -- ** Types
  Quant(..), TyVar(..), Type(..), TyCon(..),
  -- ** Qualifiers
  QLit(..), QExp(..), QExpV,
  -- ** Type patterns
  TyPat(..),
  -- ** Kind re-exports
  Variance(..), Lattice(..), BoundedLattice(..), isQVariance,
  -- ** Names
  Name, TypId, QTypId, ConId, QConId, RowLabel, RecLabel,

  -- * Qualifiers
  Qualifier(..), qlitexp, qvarexp, extractQual, liftVQExp, mapQExp,

  -- * Type constructors
  abstractTyCon, mkTC,
  -- ** Built-in
  tcUnit, tcInt, tcChar, tcFloat, tcString, tcExn, tcTuple, tcFun,
  tcUn, tcAf, tcJoin, tcRowEnd, tcRecord, tcVariant, tcRowMap,
  tcRowDots, tcRowHole,
  -- ** Convenient constructors and projections
  fvTy, bvTy, fromFreeTV,
  -- ** Pre-constructed types
  tyNulOp, tyUnOp, tyBinOp,
  tyFun, tyArr, tyLol, tyTuple, tyQLit,
  tyAf, tyUn, tyUnit, tyInt, tyChar, tyFloat, tyString, tyExn,
  tyRowEnd, tyRowMap, tyRowHole,
  (.->.), (.-*.), (.*.),
  -- *** For testing
  tcCycle, tcConst, tcIdent, tcConsTup, tcOption, tcIdfun,

  -- * Standard forms
  standardizeType, standardizeQuals,

  -- * Unfolds and folds
  -- ** Type folding
  foldType, foldTypeM, foldTypeEnv, mkBvF, mkQuF, mkMuF,
  -- ** Unfolds
  unfoldQu, unfoldRow, unfoldMu,
  -- ** Row operations
  foldRow, sortRow,

  -- * Locally nameless
  openTy, openTyN, closeTy, lcTy, lcTyK,
  closeRec, closeQuant,

  -- * Varieties
  TyConVariety(..), varietyOf,

  module Data.Empty,
) where

import Util
import Util.MonadRef
import Data.Empty
import Data.Lattice
import Error
import qualified Env
import qualified AST
import AST ( QLit(..), Variance(..), isQVariance )

import Prelude ()
import Control.Monad.ST
import Data.Generics (Typeable, Data)
import Data.STRef (STRef)
import qualified Data.List as List
import qualified Data.Map  as M
import qualified Data.Set  as S

---
--- DATA TYPES
---

-- | Everything should be renamed by now
type R        = AST.Renamed
type TypId    = AST.TypId R
type QTypId   = AST.QTypId R
type ConId    = AST.ConId R
type QConId   = AST.QConId R
type RowLabel = AST.Uid R
type RecLabel = AST.Lid R

-- | Optional names that don't affect α equivalence
type Name = Perhaps String

-- | Locally-nameless–style type variable occurrences in internal types
data TyVar tv
  -- | A free type variable
  = Free !tv
  -- | A bound type variable
  | Bound !Int !Int !Name
  deriving (Eq, Ord, Functor, Typeable, Data)

-- | Quantifiers
data Quant
  -- | Universal quantifier
  = Forall
  -- | Existential quantifier
  | Exists
  deriving (Eq, Ord, Typeable, Data)

-- | The internal representation of a type
data Type tv
  -- | A free type variable
  = TyVar !(TyVar tv)
  -- | A quantified (all or ex) type
  | TyQu  !Quant ![(Name, QLit)] !(Type tv)
  -- | A recursive (mu) type
  | TyMu  !Name !(Type tv)
  -- | A row type
  | TyRow !RowLabel !(Type tv) !(Type tv)
  -- | The application of a type constructor (possibly nullary).
  | TyApp !TyCon ![Type tv]
  deriving (Functor, Typeable, Data)

-- | Internal qualifier expressions
data QExp tv
  -- | The type qualifier expression
  = QeA
  -- | The join of a set of type variables
  | QeU !(S.Set tv)
  deriving (Eq, Typeable, Data)

-- | Qualifier expressions containing bound variables
type QExpV tv = QExp (TyVar tv)

-- | Information about a type constructor
data TyCon
  = TyCon {
      -- | Unique ID
      tcId        ∷ !Int,
      -- | Printable name
      tcName      ∷ !QTypId,
      -- | Variances for parameters, and correct length
      tcArity     ∷ ![Variance],
      -- | Bounds for parameters
      tcBounds    ∷ ![QLit],
      -- | Guards recursive types
      tcGuards    ∷ ![Bool],
      -- | Qualifier as a function of parameters
      tcQual      ∷ !(QExp Int),
      -- | For pattern-matchable types, the data constructors,
      -- where type parameters are bound at level 0
      tcCons      ∷ !(Env.Env ConId (Maybe (Type Empty))),
      -- | For type operators, the next head reduction
      tcNext      ∷ !(Maybe [([TyPat], Type Empty)])
    }
  deriving (Typeable, Data)

-- | A type pattern, for defining type operators
data TyPat
  -- | A type variable, matching any type and binding
  = TpVar !Name
  -- | A type application node, matching the given constructor
  --   and its parameters
  | TpApp !TyCon ![TyPat]
  -- | A row type pattern
  | TpRow !Name
  deriving (Typeable, Data)

instance Eq TyCon where
  tc == tc'  =  tcId tc == tcId tc'

instance Ord TyCon where
  compare tc tc'  = compare (tcName tc) (tcName tc')

---
--- Abstracting type constructors
---

-- | Remove the representation from a type constructor
abstractTyCon ∷ TyCon → TyCon
abstractTyCon tc = tc { tcCons = mempty, tcNext = Nothing }

---
--- Built-in types
---

class ExtTC r where
  extTC ∷ TyCon → r

instance ExtTC TyCon where
  extTC = id

instance ExtTC r ⇒ ExtTC (QTypId → r) where
  extTC tc x = extTC (tc { tcName = x })

instance (v ~ Variance, ql ~ QLit, ExtTC r) ⇒
         ExtTC ([(v, ql, Bool)] → r) where
  extTC tc x = extTC tc {
                 tcArity  = sel1 <$> x,
                 tcBounds = sel2 <$> x,
                 tcGuards = sel3 <$> x
               }

instance (tv ~ Int, ExtTC r) ⇒ ExtTC (QExp tv → r) where
  extTC tc x = extTC (tc { tcQual = x })

instance (a ~ Type Empty, ExtTC r) ⇒
         ExtTC (Env.Env ConId (Maybe a) → r) where
  extTC tc x = extTC (tc { tcCons = x })

instance (t ~ Type Empty, ExtTC r) ⇒
         ExtTC ([([TyPat], t)] → r) where
  extTC tc x = extTC (tc { tcNext = Just x })

mkTC ∷ ExtTC r ⇒ Int → AST.QTypId R → r
mkTC i ql
  = extTC TyCon {
    tcId        = i,
    tcName      = ql,
    tcArity     = [],
    tcBounds    = [],
    tcGuards    = [],
    tcQual      = minBound,
    tcCons      = Env.empty,
    tcNext      = Nothing
  }

internalTC ∷ ExtTC r ⇒ Int → String → r
internalTC i s = mkTC i (AST.J [] (AST.identT (AST.Ren_ i) s))

tcUnit, tcInt, tcChar, tcFloat, tcString,
  tcExn, tcUn, tcAf, tcJoin, tcTuple, tcFun,
  tcRowEnd, tcRecord, tcVariant, tcRowMap, tcRowDots, tcRowHole ∷ TyCon

tcFun        = internalTC (-1) "->"     (qvarexp 1)
                                        [(Contravariant, Qa, False),
                                         (QCovariant,    Qa, False),
                                         (Covariant,     Qa, False)]
tcUnit       = internalTC (-2) "unit"
                 (Env.fromList [(AST.ident "()" ∷ ConId, Nothing)])
tcInt        = internalTC (-3) "int"
tcChar       = internalTC (-4) "char"
tcFloat      = internalTC (-5) "float"
tcString     = internalTC (-6) "string"
tcExn        = internalTC (-7) "exn"    QeA
tcUn         = internalTC (-8) "U"
tcAf         = internalTC (-9) "A"      QeA
tcJoin       = internalTC (-10) "\\/"   (qvarexp 0 ⊔ qvarexp 1)
                                        [(Covariant,     Qa, False),
                                         (Covariant,     Qa, False)]
tcTuple      = internalTC (-11) "*"     (qvarexp 0 ⊔ qvarexp 1)
                                        [(Covariant,     Qa, False),
                                         (Covariant,     Qa, False)]
tcRowEnd     = internalTC (-12) "rowend"
tcVariant    = internalTC (-13) "variant" (qvarexp 0)
                                          [(Covariant, Qa, False)]
tcRecord     = internalTC (-14) "record"  (qvarexp 1)
                                          [(QCovariant, Qa, False),
                                           (Covariant, Qa, False)]
tcRowMap     = internalTC (-15) "rowmap#"  (qvarexp 0 ⊔ qvarexp 1)
                                           [(Covariant, Qa, False),
                                           (Invariant, Qa, False)]
tcRowDots    = internalTC (-16) "rowdots#" (qvarexp 0)
                                           [(Covariant, Qa, True)]
tcRowHole    = internalTC (-17) "rowhole#" (qvarexp 0)
                                           [(Covariant, Qa, True)]

-- Types for testing

tcCycle, tcConst, tcIdent, tcConsTup, tcOption, tcIdfun ∷ TyCon
tcCycle      = internalTC (-51) "cycle" [(Invariant,     Qa, True)]
tcConst      = internalTC (-52) "const" [(Omnivariant, Qa, False)]
                 [([TpVar Nope], tyUnit)]
tcIdent      = internalTC (-53) "ident" (qvarexp 0)
                                        [(Covariant, Qa, False)]
                 [([TpVar Nope], TyVar (Bound 0 0 Nope))]
tcConsTup    = internalTC (-54) "cons"  (qvarexp 0 ⊔ qvarexp 1)
                                        [(Covariant, Qa, False),
                                         (Covariant, Qa, False)]
                 [([TpVar Nope, TpApp tcTuple [TpVar Nope, TpVar Nope]],
                   TyApp tcTuple [TyApp tcConsTup [TyVar (Bound 0 0 Nope),
                                                   TyVar (Bound 0 1 Nope)],
                                  TyVar (Bound 0 2 Nope)]),
                  ([TpVar Nope, TpVar Nope],
                   TyApp tcTuple [TyVar (Bound 0 0 Nope),
                                  TyVar (Bound 0 1 Nope)])]
tcOption     = internalTC (-55) "option" (qvarexp 0)
                                         [(Covariant, Qa, False)]
                 (Env.fromList [(AST.ident "None" ∷ ConId, Nothing),
                                (AST.ident "Some", Just (bvTy 0 0 Nope))])
tcIdfun      = internalTC (-55) "idfun" [(Invariant, Qa, False)]
                 (Env.fromList [(AST.ident "Mono" ∷ ConId,
                                 Just (bvTy 0 0 Nope .->. bvTy 0 0 Nope)),
                                (AST.ident "Poly",
                                 Just (TyQu Forall [(Nope, Qa)]
                                        (bvTy 0 0 Nope .->. bvTy 0 0 Nope)))])

---
--- Convenience constructors
---

-- | Make a free type variable into a type
fvTy ∷ tv → Type tv
fvTy = TyVar . Free

-- | Make a bound type variable type
bvTy ∷ Optional f ⇒ Int → Int → f String → Type tv
bvTy i j n = TyVar (Bound i j (foldOpt Nope Here n))

-- | Project a free type variable from a 'TyVar'
fromFreeTV ∷ TyVar tv → tv
fromFreeTV (Free r)     = r
fromFreeTV _            = throw $
  almsBug StaticsPhase "fromFreeTV" "Got bound type variable"

-- | Make a type from a nullary type constructor
tyNulOp ∷ TyCon → Type tv
tyNulOp tc = TyApp tc []

-- | Make a type from a unary type constructor
tyUnOp ∷ TyCon → Type tv → Type tv
tyUnOp tc t1 = TyApp tc [t1]

-- | Make a type from a binary type constructor
tyBinOp ∷ TyCon → Type tv → Type tv → Type tv
tyBinOp tc t1 t2 = TyApp tc [t1, t2]

-- | A function type
tyFun ∷ Qualifier qe tv ⇒ Type tv → qe → Type tv → Type tv
tyFun t1 qe t2 = TyApp tcFun [t1, qualToType qe, t2]

-- | Constructor for unlimited arrow types
tyArr ∷ Type tv → Type tv → Type tv
tyArr = tyFun <-> Qu

-- | Constructor for affine arrow types
tyLol ∷ Type tv → Type tv → Type tv
tyLol = tyFun <-> Qa

-- | Type from a 'QLit'
tyQLit ∷ QLit → Type tv
tyQLit Qa = tyAf
tyQLit Qu = tyUn

-- | Binary types
tyTuple, tyRowMap ∷ Type tv → Type tv → Type tv

tyTuple  = tyBinOp tcTuple
tyRowMap = tyBinOp tcRowMap

-- | Nullary types
tyAf, tyUn, tyUnit, tyInt, tyChar, tyFloat, tyString, tyExn,
  tyRowEnd, tyRowHole ∷ Type tv

tyAf     = tyNulOp tcAf
tyUn     = tyNulOp tcUn
tyUnit   = tyNulOp tcUnit
tyInt    = tyNulOp tcInt
tyChar   = tyNulOp tcChar
tyFloat  = tyNulOp tcFloat
tyString = tyNulOp tcString
tyExn    = tyNulOp tcExn
tyRowEnd = tyNulOp tcRowEnd
tyRowHole= tyNulOp tcRowHole

(.*.), (.->.), (.-*.) ∷ Type tv → Type tv → Type tv
(.*.)    = tyTuple
(.->.)   = tyArr
(.-*.)   = tyLol

infixr 6 .->., .-*., `tyArr`, `tyLol`
infixl 7 .*., `tyTuple`

---
--- Qualifiers
---

instance Ord tv ⇒ Lattice (QExp tv) where
  QeA     ⊔ _        = QeA
  _       ⊔ QeA      = QeA
  QeU tvs ⊔ QeU tvs' = QeU (tvs `S.union` tvs')
  --
  QeA     ⊓ qe'      = qe'
  qe      ⊓ QeA      = qe
  QeU tvs ⊓ QeU tvs' = QeU (tvs `S.intersection` tvs')
  --
  _       ⊑ QeA      = True
  QeA     ⊑ _        = False
  QeU tvs ⊑ QeU tvs' = tvs `S.isSubsetOf` tvs'

instance Bounded (QExp tv) where
  minBound = QeU S.empty
  maxBound = QeA

class Qualifier q tv | q → tv where
  qualToType     ∷ q → Type tv
  qualifierEnv   ∷ Ord tv ⇒ [[QLit]] → q → QExpV tv
  qualifier      ∷ Ord tv ⇒ q → QExpV tv
  qualifierEnv   = const qualifier
  qualifier      = qualifierEnv []

instance Qualifier q tv ⇒ Qualifier (Maybe q) tv where
  qualToType   = maybe tyUn qualToType
  qualifierEnv = maybe minBound . qualifierEnv

instance (Ord tv, Qualifier q tv) ⇒ Qualifier [q] tv where
  qualToType   = qualToType . qualifier
  qualifierEnv = bigJoin <$$> map . qualifierEnv

instance Qualifier QLit tv where
  qualToType Qa     = tyAf
  qualToType Qu     = tyUn
  qualifier Qa      = QeA
  qualifier Qu      = QeU S.empty

instance Qualifier AST.Occurrence tv where
  qualToType = qualToType . AST.occToQLit
  qualifier  = qualifier . AST.occToQLit

instance Ord tv ⇒ Qualifier (Type tv) tv where
  qualToType        = qualToType . qualifier
  qualifierEnv env0 = foldTypeEnv env0 fquant fbvar ffvar fcon frow frec
    where
    fquant ∷ Quant → [(Name, QLit)] → ([QLit] → (QExpV tv → QExpV tv) → a) → a
    frec   ∷ Name → (QLit → (QExpV tv → QExpV tv) → a) → a
    fquant Forall αs k     = k (Qu <$ αs) bumpQExp
    fquant Exists αs k     = k (snd <$> αs) bumpQExp
    fbvar _ _    (Just Qu) = qlitexp Qu
    fbvar (i,j) n _        = qvarexp (Bound i j n)
    ffvar                  = qvarexp . Free
    fcon tc qes            = extractQual (tcQual tc) qes
    frow _ qe1 qe2         = qe1 ⊔ qe2
    frec _ k               = k Qu bumpQExp
    --
    bumpQExp QeA           = QeA
    bumpQExp (QeU tvs)     = QeU (S.map (bumpVar (-1)) tvs)
    bumpVar _ (Free r)     = Free r
    bumpVar k (Bound i j n)= Bound (i + k) j n

instance Qualifier (QExpV tv) tv where
  qualToType QeA       = TyApp tcAf []
  qualToType (QeU tvs)
    | S.null tvs       = TyApp tcUn []
    | otherwise        = foldr1 (\t1 t2 → TyApp tcJoin [t1, t2])
                                (TyVar <$> S.toList tvs)
  qualifier = id

instance Qualifier (S.Set tv) tv where
  qualifier αs   = QeU (S.mapMonotonic Free αs)
  qualToType αs  = qualToType (QeU (S.mapMonotonic Free αs))

-- | Make a qualifier expression from a single literal
qlitexp ∷ QLit → QExp tv
qlitexp Qa = QeA
qlitexp Qu = QeU S.empty

-- | Make a qualifier expression from a single type variable
qvarexp ∷ tv → QExp tv
qvarexp = QeU . S.singleton

-- | Build a qualifier from a list of qualifiers using an
--   integer-numbered qualifier.
extractQual ∷ Ord tv ⇒ QExp Int → [QExp tv] → QExp tv
extractQual QeA      _   = QeA
extractQual (QeU zs) qes = bigJoin (fst <$> filter ((`elem` zs) . snd)
                                                   (zip qes [0 ..]))

-- | Lift a free-variable q-expression to a 'QExpV'
liftVQExp ∷ QExp tv → QExpV tv
liftVQExp QeA           = QeA
liftVQExp (QeU αs)      = QeU (S.mapMonotonic Free αs)

-- | Modify the set of a 'QeU' 'QExp"
mapQExp ∷ (S.Set tv → S.Set tv') → QExp tv → QExp tv'
mapQExp _ QeA      = QeA
mapQExp f (QeU αs) = QeU (f αs)

---
--- Folds and unfolds
---

foldTypeEnv
         ∷ Ord tv ⇒
           -- | Initial environment
           [[s]] →
           -- | For quantifiers
           (∀a. Quant → [(Name, QLit)] → ([s] → (r → r) → a) → a) →
           -- | For bound variables
           ((Int, Int) → Name → Maybe s → r) →
           -- | For free variables
           (tv → r) →
           -- | For constructor applications
           (TyCon → [r] → r) →
           -- | For row type labels
           (RowLabel → r → r → r) →
           -- | For recursive types
           (∀a. Name → (s → (r → r) → a) → a) →
           -- | Type to fold
           Type tv →
           r
foldTypeEnv env0 fquant fbvar ffvar fcon frow frec σ0 =
  runReader (loop σ0) env0
  where
  loop (TyQu q αs σ)            =
    fquant q αs $ \ss f → f `liftM` local (ss:) (loop σ)
  loop (TyVar (Bound i j n))    = do
    env ← ask
    return (fbvar (i, j) n (look i j env))
  loop (TyVar (Free v))         = return (ffvar v)
  loop (TyApp tc ts)            =
    fcon tc <$> sequence
      [ if isQVariance v
          then loop (qualToType t)
          else loop t
      | t ← ts
      | v ← tcArity tc ]
  loop (TyRow n t1 t2)          =
    frow n `liftM` loop t1 `ap` loop t2
  loop (TyMu n t)               =
    frec n (\s f → f `liftM` local ([s]:) (loop t))
  --
  look i j env
    | rib:_ ← drop i env
    , elt:_ ← drop j rib = Just elt
  look _ _ _             = Nothing

foldType ∷ Ord tv ⇒
           -- | For quantifiers
           (∀a. Quant → [(Name, QLit)] → ([s] → (r → r) → a) → a) →
           -- | For bound variables
           ((Int, Int) → Name → Maybe s → r) →
           -- | For free variables
           (tv → r) →
           -- | For constructor applications
           (TyCon → [r] → r) →
           -- | For row type labels
           (RowLabel → r → r → r) →
           -- | For recursive types
           (∀a. Name → (s → (r → r) → a) → a) →
           -- | Type to fold
           Type tv →
           r
foldType = foldTypeEnv []

-- | Helper for constructing bound variable case for 'foldType'
mkBvF   ∷ (Int → Int → Name → r) →
          (Int, Int) → Name → a → r
mkBvF f (i, j) pn _ = f i j pn

-- | Helper for constructing quantifier case for 'foldType'
mkQuF
  ∷ (Quant → [(Name, QLit)] → r → s) →
    (∀a. Quant → [(Name, QLit)] → ([(Int, Int)] → (r → s) → a) → a)
mkQuF f q αs k = k [ (0, j) | j ← [0 .. length αs - 1] ] (f q αs)

-- | Helper for constructing recursive case for 'foldType'
mkMuF ∷ (Name → r → s) →
        (∀a. Name → ((Int, Int) → (r → s) → a) → a)
mkMuF f pn k = k (0, 0) (f pn)

foldTypeM ∷ (Monad m, Ord tv) ⇒
            -- | For quantifiers
            (∀a. Quant → [(Name, QLit)] → ([s] → (r → m r) → a) → a) →
            -- | For bound variables
            ((Int, Int) → Name → Maybe s → m r) →
            -- | For free variables
            (tv → m r) →
            -- | For constructor applications
            (TyCon → [r] → m r) →
            -- | For row type labels
            (RowLabel → r → r → m r) →
            -- | For recursive types
            (∀a. Name → (s → (r → m r) → a) → a) →
            -- | Type to fold
            Type tv →
            m r
foldTypeM fquant fbvar ffvar fapp frow frec =
  foldType (\qu ns k → fquant qu ns (\s k' → k s (>>= k')))
           fbvar
           ffvar
           (\tc mrs → sequence mrs >>= fapp tc)
           (\lab mr1 mr2 → mr1 >>= \r1 → mr2 >>= frow lab r1)
           (\n k → frec n (\s k' → k s (>>= k')))

--
-- Other unfolds
--

-- To strip off as many of the specified quantifier as possible,
-- building a qualifier bound environment for the layers.
unfoldQu ∷ Quant → Type tv → ([[QLit]], Type tv)
unfoldQu u0 = first reverse . loop where
  loop (TyQu u tvs t)
    | u0 == u || lcTyK 0 t = first (map snd tvs:) (loop t)
  loop t                   = ([], t)

-- To find the labels and fields of a row type, and the extension,
-- in standard order
unfoldRow ∷ Type tv → ([(RowLabel, Type tv)], Type tv)
unfoldRow = first (List.sortBy (compare <$> fst <$.> fst)) . loop where
  loop (TyRow n t1 t2) = first ((n, t1):) (loop t2)
  loop t               = ([], t)

-- Unfold leading μ (recursive type) binders.
unfoldMu ∷ Type tv → ([Name], Type tv)
unfoldMu (TyMu pn t) = first (pn:) (unfoldMu t)
unfoldMu t           = ([], t)

---
--- Row operations
---

-- Construct a row from a list of label/type pairs and a tail type.
foldRow ∷ [(RowLabel, Type a)] → Type a → Type a
foldRow = flip (foldr (uncurry TyRow))

-- Sort a row by its labels
sortRow ∷ Type a → Type a
sortRow = uncurry foldRow . unfoldRow

---
--- Type standardization
---

-- | @standardize@ puts a type in standard form.
--   A type is in standard form if three conditions are met:
--    
--   * All bound type variables actually appear in their scope.  That
--     is, ‘∀ α β γ. α → γ’ is not standard, but ‘∀ α γ. α → γ’ is.
--
--   * The same quantifier never nests directly inside itself.  That is,
--     ‘∀ α β. ∀ γ. C α β γ’ is not standard, but ‘∀ α β γ. C α β γ’ is.
--
--   * The bound type variables of each quantifier are listed in the
--     order that they appear in its scope.  That is,
--     ‘∀ α β γ. C α γ β’ is not standard, but ‘∀ α β γ. C α β γ’ is.
--
--   * Type variables bound by μ appear in their scope, and there are
--     never multiple, immediately nested μs.
--
--  Type standardization is necessary as a post-pass after parsing,
--  because it's difficult to parse into standard form directly.
standardizeType  ∷ Ord tv ⇒ Type tv → Type tv
standardizeType  = standardizeQuals M.empty

-- | Used in the definition of 'standardizeQuals' below.
type StdizeEnv s = [[(Int, STRef s [((Int, Int), (Name, QLit))], Bool, QLit)]]

-- | Standardize a type while cleaning up qualifiers.
standardizeQuals ∷ ∀tv. Ord tv ⇒ M.Map tv QLit → Type tv → Type tv
standardizeQuals qm t00 = runST (loop 0 [] t00) where
  loop ∷ ∀s. Int → StdizeEnv s → Type tv → ST s (Type tv)
  loop depth g t0 = case t0 of
    TyQu u _ _ → do
      rn ← newRef []
      let (qls, t) = unfoldQu u t0
          i        = length qls
          g'       = (depth + i, rn, False,) <$$> qls
      t' ← loop (depth + i) (g' ++ g) t
      nl ← readRef rn
      return $ case nl of
        [] → openTyN i (-1) [] t'
        _  → TyQu u [ n | (_,n) ← nl ] (openTyN (i - 1) (i - 1) [] t')
    TyApp tc ts          → TyApp tc <$> sequence
      [ if isQVariance v
          then doQual depth g t
          else loop depth g t
      | t ← ts
      | v ← tcArity tc ]
    TyVar v               → TyVar . fst <$> doVar depth g (const True) v
    TyRow _ _ _           → do
      let (row, ext) = unfoldRow t0
      row' ← sequence
        [ (ni,) <$> loop depth g ti
        | (ni, ti) ← row ]
      ext' ← loop depth g ext
      return (foldRow row' ext')
    TyMu pn _            → do
      rn ← newRef []
      let (pns, t) = unfoldMu t0
          i        = length pns
          g'       = (depth + i, rn, True,) <$$> replicate i [Qa]
      t' ← loop (depth + i) (g' ++ g) t
      nl ← readRef rn
      return $
        if null nl
          then openTyN i (-1) [] t'
          else TyMu pn (openTyN (i - 1) (i - 1) [] t')
  --
  doVar ∷ ∀s. Int → StdizeEnv s →
              (QLit → Bool) → TyVar tv → ST s (TyVar tv, Bool)
  doVar depth g keep v0 = case v0 of
    Bound i j n
      | rib:_                    ← drop i g
      , (olddepth, r, rec, ql):_ ← drop j rib
                          → do
        s  ← readRef r
        if rec
          then do
            case List.findIndex ((== (depth - i)) . fst . fst) s of
              Just _  → return ()
              Nothing → writeRef r (s ++ [((depth - i, 0), (n, ql))])
            return (Bound (depth - olddepth) 0 n, True)
          else do
            j' ← case List.findIndex ((== (depth - i, j)) . fst) s of
              Just j' → return j'
              Nothing → do
                when (keep ql) $
                  writeRef r (s ++ [((depth - i, j), (n, ql))])
                return (length s)
            return (Bound (depth - olddepth) j' n, keep ql)
      | otherwise   → return (v0, True)
    Free r       → return (Free r,
                              keep (M.findWithDefault maxBound r qm))
  --
  doQual ∷ ∀s. Ord tv ⇒ Int → StdizeEnv s → Type tv → ST s (Type tv)
  doQual depth g t =
    qualToType <$> case qualifier t of
      QeA     → return QeA
      QeU tvs → do
        tvbs' ← mapM (doVar depth g (== Qa)) (S.toList tvs)
        return (QeU (S.fromList (fst <$> filter snd tvbs')))

---
--- Locally-nameless operations
---

-- | @openTy k τs τ@ substitutes @τs@ for the bound type variables at
--   rib level @k@.  DeBruijn indices higher than @k@ are adjusted downward,
--   since opening a type peels off a quantifier.
openTy ∷ Int → [Type a] → Type a → Type a
openTy  = openTyN 1

-- | Generalization of 'openTy': the first argument specifies how much
--   to adjust indices that exceed @k@.
openTyN ∷ Int → Int → [Type a] → Type a → Type a
openTyN n k vs σ0 = case σ0 of
  TyQu u e σ       → TyQu u e (next σ)
  TyVar v          → openTV_N n k vs v
  TyApp name σs    → TyApp name (map this σs)
  TyRow name σ1 σ2 → TyRow name (this σ1) (this σ2)
  TyMu name σ      → TyMu name (next σ)
  where
    this = openTyN n k vs
    next = openTyN n (k + 1) vs

openTV_N ∷ Int → Int → [Type a] → TyVar a → Type a
openTV_N n k vs (Bound i j name)
  | i > k      = TyVar (Bound (i - n) j name)
  | i == k, Just σ ← listNth j vs
              = σ
  | otherwise = TyVar (Bound i j name)
openTV_N _ _ _  (Free v) = TyVar (Free v)

-- | @closeTy k αs τ@ finds the free variables @αs@ and replaces them
--   with bound variables at rib level @k@.  The position of each type
--   variable in @αs@ gives the index of each bound variable into the
--   new rib.
closeTy ∷ Eq a ⇒ Int → [a] → Type a → Type a
closeTy k vs σ0 = case σ0 of
  TyQu u e σ   → TyQu u e (next σ)
  TyVar (Bound i j n)
    | i >= k    → TyVar (Bound (i + 1) j n)
    | otherwise → TyVar (Bound i j n)
  TyVar (Free v)
    | Just j ← List.findIndex (== v) vs
                → TyVar (Bound k j Nope)
    | otherwise → TyVar (Free v)
  TyApp n σs    → TyApp n (map this σs)
  TyRow n σ1 σ2 → TyRow n (this σ1) (this σ2)
  TyMu n σ     → TyMu n (next σ)
  where
    this = closeTy k vs
    next = closeTy (k + 1) vs

-- | Build a recursive type by closing and binding the given variable
closeRec ∷ Ord tv ⇒ tv → Type tv → Type tv
closeRec α σ = standardizeType (TyMu Nope (closeTy 0 [α] σ))

-- | Add the given quantifier while binding the given list of variables
closeQuant ∷ Ord tv ⇒ Quant → [(tv, QLit)] → Type tv → Type tv
closeQuant qu αqs ρ = standardizeType (TyQu qu nqs (closeTy 0 αs ρ))
  where
    αs  = fst <$> αqs
    nqs = zip (repeat Nope) (snd <$> αqs)

-- | Is the given type locally closed to level k?  A type is locally closed
--   if none of its bound variables point to quantifiers "outside" the
--   type.
--
--   ASSUMPTION: No bound variables are lurking behind an apparent free
--   variable, because @lcTy@ doesn't attempt to dereference free
--   variables.  This should be an invariant, because it would come
--   about only as a result of a capturing substitution.
lcTy ∷ Int → Type a → Bool
lcTy  = loop where
  loop k (TyQu _ _ t)          = loop (k + 1) t
  loop k (TyVar (Bound i _ _)) = k > i
  loop _ (TyVar (Free _))      = True
  loop k (TyApp _ ts)          = all (loop k) ts
  loop k (TyRow _ t1 t2)       = loop k t1 && loop k t2
  loop k (TyMu _ t)            = loop (k + 1) t

-- | Are there no bound vars of level k?
lcTyK ∷ Int → Type tv → Bool
lcTyK  = loop where
  loop k (TyQu _ _ t)            = loop (k + 1) t
  loop k (TyVar (Bound i _ _)) = k /= i
  loop _ (TyVar (Free _))      = True
  loop k (TyApp _ ts)             = all (loop k) ts
  loop k (TyRow _ t1 t2)          = loop k t1 && loop k t2
  loop k (TyMu _ t)              = loop (k + 1) t

---
--- TyCon Varieties
---

data TyConVariety
  = AbstractType
  | DataType
  | OperatorType
  deriving (Eq, Ord)

-- | Find out the variety of a type constructor
varietyOf ∷ TyCon → TyConVariety
varietyOf tc
  | isJust (tcNext tc)          = OperatorType
  | Env.isEmpty (tcCons tc)     = AbstractType
  | otherwise                   = DataType

