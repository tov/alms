{-# LANGUAGE
      FlexibleContexts,
      ParallelListComp,
      QuasiQuotes,
      TemplateHaskell,
      TupleSections,
      UnicodeSyntax
    #-}
-- | Type inference for expressions
module Statics.Expr {-(
  tcExpr
)-} where

import Util
import Util.MonadRef
import qualified AST
import qualified Data.Loc
import AST.TypeAnnotation
import Meta.Quasi
import qualified Rank
import Type
import qualified Syntax.Ppr as Ppr
import Statics.Env
import Statics.Error
import Statics.Constraint
import Statics.InstGen
import Statics.Subsume
import Statics.Type
import Statics.Patt

import Prelude ()
import qualified Data.Map as M

tcExpr ∷ MonadConstraint tv r m ⇒
         Δ tv → Γ tv → AST.Expr R → m (AST.Expr R, Type tv)
tcExpr δ γ e = withTVsOf δ γ e $ \δ' → do
  infer (request Forall Exists) δ' γ e Nothing

infer  ∷ MonadConstraint tv r m ⇒
         Request tv → Δ tv → Γ tv → AST.Expr R → Maybe (Type tv) →
         m (AST.Expr R, Type tv)
infer φ0 δ γ e0 mσ0 = do
  traceN 1 (TraceIn ("infer", φ0, γ, e0, mσ0))
  mσ ← mapM subst mσ0
  let φ = maybe id prenexFlavors mσ φ0
  σ ← withLocation e0 $ case e0 of
    [ex| $qvid:n |]             → do
      σ' ← maybeInstGen e0 φ γ =<< γ !.! n
      return ([ex| $qvid:n |], σ')
    --
    [ex| $int:_ |]              → return (e0, tyInt)
    [ex| $char:_ |]             → return (e0, tyChar)
    [ex| $flo:_ |]              → return (e0, tyFloat)
    [ex| $str:_ |]              → return (e0, tyString)
    --
    [ex| $qcid:c $opt:me |]     → do
      -- Look up the type constructor and parameter type for the
      -- given data constructor
      tcexn ← γ !.! c
      (tc, mσ1) ← case tcexn of
        Left tc   → (tc,) <$> tcCons tc !.! jname c
        Right mσ1 → return (tcExn, mσ1)
      -- Propagation: If an annotation has been passed downward, split
      -- it into type parameters for the type constructor.  If splitting
      -- fails, then instantiate type variables with the right bounds
      -- and kinds.
      mσs ← splitCon mσ tc
      σs  ← sequence
              [ maybe (newTVTy' (qli, variancei)) return mσi
              | mσi       ← mσs
              | qli       ← tcBounds tc
              | variancei ← tcArity tc ]
      -- Check whether a parameter is expected. If it isn't, then assert
      -- that none was given.  If it is, then instantiate it using the
      -- propagated parameters, and propagate the instantated parameter
      -- type downward.  Force the result to subsume the expected type.
      me' ← case mσ1 of
        Nothing → do
          tassert (isNothing me)
            [msg| In expression, nullary data constructor $q:c is
                  applied to an argument. |]
          return Nothing
        Just σ1E → do
          let σ1 = openTy 0 σs (elimEmptyF σ1E)
          case me of
            Just e  → do
              (e', σ1') ← infer request δ γ e (Just σ1)
              σ1' ≤ σ1
              return (Just e')
            Nothing → do
              typeError_
                [msg| In expression, unary data constructor $q:c is used
                      with no argument. |]
              return Nothing
      σ'  ← maybeGen e0 φ γ (TyApp tc σs)
      return ([ex| $qcid:c $opt:me' |], σ')
    --
    [ex| let $π = $e1 in $e2 |] → do
      mσ1               ← extractPattAnnot δ γ π
      ((e1', σs), αs)   ← collectTVs $ do
        (e1', σ1)         ← infer (request Forall Exists) δ γ e1 mσ1
        (_, σs)           ← tcPatt δ γ π (Just σ1) e2
        return (e1', σs)
      γ'                ← γ !+! π -:*- σs
      (e2', σ')         ← infer (request φ γ αs) δ γ' e2 mσ
      return ([ex| let $π = $e1' in $e2' |], σ')
    [ex| match $e1 with $list:cas |] → do
      ((e1', σ1), αs)   ← collectTVs (infer request δ γ e1 Nothing)
      (cas', σ')        ← tcMatchCases (request φ γ αs) δ γ σ1 cas mσ
      return ([ex| match $e1' with $list:cas' |], σ')
    [ex| let rec $list:bs in $e2 |] → do
      (bs', γ')         ← tcLetRecBindings δ γ bs
      (e2', σ')         ← infer φ δ γ' e2 mσ
      return ([ex| let rec $list:bs' in $e2' |], σ')
    [ex| let $decl:_ in $_ |]       → do
      typeBug "tcExpr" "TODO: let decl (e.g. let module) unimplemented" --XXX
    --
    [ex| ($e1, $e2) |]          → do
      [mσ1, mσ2]        ← splitCon mσ tcTuple
      (e1', σ1)         ← infer request δ γ e1 mσ1
      (e2', σ2)         ← infer request δ γ e2 mσ2
      σ'                ← maybeGen e0 φ γ (tyTuple σ1 σ2)
      return ([ex| ($e1', $e2') |], σ')
    --
    [ex| λ $π → $e |]           → do
      [mσ1, _, mσ2]     ← splitCon mσ tcFun
      ((σ1, σs), αs)    ← collectTVs (tcPatt δ γ π mσ1 e)
      αs'               ← filterM (isMonoType <$$> subst . fst)
                                  ((fvTy &&& tvDescr) <$> αs)
      γ'                ← γ !+! π -:*- σs
      (e', σ2)          ← infer (request Exists γ αs) δ γ' e mσ2
      for_ αs' $ \(α, descr) → do
        τ ← subst α
        tassert (isMonoType τ)
          [msg| Use $descr polymorphically |]
      let qe            = arrowQualifier γ e0
      σ'                ← maybeGen e0 φ γ (tyFun qe σ1 σ2)
      return ([ex| λ $π → $e' |], σ')
    --
    [ex| $_ $_ |]               → do
      let (es, e1)      = AST.unfoldExApp e0
      ((e0', σ), αs)    ← collectTVs $ do
        (e1', σ1)         ← infer request δ γ e1 Nothing
        (es', σ)          ← inferApp δ γ σ1 es
        return (foldl' AST.exApp e1' es', σ)
      σ'                ← maybeInstGen e0 (request φ γ αs) γ σ
      return (e0', σ')
    --
    [ex| `$uid:c $opt:me1 |]    → do
      [mσ0]             ← splitCon mσ tcVariant
      (mσ1, _)          ← splitRow mσ0 c
      σ2                ← newTVTy
      (me1', σ1)        ← case me1 of
        Nothing → return (Nothing, tyUnit)
        Just e1 → first Just <$> infer request δ γ e1 mσ1
      σ'                ← maybeGen e0 φ γ (TyApp tcVariant [TyRow c σ1 σ2])
      return ([ex| `$uid:c $opt:me1' |], σ')
    [ex| #$uid:c $e1 |]         → do
      [mσ0]             ← splitCon mσ tcVariant
      (_, mσ2)          ← splitRow mσ0 c
      (e1', σ2)         ← infer request δ γ e1 (tyUnOp tcVariant <$> mσ2)
      σ1                ← newTVTy
      σ2'               ← newTVTy
      tyUnOp tcVariant σ2' =: σ2
      σ'                ← maybeGen e0 φ γ (tyUnOp tcVariant (TyRow c σ1 σ2'))
      return ([ex| #$uid:c $e1' |], σ')
    --
    [ex| $e : $annot |]         → do
      σ                 ← tcType δ γ annot
      (e', αs)          ← collectTVs . withPinnedTVs σ $ do
        (e', σ')          ← infer request δ γ e (Just σ)
        σ' ≤ σ
        return e'
      σ'                ← maybeGen e0 (request φ γ αs) γ σ
      return ([ex| $e' : $annot |], σ')
    [ex| $_ :> $_ |]      → do
      typeBug "tcExpr" "TODO: cast (:>) unimplemented" --XXX
    --
    [ex| $anti:a |]             → $(AST.antifail)
    [ex| $antiL:a |]            → $(AST.antifail)
    --
  traceN 1 (TraceOut ("infer", σ))
  return σ

-- | Infer the type of an n-ary application expression
inferApp ∷ MonadConstraint tv r m ⇒
           Δ tv → Γ tv → Type tv → [AST.Expr R] →
           m ([AST.Expr R], Type tv)
inferApp δ γ ρ e1n = do
  traceN 2 (TraceIn ("inferApp", γ, ρ, e1n))
  (σ1m, σ)              ← funmatchN (length e1n) ρ
  refs                  ← replicateM (length σ1m) (newRef Nothing)
  withPinnedTVs ρ $
    subsumeN [ (σi, do
                      (ei', σi') ← infer (request Exists) δ γ ei (Just σi)
                      writeRef refi (Just ei')
                      traceN 2 ("subsumeI", i, ei, σi', σi)
                      if AST.isAnnotated ei
                        then σi' <: σi
                        else σi' ≤  σi)
             | i    ← [ 0 ∷ Int .. ]
             | refi ← refs
             | σi   ← σ1m
             | ei   ← e1n ]
  e1m'                  ← for refs $
    readRef >=> maybe (typeBug "inferApp" "ref contained Nothing") return
  if length σ1m < length e1n
    then do
      ρ' ← instantiate σ
      first (e1m' ++) <$> inferApp δ γ ρ' (drop (length σ1m) e1n)
    else do
      traceN 2 (TraceOut ("inferApp", σ))
      return (e1m', σ)

-- | Type check a list of pattern match alternatives
tcMatchCases ∷ MonadConstraint tv r m ⇒
               Request tv → Δ tv → Γ tv →
               Type tv → [AST.CaseAlt R] → Maybe (Type tv) →
               m ([AST.CaseAlt R], Type tv)
tcMatchCases _ _ _ _ [] _ = ([],) <$> newTVTy
tcMatchCases φ δ γ σ ([caQ| `$uid:n $opt:mπi → $ei |]:cas) mσ
  | maybe True (isPattTotal γ) mπi = do
  traceN 3 ("tcMatchCases", φ, σ, "variant", n, mπi, ei)
  β                     ← newTVTy
  σ1                    ← newTVTy
  σ2                    ← newTVTy
  σ ≤≥ TyApp tcVariant [TyRow n σ1 σ2]
  (γ', αs)              ← case mπi of
    Just πi → do
      ((_, σs), αs)         ← collectTVs (tcPatt δ γ πi (Just σ1) ei)
      γ'                    ← γ !+! πi -:*- σs
      return (γ', αs)
    Nothing → do
      σ1 =: tyUnit
      return (γ, [])
  (ei', σi)             ← infer (request φ γ αs) δ γ' ei mσ
  (cas', σk)            ← if null cas
    then do
      σ2 ≤≥ tyNulOp tcEnd
      return ([], β)
    else tcMatchCases φ δ γ (TyApp tcVariant [σ2]) cas mσ
  if AST.isAnnotated ei
    then σi <: β
    else σi ≤  β
  σk <: β
  return ([caQ|+ `$uid:n $opt:mπi → $ei' |]:cas', β)
tcMatchCases φ δ γ σ ([caQ| $πi → $ei |]:cas) mσ = do
  traceN 3 ("tcMatchCases", φ, σ, πi, ei)
  β                     ← newTVTy
  ((_, σs), αs)         ← collectTVs (tcPatt δ γ πi (Just σ) ei)
  γ'                    ← γ !+! πi -:*- σs
  (ei', σi)             ← infer (request φ γ αs) δ γ' ei mσ
  (cas', σk)            ← tcMatchCases φ δ γ σ cas mσ
  if AST.isAnnotated ei
    then σi <: β
    else σi ≤  β
  σk <: β
  return ([caQ|+ $πi → $ei' |]:cas', β)
tcMatchCases _ _ _ _ ([caQ| $antiC:a |]:_) _ = $(AST.antifail)

tcLetRecBindings ∷ MonadConstraint tv r m ⇒
                   Δ tv → Γ tv → [AST.Binding R] →
                   m ([AST.Binding R], Γ tv)
tcLetRecBindings δ γ bs = do
  (ns, es)          ← unzip <$> mapM unBinding bs
  let mannots       = AST.getExprAnnot <$> es
  σs                ← mapM (maybe newTVTy (tcType δ γ)) mannots
  γ'                ← γ !+! ns -:*- σs
  (es', σs')        ← unzip <$> sequence
    [ do
        tassert (AST.syntacticValue ei)
          [msg|
            In let rec, binding for $q:ni is not a syntactic value.
          |]
        σi ⊏: Qu
        infer request δ γ' ei (σi <$ mannoti)
    | ni        ← ns
    | ei        ← es
    | mannoti   ← mannots
    | σi        ← σs ]
  zipWithM (<:) σs' σs
  σs''              ← generalizeList True (rankΓ γ) σs'
  γ'                ← γ !+! ns -:*- σs''
  return (zipWith AST.bnBind ns es', γ')
  where
    unBinding [bnQ| $vid:x = $e |] = return (x, e)
    unBinding [bnQ| $antiB:a |]    = $(AST.antifail)

---
--- MISCELLANEOUS HELPERS
---

-- | Determine which quantifiers may appear at the beginning of
--   a type scheme, given a list of quantifiers that may be presumed
--   to belong to an unsubstituted variable.
prenexFlavors ∷ Type tv → Request tv' → Request tv'
prenexFlavors σ φ =
  case σ of
    TyQu Exists _ (TyQu Forall _ _) → φ { rqEx = True, rqAll = True }
    TyQu Exists _ (TyVar _)         → φ { rqEx = True }
    TyQu Exists _ _                 → φ { rqEx = True, rqAll = False }
    TyQu Forall _ _                 → φ { rqEx = False, rqAll = True }
    TyVar _                         → φ
    _                               → φ { rqEx = False, rqAll = False }

-- | To compute the qualifier expression for a function type.
arrowQualifier ∷ Ord tv ⇒ Γ tv → AST.Expr R → QExpV tv
arrowQualifier γ e =
  bigJoin [ qualifier (γ =..= n)
          | n      ← M.keys (AST.fv e) ]

-- | Extend the environment and update the ranks of the free type
--   variables of the added types.
(!+!) ∷ MonadSubst tv r m ⇒ Γ tv → Γv tv → m (Γ tv)
γ !+! γv = do
  lowerRank (Rank.inc (rankΓ γ)) =<< subst (range γv)
  return (bumpΓ γ =+= γv)
infixl 2 !+!

---
--- SUBSUMPTION OPERATIONS
---

-- | Given a function arity and a type, extracts a list of argument
--   types and a result type of at most the given arity.
funmatchN ∷ MonadConstraint tv r m ⇒
            Int → Type tv → m ([Type tv], Type tv)
funmatchN n0 σ0 = loop n0 =<< subst σ0
  where
  loop 0 σ = return ([], σ)
  loop n σ = case σ of
    TyApp tc [σ1, _, σ']        | tc == tcFun
      → first (σ1:) <$> loop (n - 1) σ'
    TyApp _ _                   | Next σ' ← headReduceType σ
      → loop n σ'
    TyVar (Free α)              | tvFlavorIs Universal α
      → do
      β1 ← newTVTy
      qe ← qvarexp . Free <$> newTV' KdQual
      β2 ← newTVTy
      σ =: tyFun qe β1 β2
      return ([β1], β2)
    TyMu _ σ1
      → loop n (openTy 0 [σ] σ1)
    _ → do
      tErrExp_
        [msg| In application expression, operator is not a function: |]
        [msg| $σ |]
        [msg| a function type |]
      βs ← replicateM n newTVTy
      β2 ← newTVTy
      return (βs, β2)

---
--- INSTANTIATING ANNOTATION TYPE VARIABLES
---

-- | Given the environments, a piece of syntax, and a continuation,
--   call the continuation with the type variable environment extended
--   with fresh type variables for any annotation type variables in the
--   piece of syntax.
withTVsOf ∷ (MonadConstraint tv r m, HasAnnotations a R) ⇒
            Δ tv → Γ tv → a → (Δ tv → m b) → m b
withTVsOf δ γ stx kont = do
  let (αs, κs) = unzip (tvsWithKinds γ stx)
  αs' ← mapM newTV' κs
  kont (δ =+= αs =:*= αs')

-- | Given an expression, get its type variables with their kinds
tvsWithKinds ∷ HasAnnotations a R ⇒
               Γ tv → a → [(AST.TyVar R, Kind)]
tvsWithKinds γ = M.toList . (unKindLat <$$> annotFtvMap var con) where
  var _      = KindLat KdType
  con n ix = case γ =..= n of
    Just tc
      | variance:_ ← drop ix (tcArity tc)
      , isQVariance variance
      → \_ → KindLat KdQual
    _ → id

newtype KindLat = KindLat { unKindLat ∷ Kind }

instance Monoid KindLat where
  mempty = KindLat KdQual
  mappend (KindLat KdQual) (KindLat KdQual) = KindLat KdQual
  mappend _                _                = KindLat KdType

---
--- Testing

test_tcExpr e =
  runConstraintIO
    constraintState0
    (subst =<< snd <$> tcExpr mempty test_g0 e)

