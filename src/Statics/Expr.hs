-- | Type inference for expressions
module Statics.Expr (
  tcExpr, tcExprPatt, tcLetRecBindings,
) where

import Util
import Util.MonadRef
import qualified AST
import qualified Data.Loc
import Meta.Quasi
import Type
import Statics.Env
import Statics.Error
import Statics.Constraint
import Statics.InstGen
import Statics.Subsume
import Statics.Type
import Statics.Patt
import {-# SOURCE #-} Statics.Decl

import Prelude ()
import qualified Data.Map as M
import Data.IORef (IORef)

tcExpr ∷ MonadConstraint tv r m ⇒
         Γ tv → AST.Expr R → m (AST.Expr R, Type tv)
tcExpr γ e = withTVsOf mempty γ e $ \δ →
  infer (request Forall Exists) δ γ e Nothing

tcExprPatt ∷ MonadConstraint tv r m ⇒
             Γ tv → AST.Expr R → AST.Patt R →
             m (AST.Expr R, [Type tv])
tcExprPatt γ e π = withTVsOf mempty γ (e, π) $ \δ → do
  mσ1               ← extractPattAnnot δ γ π
  (e', σ1)          ← infer (request Forall Exists) δ γ e mσ1
  (_, σs)           ← tcPatt δ γ π (Just σ1) [ex|+! () |]
  mapM (⊏: Qu) σs
  return (e', σs)

infer  ∷ MonadConstraint tv r m ⇒
         Request tv → Δ tv → Γ tv → AST.Expr R → Maybe (Type tv) →
         m (AST.Expr R, Type tv)
infer φ0 δ γ e0 mσ0 = do
  traceN 1 (TraceIn ("infer", φ0, e0, mσ0))
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
      (bs', ns, σs)     ← tcLetRecBindingsΔ δ γ bs
      γ'                ← γ !+! ns -:*- σs
      (e2', σ')         ← infer φ δ γ' e2 mσ
      return ([ex| let rec $list:bs' in $e2' |], σ')
    [ex| let $decl:d in $e1 |]      → do
      (d', γ', _)       ← tcDecl [AST.ident "?LetModule"] γ d
      (e1', σ1)         ← infer request δ γ' e1 mσ
      σ'                ← maybeInstGen e0 φ γ σ1
      return ([ex| let $decl:d' in $e1' |], σ')
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
      σ'                ← maybeGen e0 φ γ (tyFun σ1 qe σ2)
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
      [mσRow]           ← splitCon mσ tcVariant
      (mσ1, _)          ← splitRow mσRow c
      σ2                ← newTVTy
      (me1', σ1)        ← case me1 of
        Nothing → return (Nothing, tyUnit)
        Just e1 → first Just <$> infer request δ γ e1 mσ1
      σ'                ← maybeGen e0 φ γ (TyApp tcVariant [TyRow c σ1 σ2])
      return ([ex| `$uid:c $opt:me1' |], σ')
    [ex| #$uid:c $e1 |]         → do
      [mσRow]           ← splitCon mσ tcVariant
      (_, mσ2)          ← splitRow mσRow c
      (e1', σ2)         ← infer request δ γ e1 (tyUnOp tcVariant <$> mσ2)
      σ1                ← newTVTy
      σ2'               ← newTVTy
      tyUnOp tcVariant σ2' =: σ2
      σ'                ← maybeGen e0 φ γ (tyUnOp tcVariant (TyRow c σ1 σ2'))
      return ([ex| #$uid:c $e1' |], σ')
    --
    [ex| { $list:flds | $e2 } |] → do
      (flds', e2', σ') ← inferRecordExp False e0 φ δ γ flds e2 mσ
      return ([ex| { $list:flds' | $e2' } |], σ')
    [ex| {+ $list:flds | $e2 +} |] → do
      (flds', e2', σ') ← inferRecordExp True e0 φ δ γ flds e2 mσ
      return ([ex| {+ $list:flds' | $e2' +} |], σ')
    --
    [ex| $e1 . $uid:u |] → do
      (([e1'], σ), αs)  ← collectTVs $ do
        σField            ← newTVTy
        σRow              ← newTVTy
        let σSel = tyBinOp tcRecord tyAf (TyRow u σField σRow) `tyLol` σField
        inferApp δ γ σSel [e1]
      σ'                ← maybeInstGen e0 (request φ γ αs) γ σ
      return ([ex| $e1' . $uid:u |], σ')
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

-- | Infer the type of a record expression.
inferRecordExp ∷ MonadConstraint tv r m ⇒
                 Bool → AST.Expr R →
                 Request tv → Δ tv → Γ tv →
                 [AST.Field R] → AST.Expr R → Maybe (Type tv) →
                 m ([AST.Field R], AST.Expr R, Type tv)
inferRecordExp bqual e0 φ δ γ flds e2 mσ = do
  let qual = if bqual then tyAf else tyUn
  [_, mσRow]         ← splitCon mσ tcRecord
  let eachFld mσRow' [fdQ| $uid:ui = $ei |] = do
        when bqual . tassert (AST.syntacticValue ei) $
          [msg|
            In an additive-record expression, all fields must be syntactic
            values:
            <dl>
              <dt>field:      <dd>$1
              <dt>expression: <dd>$5:ei
            </dl>
          |] (AST.uidToLid ui)
        (mσi, mσRow'')  ← splitRow mσRow' ui
        (ei', σi)       ← infer request δ γ ei mσi
        tell ([[fdQ| $uid:ui = $ei' |]], Endo (TyRow ui σi))
        return mσRow''
      eachFld _      [fdQ| $antiF:a |] = $(AST.antifail)
  (mσ2, (flds', σs)) ← runWriterT (foldM eachFld mσRow flds)
  (e2', σ2)          ← infer request δ γ e2 (tyBinOp tcRecord qual <$> mσ2)
  σRow               ← newTVTy
  σ2 <: tyBinOp tcRecord qual σRow
  σ'                 ← maybeGen e0 φ γ
                         (tyBinOp tcRecord qual (appEndo σs σRow))
  return (flds', e2', σ')

-- | Infer the type of an n-ary application expression
inferApp ∷ MonadConstraint tv r m ⇒
           Δ tv → Γ tv → Type tv → [AST.Expr R] →
           m ([AST.Expr R], Type tv)
inferApp δ γ ρ e1n = do
  traceN 2 (TraceIn ("inferApp", ρ, e1n))
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
tcMatchCases φ δ γ σ ([caQ| #$uid:n $opt:mπi → $ei |]:cas) mσ = do
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
      σ2 ≤≥ tyNulOp tcRowEnd
      return ([], β)
    else tcMatchCases φ δ γ (TyApp tcVariant [σ2]) cas mσ
  if AST.isAnnotated ei
    then σi <: β
    else σi ≤  β
  σk <: β
  return ([caQ|+ `$uid:n $opt:mπi → $ei' |]:cas', β)
-- Should we do this case automatically like this?:
{-
tcMatchCases φ δ γ σ ([caQ| `$uid:n $opt:mπi → $ei |]:cas) mσ
  | maybe True (isPattTotal γ) mπi = do
  tcMatchCases φ δ γ σ ([caQ| #$uid:n $opt:mπi → $ei |]:cas) mσ
  -}
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
                   Γ tv → [AST.Binding R] →
                   m ([AST.Binding R], [VarId], [Type tv])
tcLetRecBindings γ bs = withTVsOf mempty γ bs $ \δ → tcLetRecBindingsΔ δ γ bs

tcLetRecBindingsΔ ∷ MonadConstraint tv r m ⇒
                    Δ tv → Γ tv → [AST.Binding R] →
                    m ([AST.Binding R], [VarId], [Type tv])
tcLetRecBindingsΔ δ γ bs = do
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
  return (zipWith AST.bnBind ns es', ns, σs'')
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
      σ =: tyFun β1 qe β2
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
--- Testing

test_tcExpr ∷ AST.Expr R →
              IO (Either [AlmsError]
                         (Type (TV IORef), ConstraintState (TV IORef) IORef))
test_tcExpr e =
  runConstraintIO
    constraintState0
    (subst =<< snd <$> tcExpr test_g0 e)

