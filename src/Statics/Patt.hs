-- | Type inference for patterns
module Statics.Patt (
  tcPatt, extractPattAnnot, isPattTotal,
) where

import Util
import qualified AST
import qualified Data.Loc
import qualified Syntax.PprClass as Ppr
import Meta.Quasi
import Message.Quasi
import Type
import Statics.Constraint
import Statics.Env
import Statics.Error
import Statics.InstGen
import Statics.Subsume
import Statics.Type

import Prelude ()
import qualified Data.Map as M

-- | Type check a pattern.
tcPatt ∷ (MonadConstraint tv r m, AST.Fv stx R) ⇒
         -- | type variable environment
         Δ tv →
         -- | environment
         Γ tv →
         -- | pattern to check
         AST.Patt R →
         -- | expected type to match
         Maybe (Type tv) →
         -- | expression in scope of pattern (used to check variable
         --   occurrences)
         stx →
         m (Type tv, [Type tv])
tcPatt δ γ π0 mσ0 e0 = do
  traceN 1 (TraceIn ("inferPatt", δ, π0, mσ0))
  (σ, σs) ← evalRWST (loop π0 mσ0) 0 ()
  traceN 1 (TraceOut ("inferPatt", σ, σs))
  return (σ, σs)
  where
  -- Loop writes the types of bound parameters and reads the number
  -- of occurrences of any surrounding "as" patterns. The latter is so
  -- that if we check a pattern like “π as x”, occurrences of x count
  -- as occurrences of all the variables in π.
  loop π mσ = withLocation π $ case π of
    [pa| _ |]                     → do
      σ ← maybeFresh mσ [msg| unannotated wildcard pattern |]
      return σ
    [pa| $vid:n |]                → do
      σ ← maybeFresh mσ [msg| unannotated parameter $q:n |]
      bind n σ
      return σ
    [pa| $qcid:c $opt:mπ |]         → do
      tcexn ← γ !.! c
      (tc, mσ1) ← case tcexn of
        Left tc   → (tc,) <$> tcCons tc !.! jname c
        Right mσ1 → return (tcExn, mσ1)
      mσs ← splitCon mσ tc
      σs  ← mapM (flip maybeFresh [msg| |]) mσs
      case (mπ, mσ1) of
        (Just π1, Just σ1) → void $ loop π1 (Just (openTy 0 σs (elimEmptyF σ1)))
        (Nothing, Nothing) → return ()
        (Nothing, Just _ ) →
          typeError_ [msg|
            In pattern, unary data constructor $q:c is
            used with no argument.
          |]
        (Just _,  Nothing) →
          typeError_ [msg|
            In pattern, nullary data constructor $q:c is
            applied to an argument.
          |]
      mσ ?≤ TyApp tc σs
    [pa| ($π1, $π2) |]            → do
      [mσ1, mσ2] ← splitCon mσ tcTuple
      σ1 ← loop π1 mσ1
      σ2 ← loop π2 mσ2
      mσ ?≤ tyTuple σ1 σ2
    [pa| $str:_ |]                → tcLitPatt tcString mσ
    [pa| $int:_ |]                → tcLitPatt tcInt mσ
    [pa| $flo:_ |]                → tcLitPatt tcFloat mσ
    [pa| $char:_ |]               → tcLitPatt tcChar mσ
    [pa| $antiL:a |]              → $(AST.antifail)
    [pa| $π1 as $vid:n |]          → do
      σ  ← local (+ occOf n) (loop π1 mσ)
      bind n σ
      return σ
    [pa| `$uid:lab $opt:mπ |]     → do
      [mσRow]    ← splitCon mσ tcVariant
      (mσ1, mσ2) ← splitRow mσRow lab
      let π1 = fromMaybe [pa|+ () |] mπ
      σ1 ← loop π1 mσ1
      σ2 ← maybeFresh mσ2 [msg| |]
      mσ ?≤ TyApp tcVariant [TyRow lab σ1 σ2]
    [pa| $π1 : $annot |]           → do
      σ' ← tcType δ γ annot
      σ  ← mσ ?≤ σ'
      loop π1 (Just σ')
      return σ
    [pa| { $uid:u = $π1 | $π2 } |] → do
      [_, mσRow]        ← splitCon mσ tcRecord
      (mσ1, mσ2)        ← splitRow mσRow u
      σ1                ← loop π1 mσ1
      σ2                ← loop π2 (tyRecord tyUn <$> mσ2)
      σ2'               ← newTVTy
      tyRecord tyUn σ2' =: σ2
      mσ ?≤ tyRecord tyUn (TyRow u σ1 σ2')
    [pa| ! $_ |]                  →
      typeBug "tcPatt" "Encountered bang (!) pattern"
    [pa| $anti:a |]               → $(AST.antifail)
  --
  occOf n  = fromMaybe 0 (M.lookup (J [] n) (AST.fv e0))
  bind n τ = do
    as_occs ← ask
    τ ⊏: occOf n + as_occs
    tell [τ]
  --
  maybeFresh mσ message = case mσ of
    Nothing → newTVTy' (Ppr.ppr message)
    Just σ  → do
      σ' ← subst σ
      case σ' of
        TyVar (Free α) → reportTVs [α]
        _ → return ()
      return σ'
  --
  Nothing ?≤ σ' = return σ'
  Just σ  ?≤ σ' = do σ ≤ σ'; return σ

tcLitPatt ∷ MonadConstraint tv r m ⇒
            TyCon → Maybe (Type tv) → m (Type tv)
tcLitPatt tc mσ = do
  let σ' = tyNulOp tc
  maybe (return ()) (=: σ') mσ
  return σ'

isPattTotal ∷ Γ tv → AST.Patt R → Bool
isPattTotal γ = loop where
  loop [pa| _ |]                = True
  loop [pa| $vid:_ |]           = True
  loop [pa| $qcid:n $opt:mπ |]  =
    maybe False oneCon (γ =..= n) && maybe True loop mπ
    where
      oneCon (Left tc) = numberOfKeys (tcCons tc) == 1
      oneCon (Right _) = False
  loop [pa| ($π1, $π2) |]       = loop π1 && loop π2
  loop [pa| $lit:_ |]           = False
  loop [pa| $π as $vid:_ |]     = loop π
  loop [pa| `$uid:_ $opt:_ |]   = False
  loop [pa| $π : $_ |]          = loop π
  loop [pa| { $uid:_ = $π1 | $π2 } |]
                                = loop π1 && loop π2
  loop [pa| ! $π |]             = loop π
  loop [pa| $anti:a |]          = $(AST.antierror)

-- | Extract and instantiate the annotations in a pattern as an annotation.
extractPattAnnot ∷ MonadConstraint tv r m ⇒
                   Δ tv → Γ tv → AST.Patt R → m (Maybe (Type tv))
extractPattAnnot δ γ = loop where
  loop [pa| _ |]                = return Nothing
  loop [pa| $vid:_ |]           = return Nothing
  loop [pa| $qcid:_ $opt:_ |]   = return Nothing
  loop [pa| ($π1, $π2) |]       = do
    mσ1 ← loop π1
    mσ2 ← loop π2
    case (mσ1, mσ2) of
      (Just σ1, Just σ2)   → return (Just (tyTuple σ1 σ2))
      (Nothing, Just σ2)   → Just . flip tyTuple σ2 <$> newTVTy
      (Just σ1, Nothing)   → Just . tyTuple σ1 <$> newTVTy
      (Nothing, Nothing)   → return Nothing
  loop [pa| $lit:_ |]           = return Nothing
  loop [pa| $π as $vid:_ |]     = loop π
  loop [pa| `$uid:_ |]          = return Nothing
  loop [pa| `$uid:uid $π |]     = do
    mσ ← loop π
    case mσ of
      Just σ  → Just . TyRow uid σ <$> newTVTy
      Nothing → return Nothing
  loop [pa| $_ : $annot |]      = Just <$> tcType δ γ annot
  loop [pa| { $uid:uid = $π1 | $π2 } |]
                                = do
    mσ1 ← loop π1
    mσ2 ← loop π2
    case (mσ1, mσ2) of
      (Just σ1, Just (TyApp _ [qual, σ2])) →
        return (Just (tyRecord qual (TyRow uid σ1 σ2)))
      (Nothing, Just (TyApp _ [qual, σ2])) → do
        σ1 ← newTVTy
        return (Just (tyRecord qual (TyRow uid σ1 σ2)))
      (Just σ1, _) → do
        qual ← newTVTy' KdQual
        σ2   ← newTVTy
        return (Just (tyRecord qual (TyRow uid σ1 σ2)))
      (Nothing, _) → return Nothing
  loop [pa| ! $π |]             = loop π
  loop [pa| $anti:a |]          = $(AST.antierror)

-- | Bind a pattern to a list of types.
instance GenNewEnv (AST.Patt R) [Type tv] VarId (Type tv) where
  π -:*- σs = AST.dv π -:*- σs

{-
test_tcPatt π e =
  runConstraintIO
    constraintState0
    (subst =<< tcPatt mempty test_g0 π Nothing e)
-}
