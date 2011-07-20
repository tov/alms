{-# LANGUAGE
      FlexibleInstances,
      GeneralizedNewtypeDeriving,
      MultiParamTypeClasses,
      QuasiQuotes,
      TypeSynonymInstances,
      UnicodeSyntax
    #-}
module Statics.Sealing (
  sealWith
) where

import Util
import qualified AST
import Syntax.PprClass (MAYBE(..))
import Type
import Statics.Constraint
import Statics.Env as Env
import Statics.Error
import Statics.Subsume

import Prelude ()
import qualified Data.Map as M

-- | Perform generative signature matching
sealWith ∷ MonadConstraint tv r m ⇒
           [ModId] → Signature tv → Signature tv → m (Signature tv)
sealWith μ sig0 sig1 = do
  let sig1'     = renameSig (makeNameMap sig0) μ sig1
      γ0        = sigToEnv sig0
  tcsubst       ← matchSigTycons γ0 sig1'
  subsumeSig γ0 (applyTCSInTyCon tcsubst sig1')
  let tcs       = getGenTycons sig1'
  tcs'          ← for tcs $ \tc → do
    ix ← tvUniqueID <$> newTV
    return tc { tcId = ix }
  return (substTyCons tcs tcs' sig1')

-- | For mapping renamed names (from structures) into unrenamed names
--   (in signatures)
data NameMap
  = NameMap {
      nmVar     ∷ Env VarId      VarId,
      nmCon     ∷ Env ConId      ConId,
      nmTyp     ∷ Env TypId      TypId,
      nmMod     ∷ Env ModId      (ModId, NameMap),
      nmSig     ∷ Env SigId      SigId
  }

instance Monoid NameMap where
  mempty = NameMap empty empty empty empty empty
  mappend (NameMap a1 a2 a3 a4 a5) (NameMap b1 b2 b3 b4 b5) =
    NameMap (a1 =+= b1) (a2 =+= b2) (a3 =+= b3) (a4 =+= b4) (a5 =+= b5)

instance GenEmpty NameMap where
  genEmpty = mempty
instance GenExtend NameMap NameMap where
  (=+=) = mappend
instance GenLookup NameMap VarId VarId where
  e =..= k = nmVar e =..= k
instance GenLookup NameMap ConId ConId where
  e =..= k = nmCon e =..= k
instance GenLookup NameMap TypId TypId where
  e =..= k = nmTyp e =..= k
instance GenLookup NameMap ModId (ModId, NameMap) where
  e =..= k = nmMod e =..= k
instance GenLookup NameMap SigId SigId where
  e =..= k = nmSig e =..= k

-- | Given a signature, construct a 'NameMap' mapping trivially-renamed
--   versions of its names to the actual renamed version.
makeNameMap ∷ Signature tv → NameMap
makeNameMap = foldMap eachItem where
  eachItem (SgVal n _)   = mempty { nmVar = unTag n =:= n }
  eachItem (SgTyp n tc)  =
    mempty {
      nmTyp = unTag n =:= n,
      nmCon = Env.fromList ((unTag &&& id) <$> Env.domain (tcCons tc))
    }
  eachItem (SgExn n _)   = mempty { nmCon = unTag n =:= n }
  eachItem (SgSig n _)   = mempty { nmSig = unTag n =:= n }
  eachItem (SgMod n sig) = mempty { nmMod = unTag n =:= (n, makeNameMap sig) }
  --
  unTag ∷ AST.Id a ⇒ a R → a R
  unTag = AST.renId bogus

-- | Make the names in a signature match the names from the module it's
--   being applied to.
renameSig ∷ NameMap → [ModId] → Signature tv → Signature tv
renameSig nm μ = map eachItem where
  eachItem (SgVal n σ)   = SgVal (nm !..! n) σ
  eachItem (SgTyp n tc)  = SgTyp (nm !..! n) tc'
    where
    tc' = tc {
      tcName = J (reverse μ) (jname (tcName tc)),
      tcCons = Env.fromList (first (nm !..!) <$> Env.toList (tcCons tc))
    }
  eachItem (SgExn n mσ)  = SgExn (nm !..! n) mσ
  eachItem (SgMod n sig) = SgMod n' sig'
    where
      (n', nm') = nm !..! n
      sig'      = renameSig nm' (n':μ) sig
  eachItem (SgSig n sig) = SgSig (nm !..! n) sig

-- | Given a signature, find the tycon substitutions necessary to
--   unify it with the module in the environment.
matchSigTycons ∷ MonadConstraint tv r m ⇒
                 Γ tv → Signature tv → m TyConSubst
matchSigTycons γ = execWriterT . eachSig [] where
  eachSig μ = mapM_ (eachItem μ)
  eachItem μ sigitem = case sigitem of
    SgVal _ _   → return ()
    SgTyp n tc  → do
      tc' ← γ !.! J (reverse μ) n
      tell (makeTyConSubst [tc] [tc'])
    SgExn _ _   → return ()
    SgMod n sig → eachSig (n:μ) sig
    SgSig _ _   → return ()

-- | Check whether the given signature subsumes the signature
--   implicit in the environment.
subsumeSig ∷ MonadConstraint tv r m ⇒
             Γ tv → Signature tv → m ()
subsumeSig γ = eachSig where
  eachSig      = mapM_ eachItem
  eachItem sg0 = case sg0 of
    SgVal n σ   → do
      σ'        ← γ !.! n
      σ' ≤ σ
        `addErrorContext`
          [msg| In signature matching, type mismatch for value binding $q:n. |]
    SgTyp n tc  → do
      tc'       ← γ !.! n
      case varietyOf tc of
        OperatorType → matchTyCons tc' tc
        DataType     → matchTyCons tc' tc
        AbstractType → do
          let sigAss assertion thing getter =
                tAssExp assertion
                  ([msg| In signature matching, cannot match the
                         definition for type $q:1 because the
                         $words:thing does not match: |] (tcName tc))
                  (showMsg (getter tc'))
                  (showMsg (getter tc))
          sigAss (length (tcArity tc') == length (tcArity tc))
            "number of type parameters" (length . tcArity)
          sigAss (all2 (⊑) (tcArity tc') (tcArity tc))
            "variance" tcArity
          sigAss (all2 (⊑) (tcBounds tc') (tcBounds tc))
            "parameter bounds" tcBounds
          sigAss (tcQual tc' ⊑ tcQual tc)
            "qualifier" tcQual
    SgExn n mσ  → do
      emσ'      ← γ !.! n
      case emσ' of
        Left _    → typeBug "subsumeSig" "Datacon where exn expected"
        Right mσ' → tAssExp (mσ == mσ')
          [msg| In signature matching, parameter type of exception $q:n
                does not match |]
          (maybe [msg| no parameter |] pprMsg mσ')
          (maybe [msg| no parameter |] pprMsg mσ)
    SgMod n sig → do
      (_, γ')   ← γ !.! n
      subsumeSig γ' sig
    SgSig n sig → do
      (sig', _) ← γ !.! n
      matchSigs sig' sig

-- | Check that two signatures match EXACTLY.
--   First signature is what we have, and second is what we want.
matchSigs ∷ (Ord tv, MonadAlmsError m) ⇒
            Signature tv → Signature tv → m ()
matchSigs = loop where
  loop [] []                = return ()
  loop (SgVal n1 σ1 : sgs1)     (SgVal n2 σ2 : sgs2)
    | n1 == n2, σ1 == σ2    = loop sgs1 sgs2
  loop (SgTyp n1 tc1 : sgs1)    (SgTyp n2 tc2 : sgs2)
    | n1 == n2              = do
      matchTyCons tc1 tc2
      loop (substTyCon tc1 tc2 sgs1) sgs2
  loop (SgExn n1 mσ1 : sgs1)    (SgExn n2 mσ2 : sgs2)
    | n1 == n2, mσ1 == mσ2  = loop sgs1 sgs2
  loop (SgMod n1 sig1 : sgs1)   (SgMod n2 sig2 : sgs2)
    | n1 == n2              = do
      matchSigs sig1 sig2
      loop sgs1 sgs2
  loop (SgSig n1 sig1 : sgs1)   (SgSig n2 sig2 : sgs2)
    | n1 == n2              = do
      matchSigs sig1 sig2
      loop sgs1 sgs2
  loop [] (sg : _)          = do
    (n, what) ← whatIs sg
    typeError [msg|
      In exact signature matching, missing expected $what $qmsg:n.
    |]
  loop (sg : _) []          = do
    (n, what) ← whatIs sg
    typeError [msg|
      In exact signature matching, found unexpected $what $qmsg:n.
    |]
  loop (sg1 : _) (sg2 : _)  = do
    (n1, what1) ← whatIs sg1
    (n2, what2) ← whatIs sg2
    typeError [msg|
      In exact signature matching (for signatures as entries in
      signatures being matched), got signature items didn’t match:
      <dl>
        <dt>actual:   <dd>$what1 $qmsg:n1
        <dt>expected: <dd>$what2 $qmsg:n2
      </dl>
    |]
  --
  whatIs (SgVal n _) = return (pprMsg n, "value")
  whatIs (SgTyp n _) = return (pprMsg n, "type")
  whatIs (SgExn n _) = return (pprMsg n, "exception")
  whatIs (SgMod n _) = return (pprMsg n, "module")
  whatIs (SgSig n _) = return (pprMsg n, "module type")

-- | Get a list of all the tycons that need a new index allocated
--   because they're generative.
getGenTycons ∷ Signature tv → [TyCon]
getGenTycons = execWriter . eachSig where
  eachSig       = mapM_ eachItem
  eachItem sg0  = case sg0 of
    SgVal _ _   → return ()
    SgTyp _ tc  → unless (varietyOf tc == OperatorType) (tell [tc])
    SgExn _ _   → return ()
    SgMod _ sig → eachSig sig
    SgSig _ _   → return ()

-- | Check that two type constructors match exactly.
matchTyCons ∷ MonadAlmsError m ⇒ TyCon → TyCon → m ()
matchTyCons tc1 tc2 = case (varietyOf tc1, varietyOf tc2) of
  (AbstractType, AbstractType) → do
    tcArity tc1  ==! tcArity tc2        $ "arity or variance"
    tcBounds tc1 ==! tcBounds tc2       $ "parameter bound"
    tcGuards tc1 ==! tcGuards tc2       $ "guarded parameters"
    tcQual tc1   ==! tcQual tc2         $ "qualifier"
  (DataType, DataType) → do
    tcArity tc1  ==! tcArity tc2        $ "number of parameters"
    let rhs1 = tcCons tc1
        rhs2 = tcCons tc2
    forM_ (Env.toList rhs1) $ \(k, mσ1) → do
      mσ2 ← rhs2 !.! k
      MAYBE mσ1  ==! MAYBE mσ2          $ "parameter of constructor " ++ show k
  (OperatorType, _)            | tyconExtEq tc1 tc2 → return ()
  (_,            OperatorType) | tyconExtEq tc1 tc2 → return ()
  (OperatorType, OperatorType) → do
    let next1 = fromMaybe [] (tcNext tc1)
        next2 = fromMaybe [] (tcNext tc2)
        ncs1  = length next1
        ncs2  = length next1
    ncs1         ==! ncs2               $ "number of clauses"
    forM_ (zip3 next1 next2 [1 ∷ Int .. ]) $
      \((tp1, σ1), (tp2, σ2), ix) → do
        length tp1 ==! length tp2 $
          if ncs1 == 1
            then "number of type parameters"
            else "number of parameters else in clause " ++ show ix
        zipWithM_ matchTyPats tp1 tp2
        σ1         ==! σ2               $
          if ncs1 == 1
            then "type synonym right-hand sides"
            else "type operator right-hand sides in clause " ++ show ix
  (v1, v2) → v1 ==! v2 $ "kind of definition"
  where
    (a1 ==! a2) what =
      tAssExp (a1 == a2)
        [msg| In signature match, cannot match definition for type
              $q:tc1 because the $words:what does not match: |]
        (pprMsg a1)
        (pprMsg a2)

-- | Extensional equality for type constructors.
--   This is probably too weak.
tyconExtEq ∷ TyCon → TyCon → Bool
tyconExtEq tc1 tc2 | tcBounds tc1 == tcBounds tc2 =
  let tvs = fvTy <$> [ 1 .. length (tcArity tc1) ]
   in TyApp tc1 tvs == TyApp tc2 tvs
tyconExtEq _   _   = False

-- | To check that two type patterns match, and return the pairs of
--   type variables that line up and thus need renaming.
matchTyPats ∷ MonadAlmsError m ⇒ TyPat → TyPat → m ()
matchTyPats (TpVar _) (TpVar _)
  = return ()
matchTyPats (TpRow _) (TpRow _)
  = return ()
matchTyPats (TpApp tc1 tvs1) (TpApp tc2 tvs2)
  | tc1 == tc2
  = zipWithM_ matchTyPats tvs1 tvs2
matchTyPats tp1 tp2
  = tErrExp
      [msg| In signature matching, cannot match type patterns: |]
      (pprMsg tp1)
      (pprMsg tp2)

---
--- TYPE CONSTRUCTOR SUBSTITUTION
---

-- | A substitution mapping type constructors to other type
--   constructors
type TyConSubst = M.Map Int TyCon

-- | Construct a tycon substitution from a list of tycons and a list
--   to map them to.
makeTyConSubst ∷ [TyCon] → [TyCon] → TyConSubst
makeTyConSubst tcs tcs' = M.fromList (zip (tcId <$> tcs) tcs')

class SubstTyCon a where
  applyTCS, applyTCSInTyCon ∷ TyConSubst → a → a
  applyTCSInTyCon    = applyTCS

instance SubstTyCon a ⇒ SubstTyCon (Maybe a) where
  applyTCS        = fmap . applyTCS
  applyTCSInTyCon = fmap . applyTCSInTyCon

instance SubstTyCon a ⇒ SubstTyCon [a] where
  applyTCS        = fmap . applyTCS
  applyTCSInTyCon = fmap . applyTCSInTyCon

instance SubstTyCon v ⇒ SubstTyCon (Env k v) where
  applyTCS        = fmap . applyTCS
  applyTCSInTyCon = fmap . applyTCSInTyCon

instance (SubstTyCon a, SubstTyCon b) ⇒ SubstTyCon (a, b) where
  applyTCS s        = applyTCS s *** applyTCS s
  applyTCSInTyCon s = applyTCSInTyCon s *** applyTCSInTyCon s

instance (SubstTyCon a, SubstTyCon b, SubstTyCon c) ⇒
         SubstTyCon (a, b, c) where
  applyTCS s (a, b, c) = (applyTCS s a, applyTCS s b, applyTCS s c)
  applyTCSInTyCon s (a, b, c) =
    (applyTCSInTyCon s a, applyTCSInTyCon s b, applyTCSInTyCon s c)

instance (SubstTyCon a, SubstTyCon b) ⇒ SubstTyCon (Either a b) where
  applyTCS s        = applyTCS s +++ applyTCS s
  applyTCSInTyCon s = applyTCSInTyCon s +++ applyTCSInTyCon s

instance SubstTyCon TyCon where
  applyTCS s tc
    | Just tc' ← M.lookup (tcId tc) s
      = applyTCSInTyCon s tc'
    | otherwise
      = applyTCSInTyCon s tc
  applyTCSInTyCon s tc
    = tc {
          tcNext = applyTCS s (tcNext tc),
          tcCons = applyTCS s (tcCons tc)
        }

instance SubstTyCon TyPat where
  applyTCS s tp0 = case tp0 of
    TpVar _     → tp0
    TpRow _     → tp0
    TpApp tc σs → TpApp (applyTCS s tc) (applyTCS s σs)

instance SubstTyCon (Type tv) where
  applyTCS s σ0 = case σ0 of
    TyVar _         → σ0
    TyQu qu αs σ    → TyQu qu αs (applyTCS s σ)
    TyMu α σ        → TyMu α (applyTCS s σ)
    TyRow lab σ1 σ2 → TyRow lab (applyTCS s σ1)
                                (applyTCS s σ2)
    TyApp tc σs     → TyApp (applyTCS s tc)
                            (applyTCS s σs)

instance SubstTyCon (SigItem tv) where
  applyTCS s sg0 = case sg0 of
    SgVal n σ   → SgVal n (applyTCS s σ)
    SgTyp n tc  → SgTyp n (applyTCS s tc)
    SgExn n mσ  → SgExn n (applyTCS s mσ)
    SgMod n sig → SgMod n (applyTCS s sig)
    SgSig n sig → SgSig n (applyTCS s sig)
  applyTCSInTyCon s sg0 = case sg0 of
    SgVal n σ   → SgVal n (applyTCS s σ)
    SgTyp n tc  → SgTyp n (applyTCSInTyCon s tc)
    SgExn n mσ  → SgExn n (applyTCS s mσ)
    SgMod n sig → SgMod n (applyTCSInTyCon s sig)
    SgSig n sig → SgSig n (applyTCS s sig)

-- Give a list of tycons to replace and a list of tycons to replace them
-- with, replaces them all recursively, including knot-tying
substTyCons ∷ SubstTyCon a ⇒ [TyCon] → [TyCon] → a → a
substTyCons tcs tcs' = applyTCS (makeTyConSubst tcs tcs')

-- | Replace all occurrences of the first tycon with the second
substTyCon ∷ SubstTyCon a ⇒ TyCon → TyCon → a → a
substTyCon tc tc' = substTyCons [tc] [tc']
