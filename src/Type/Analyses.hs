module Type.Analyses (
  inferKinds,
  isMonoType,
  tyPatToType,
  tyPatKinds,
) where

import Util
import Type.Internal
import Type.TyVar

import Prelude ()
import qualified Data.Set as S

-- | Find the kinds of the rib 0 type variables in an opened type, where
--   the given 'Int' is the width of the rib.
inferKinds ∷ Ord tv ⇒ Type tv → [Kind]
inferKinds = varianceToKind <$$> loop 0 where
  loop k (TyQu _ _ σ)             = loop (k + 1) σ
  loop k (TyVar (Bound i j _))
    | i == k                      = replicate j 0 ++ 1 : repeat 0
    | otherwise                   = repeat 0
  loop _ (TyVar (Free _))         = repeat 0
  loop k (TyApp tc σs)            =
    foldr (zipWith (+)) (repeat 0)
      [ let σ' = if isQVariance var
                   then qualToType σ
                   else σ
         in (* var) <$> loop k σ'
      | var ← tcArity tc
      | σ   ← σs ]
  loop k (TyRow _ σ1 σ2)          = zipWith (+) (loop k σ1) (loop k σ2)
  loop k (TyMu _ σ)               = loop (k + 1) σ

-- | Is the given type monomorphic (quantifer free)?
isMonoType ∷ Ord tv ⇒ Type tv → Bool
isMonoType = foldType (\_ ns k → k (() <$ ns) (\_ → False))
                      (\_ _ _ → False)
                      (\_ → True)
                      (\_ → and)
                      (\_ → (&&))
                      (\_ k → k () id)

-- | Convert a type pattern to a type.
tyPatToType ∷ TyPat → Type Int
tyPatToType tp0 = evalState (loop tp0) [0..]
  where
  loop (TpVar _)      = fvTy <$> next
  loop (TpRow _)      = tyUnOp tcRowDots . fvTy <$> next
  loop (TpApp tc tps) = TyApp tc <$> mapM loop tps
  next = do
    i:rest ← get
    put rest
    return i

-- | Find out the variances, qualifier-involvement, guardedness and
--   'QLit' bounds of the type variables in a type pattern.
tyPatKinds ∷ TyPat → [(Variance, Bool, Bool, QLit)]
tyPatKinds = loop 1 True False Qa where
  loop !variance !involved !guarded !bound tp0 = case tp0 of
    TpVar _      → [(variance, involved, guarded, bound)]
    TpRow _      → [(variance, involved, guarded, bound)]
    TpApp tc tps →
      concat
        [ loop (vi * variance)
               (involved && S.member i ftv_qe)
               (guarded || gi)
               (if bound == Qu && involved
                  then Qu
                  else bi)
               tpi
        | i        ← [ 0 .. ]
        | vi       ← tcArity tc
        | gi       ← tcGuards tc
        | bi       ← tcBounds tc
        | tpi      ← tps ]
      where ftv_qe = ftvSet (tcQual tc)

