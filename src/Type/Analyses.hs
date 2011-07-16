{-# LANGUAGE
      ParallelListComp,
      UnicodeSyntax
    #-}
module Type.Analyses (
  inferKinds
) where

import Util
import Type.Internal
import Type.TyVar

import Prelude ()

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
  --
  varianceToKind var = if isQVariance var then KdQual else KdType

