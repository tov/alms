{-# LANGUAGE
      ParallelListComp,
      UnicodeSyntax
    #-}
module Type.Analyses (
  inferKinds,
  isMonoType,
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

-- | Is the given type monomorphic (quantifer free)?
isMonoType ∷ Ord tv ⇒ Type tv → Bool
isMonoType = foldType (\_ ns k → k (() <$ ns) (\_ → False))
                      (\_ _ _ → False)
                      (\_ → True)
                      (\_ → and)
                      (\_ → (&&))
                      (\_ k → k () id)

