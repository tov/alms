{-# LANGUAGE
      UnicodeSyntax
    #-}
-- | Facilities for proper handling of equirecursive types
module Type.Recursive (
  -- * Equirecursive type standardization
  standardizeMus,

  -- * Non-equirecursive comparison
  NoRec(..),
) where

import Util
import Util.MonadRef
import Type.Internal

import Prelude ()
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.ST (runST)

-- | Put all recursion in standard form.
--   PRECONDITION: The type is in 'standardize' standard form and all
--   type variables are substituted
standardizeMus ∷ Ord tv ⇒ Type tv → Type tv
standardizeMus σ00 = runST $ do
  counter ← newRef (0 ∷ Int)
  let loop g0 σ0 = do
        case M.lookup σ0 g0 of
          Just (i, used') → do
            writeRef used' True
            return (fvTy i)
          Nothing → do
            i    ← gensym
            used ← newRef False
            let g = M.insert σ0 (i, used) g0
            σ0'  ← case σ0 of
              TyQu qu qls σ → do
                is ← mapM (const gensym) qls
                σ' ← loop g (openTy 0 (map fvTy is) σ)
                return (TyQu qu qls (closeTy 0 is σ'))
              TyApp tc σs   → TyApp tc `liftM` mapM (loop g) σs
              TyVar _       → return σ0
              TyRow n σ1 σ2 → TyRow n `liftM` loop g σ1 `ap` loop g σ2
              TyMu _ σ1     → loop g0 (openTy 0 [σ0] σ1)
            wasUsed ← readRef used
            return $ if wasUsed
              then TyMu Nope (closeTy 0 [i] σ0')
              else σ0'
      gensym  = do
        i ← readRef counter
        writeRef counter (i + 1)
        return (Right i)
      clean = either id (error "BUG! (standardizeMus)")
  σ00' ← loop M.empty (Left <$> σ00)
  return (clean <$> σ00')


-- | Newtype for defining 'Eq' and 'Ord' on types treating 'TyMu' as a
-- normal type constructor without unfolding.  We build the correct
-- equirecursive operations on top of this.
newtype NoRec tv = NoRec (Type tv)

instance Ord tv ⇒ Eq (Type tv) where
  σ1 == σ2 = compare σ1 σ2 == EQ

instance Ord tv ⇒ Ord (Type tv) where
  compare σ10 σ20 = evalState (loop σ10 σ20) S.empty where
    compareM a b = return (compare a b)
    loop σ1 σ2 = do
      seen ← get
      if (S.member (NoRec σ1, NoRec σ2) seen ||
          S.member (NoRec σ2, NoRec σ1) seen)
        then return EQ
        else do
          put (S.insert (NoRec σ1, NoRec σ2) seen)
          case (σ1, σ2) of
            (TyMu _ σ1', _)
              → loop (openTy 0 [σ1] σ1') σ2
            (_, TyMu _ σ2')
              → loop σ1 (openTy 0 [σ2] σ2')
            (TyVar v1, TyVar v2)
              → compareM v1 v2
            (TyQu qu1 qls1 σ1', TyQu qu2 qls2 σ2')
              → compareM qu1 qu2        `thenCmpM`
                compareM qls1 qls2      `thenCmpM`
                loop σ1' σ2'
            (TyRow n1 σ1f σ1r, TyRow n2 σ2f σ2r)
              → compareM n1 n2          `thenCmpM`
                loop σ1f σ2f            `thenCmpM`
                loop σ1r σ2r
            (TyApp n1 σs1, TyApp n2 σs2)
              → compareM n1 n2          `thenCmpM`
                compareM (length σs1) (length σs2)
                                        `thenCmpM`
                foldl' thenCmpM (return EQ) (zipWith loop σs1 σs2)
            (TyVar _, _)
              → return LT
            (_, TyVar _)
              → return GT
            (TyQu _ _ _, _)
              → return LT
            (_, TyQu _ _ _)
              → return GT
            (TyApp _ _, _)
              → return LT
            (_, TyApp _ _)
              → return GT

instance Ord tv ⇒ Eq (NoRec tv) where
  σ1 == σ2 = compare σ1 σ2 == EQ

instance Ord tv ⇒ Ord (NoRec tv) where
  NoRec σ10 `compare` NoRec σ20 = loop σ10 σ20 where
    loop (TyVar r1)         (TyVar r2)
      = compare r1 r2
    loop (TyQu qu1 qls1 σ1) (TyQu qu2 qls2 σ2)
      = compare qu1 qu2   `mappend`
        compare qls1 qls2 `mappend`
        loop σ1 σ2
    loop (TyMu _ σ1)        (TyMu _ σ2)
      = loop σ1 σ2
    loop (TyRow l1 t1 t1')  (TyRow l2 t2 t2')
      = compare l1 l2     `mappend`
        loop t1 t2        `mappend`
        loop t1' t2'
    loop (TyApp tc1 σs1)    (TyApp tc2 σs2)
      = compare tc1 tc2   `mappend`
        mconcat (zipWith loop σs1 σs2)
    loop (TyVar _)          _                  = LT
    loop _                  (TyVar _)          = GT
    loop (TyQu _ _ _)       _                  = LT
    loop _                  (TyQu _ _ _)       = GT
    loop (TyMu _ _)         _                  = LT
    loop _                  (TyMu _ _)         = GT
    loop (TyRow _ _ _)      _                  = LT
    loop _                  (TyRow _ _ _)      = GT


