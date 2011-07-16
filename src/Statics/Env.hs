{-# LANGUAGE
      DeriveDataTypeable,
      DeriveFunctor,
      FlexibleContexts,
      FlexibleInstances,
      MultiParamTypeClasses,
      GeneralizedNewtypeDeriving,
      ScopedTypeVariables,
      TypeSynonymInstances,
      UndecidableInstances,
      UnicodeSyntax
    #-}
module Statics.Env (
  -- * Type variable environment
  Δ,
  -- * Main environment
  Γ(..), Γv, Γc, Γt, Γm, Γs, R,
  -- ** Operations
  bumpΓ, sigToEnv, sigItemToEnv, (!.!),
  module Statics.Sig,
  module Env,
) where

import Util
import qualified AST
import Type
import Statics.Sig
import Statics.Error
import qualified Rank
import qualified Syntax.Ppr as Ppr
import Env

import Prelude ()
import Data.Generics (Typeable, Data)
import qualified Data.Map as M

type R = AST.Renamed

-- | Mapping from type variable names to type variables
type Δ tv = Env (AST.TyVar R) tv

-- | Mapping variable names to type
type Γv tv      = Env VarId (Type tv)
-- | Mapping data constructor names to type constructors or exception
--   parameter types
type Γc tv      = Env ConId (Either TyCon (Maybe (Type tv)))
-- | Mapping type names to type constructors
type Γt tv      = Env TypId TyCon
-- | Mapping module names to their signatures and reflection as an environment
type Γm tv      = Env ModId (Signature tv, Γ tv)
-- | Mapping signature names to signatures and reflection as an environment
type Γs tv      = Env SigId (Signature tv, Γ tv)

-- | An environment
data Γ tv
  = Γ {
      rankΓ     ∷ !Rank.Rank,
      varΓ      ∷ !(Γv tv),
      conΓ      ∷ !(Γc tv),
      typΓ      ∷ !(Γt tv),
      modΓ      ∷ !(Γm tv),
      sigΓ      ∷ !(Γs tv)
    }
  deriving (Functor, Show, Typeable, Data)

instance Monoid (Γ tv) where
  mempty = Γ Rank.zero empty empty empty empty empty
  Γ rank a b c d e `mappend` Γ rank' a' b' c' d' e'
    = Γ (rank `max` rank') (a=+=a') (b=+=b') (c=+=c') (d=+=d') (e=+=e')

-- | Increment the rank of the environment
bumpΓ ∷ Γ tv → Γ tv
bumpΓ γ = γ { rankΓ = Rank.inc (rankΓ γ) }

-- | Reflect a signature as an environment
sigToEnv ∷ Signature tv → Γ tv
sigToEnv = foldMap sigItemToEnv

-- | Reflect a signature item as an environment
sigItemToEnv ∷ SigItem tv → Γ tv
sigItemToEnv (SgVal n τ)   = mempty { varΓ = n =:= τ }
sigItemToEnv (SgTyp n tc)  =
  mempty {
    typΓ = n =:= tc,
    conΓ = Left tc <$ tcCons tc
  }
sigItemToEnv (SgExn n mτ)  = mempty { conΓ = n =:= Right mτ }
sigItemToEnv (SgMod n sig) = mempty { modΓ = n =:= (sig, sigToEnv sig) }
sigItemToEnv (SgSig n sig) = mempty { sigΓ = n =:= (sig, sigToEnv sig) }

---
--- INSTANCES
---

instance GenEmpty (Γ tv) where
  genEmpty = mempty

instance GenExtend (Γ tv) (Γ tv) where
  (=+=) = mappend
instance GenExtend (Γ tv) (Γv tv) where
  e =+= ev' = e { varΓ = varΓ e =+= ev' }
instance GenExtend (Γ tv) (Γc tv) where
  e =+= ec' = e { conΓ = conΓ e =+= ec' }
instance GenExtend (Γ tv) (Γt tv) where
  e =+= et' = e { typΓ = typΓ e =+= et' }
instance GenExtend (Γ tv) (Γm tv) where
  e =+= em' = e { modΓ = modΓ e =+= em' }
instance GenExtend (Γ tv) (Γs tv) where
  e =+= es' = e { sigΓ = sigΓ e =+= es' }

instance GenLookup (Γ tv) VarId (Type tv) where
  (=..=) = (=..=) . varΓ
instance GenLookup (Γ tv) ConId (Either TyCon (Maybe (Type tv))) where
  (=..=) = (=..=) . conΓ
instance GenLookup (Γ tv) TypId TyCon where
  (=..=) = (=..=) . typΓ
instance GenLookup (Γ tv) ModId (Signature tv, Γ tv) where
  (=..=) = (=..=) . modΓ
instance GenLookup (Γ tv) SigId (Signature tv, Γ tv) where
  (=..=) = (=..=) . sigΓ
instance GenLookup (Γ tv) k v =>
         GenLookup (Γ tv) (Path ModId k) v where
  e =..= J []     k = e =..= k
  e =..= J (p:ps) k = do
    (_, e') <- e =..= p
    e' =..= J ps k

(!.!) ∷ (GenLookup e k v, Show k) ⇒ MonadAlmsError m ⇒ e → k → m v
e !.! k = case e =..= k of
  Just v  → return v
  Nothing → typeBug "GenLookup" ("unbound identifier: " ++ show k)

infixl 6 !.!

instance (Ppr.Ppr k, Ppr.Ppr v) ⇒ Ppr.Ppr (Env k v) where
  ppr env = Ppr.braces . Ppr.fsep . Ppr.punctuate Ppr.comma $
    [ Ppr.ppr0 k Ppr.<> Ppr.colon Ppr.<+> Ppr.ppr0 v
    | (k, v) <- Env.toList env ]

instance Tv tv ⇒ Ppr.Ppr (Γ tv) where
  ppr γ = Ppr.char 'Γ' Ppr.<> Ppr.ppr (M.fromList
    [ ("rank", Ppr.ppr0 $ rankΓ γ)
    , ("typ",  Ppr.ppr0 $ typΓ γ)
    , ("var",  Ppr.ppr0 $ varΓ γ)
    , ("con",  Ppr.ppr0 $ conΓ γ)
    , ("mod",  Ppr.ppr0 $ snd <$> modΓ γ)
    , ("sig",  Ppr.ppr0 $ snd <$> sigΓ γ)
    ])
