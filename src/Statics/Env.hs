{-# LANGUAGE
      DeriveDataTypeable,
      DeriveFunctor,
      FlexibleInstances,
      MultiParamTypeClasses,
      GeneralizedNewtypeDeriving,
      ScopedTypeVariables,
      TypeSynonymInstances,
      UnicodeSyntax
    #-}
module Statics.Env (
  -- * Type variable environment
  Δ,
  -- * Main environment
  Γ(..), Γv, Γc, Γt, Γm, Γs, TYPE(..),
  -- ** Operations
  bumpΓ, sigToEnv, sigItemToEnv,
) where

import Util
import AST.Ident
import qualified AST
import Type
import Statics.Sig
import qualified Rank
import Env

import Prelude ()
import Data.Generics (Typeable, Data)
import qualified Data.Map as M

type R = AST.Renamed

-- | Mapping from type variable names to type variables
type Δ tv = M.Map (AST.TyVar R) tv

-- | Mapping variable names to type
type Γv tv      = Env (Lid R) (Type tv)
-- | Mapping data constructor names to type constructors or exception
--   parameter types
type Γc tv      = Env (Uid R) (Either TyCon (Maybe (Type tv)))
-- | Mapping type names to type constructors
type Γt tv      = Env (Lid R) TyCon
-- | Mapping module names to their signatures and reflection as an environment
type Γm tv      = Env (Uid R) (Signature tv, Γ tv)
-- | Mapping signature names to signatures and reflection as an environment
type Γs tv      = Env (TYPE (Uid R)) (Signature tv, Γ tv)

-- | Wrapper for specifying type rather than value operations
newtype TYPE a = TYPE { unTYPE ∷ a }
  deriving (Eq, Ord, Show, Functor, Bogus, IsBogus, Id, Typeable, Data)

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
  deriving (Functor, Show)

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
sigItemToEnv (SiValue n τ)     = mempty { varΓ = n =:= τ }
sigItemToEnv (SiType n tc)     =
  mempty {
    typΓ = n =:= tc,
    conΓ = Left tc <$ tcCons tc
  }
sigItemToEnv (SiExn n mτ)      = mempty { conΓ = n =:= Right mτ }
sigItemToEnv (SiModule n sig)  = mempty { modΓ = n =:= (sig, sigToEnv sig) }
sigItemToEnv (SiModType n sig) = mempty { sigΓ = TYPE n =:= (sig, sigToEnv sig) }

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

instance GenLookup (Γ tv) (Lid R) (Type tv) where
  (=..=) = (=..=) . varΓ
instance GenLookup (Γ tv) (Uid R) (Either TyCon (Maybe (Type tv))) where
  (=..=) = (=..=) . conΓ
instance GenLookup (Γ tv) (TYPE (Lid R)) TyCon where
  (=..=) = (=..=) . typΓ <$.> unTYPE

{-
instance GenLookup (Γ tv) (Lid R) TyCon where
  e =..= k = tlevel e =..= k
instance GenLookup (Γ tv) (Uid R) (Module, (Γ tv)) where
  e =..= k = mlevel e =..= k
instance GenLookup (Γ tv) SIGVAR (Module, (Γ tv)) where
  e =..= k = slevel e =..= k
instance GenLookup (Γ tv) k v =>
         GenLookup (Γ tv) (Path (Uid R) k) v where
  e =..= J []     k = e =..= k
  e =..= J (p:ps) k = do
    (_, e') <- e =..= p
    e' =..= J ps k

-}
