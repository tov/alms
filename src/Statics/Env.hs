{-# LANGUAGE TypeFamilies #-}
module Statics.Env (
  -- * Type variable environment
  Δ,
  -- * Main environment
  Γ(..), Γv, Γc, Γt, Γm, Γs, R,
  -- ** Operations
  bumpΓ, sigToEnv, sigItemToEnv, (!.!), (!..!), ExtendRank(..),
  -- * Testing
  test_g0,
  -- * Re-exports
  module Statics.Sig,
  module Env,
) where

import Util
import qualified AST
import Type
import Statics.Sig
import Statics.Error
import qualified Type.Rank as Rank
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
type Γc tv      = Env ConId (Either TyCon (Maybe (Type Empty)))
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
instance (v ~ VarId, tv ~ tv') ⇒
         GenExtend (Γ tv) (Env v (Type tv')) where       -- Γv
  e =+= ev' = e { varΓ = varΓ e =+= ev' }
instance (c ~ ConId, tc ~ TyCon, mt ~ Maybe (Type Empty)) ⇒
         GenExtend (Γ tv) (Env c (Either tc mt)) where  -- Γc
  e =+= ec' = e { conΓ = conΓ e =+= ec' }
instance t ~ TypId ⇒
         GenExtend (Γ tv) (Env t TyCon) where           -- Γt
  e =+= et' = e { typΓ = typΓ e =+= et' }
instance (s ~ Signature tv, g ~ Γ tv) ⇒
         GenExtend (Γ tv) (Env ModId (s, g)) where      -- Γm
  e =+= em' = e { modΓ = modΓ e =+= em' }
instance (s ~ Signature tv, g ~ Γ tv) ⇒
         GenExtend (Γ tv) (Env SigId (s, g)) where      -- Γs
  e =+= es' = e { sigΓ = sigΓ e =+= es' }
instance tv ~ tv' ⇒ GenExtend (Γ tv) (Signature tv') where
  e =+= sig = e =+= sigToEnv sig

instance GenLookup (Γ tv) VarId (Type tv) where
  (=..=) = (=..=) . varΓ
instance GenLookup (Γ tv) ConId (Either TyCon (Maybe (Type Empty))) where
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

(!.!) ∷ (GenLookup e k v, Show k, MonadAlmsError m) ⇒ e → k → m v
e !.! k = case e =..= k of
  Just v  → return v
  Nothing → typeBug "GenLookup" ("unbound identifier: " ++ show k)

(!..!) ∷ (GenLookup e k v, Show k) ⇒ e → k → v
e !..! k = case e =..= k of
  Just v  → v
  Nothing → typeBugError "GenLookup" ("unbound identifier: " ++ show k)

infixl 6 !.!, !..!

-- | Extend the environment and update the ranks of the free type
--   variables of the added types.
class ExtendRank a tv | a → tv where
  (!+!) ∷ MonadSubst tv r m ⇒ Γ tv → a → m (Γ tv)

infixl 2 !+!

instance ExtendRank (Γ tv) tv where
  γ !+! γ' = do
    lowerRank (Rank.inc (rankΓ γ)) =<< subst (range (varΓ γ'))
    return (bumpΓ γ =+= γ')

instance ExtendRank (Γv tv) tv where
  γ !+! γv = γ !+! mempty { varΓ = γv }

instance ExtendRank (Signature tv) tv where
  γ !+! sig = γ !+! sigToEnv sig

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

test_g0 ∷ ∀ tv. Tv tv ⇒ Γ tv
test_g0 = mempty
  =+= AST.ident "->"            =:= tcFun
  =+= AST.ident "unit"          =:= tcUnit
    =+= AST.ident "()"            =:= Left tcUnit
  =+= AST.ident "int"           =:= tcInt
  =+= AST.ident "exn"           =:= tcExn
    =+= AST.ident "Failure"       =:= Right (Just tyString)
    =+= AST.ident "Match"         =:= Right Nothing
  =+= AST.ident "U"             =:= tcUn
  =+= AST.ident "A"             =:= tcAf
  =+= AST.ident "\\/"           =:= tcJoin
  =+= AST.ident "*"             =:= tcTuple
  =+= AST.ident "rowend"        =:= tcRowEnd
  =+= AST.ident "variant"       =:= tcVariant
  =+= AST.ident "record"        =:= tcRecord
  =+= AST.ident "rowmap"        =:= tcRowMap
  =+= AST.ident "rowhole"       =:= tcRowHole
  =+= AST.ident "option"        =:= tcOption
    =+= AST.ident "None"          =:= Left tcOption
    =+= AST.ident "Some"          =:= Left tcOption
  =+= AST.ident "idfun"         =:= tcIdfun
    =+= AST.ident "Mono"          =:= Left tcIdfun
    =+= AST.ident "Poly"          =:= Left tcIdfun
  =+= AST.ident "ident"         =:= tcIdent
  =+= AST.ident "const"         =:= tcConst
  =+= AST.ident "cons"          =:= tcConsTup
  =+= AST.ident "x"             =:= tyInt
  =+= AST.ident "bot"           =:= TyQu Forall [(Nope, Qa)] (bvTy 0 0 Nope)
  =+= AST.ident "botU"          =:= TyQu Forall [(Nope, Qu)] (bvTy 0 0 Nope)

