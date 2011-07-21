{-# LANGUAGE
      UnicodeSyntax
    #-}
module Statics.Decl where

import qualified AST
import Statics.Constraint
import Statics.Env

tcDecl  ∷ MonadConstraint tv r m ⇒
          [ModId] → Γ tv → AST.Decl R →
          m (AST.Decl R, Γ tv, Signature tv)
