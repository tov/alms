-- vim: ft=haskell
{-# LANGUAGE
      FlexibleInstances,
      MultiParamTypeClasses,
      RoleAnnotations,
      TypeFamilies,
      TypeSynonymInstances #-}
{-# OPTIONS_GHC -w #-}
module AST.Decl where

import AST.Notable
import AST.Ident (Tag, Fv, Dv)

import Data.Data (Data, Typeable)

type role DeclNote nominal
type role Decl' nominal

data DeclNote i
data Decl' i
type Decl i = N (DeclNote i) (Decl' i)

instance Typeable DeclNote
instance Typeable Decl'
instance Tag i => Data (DeclNote i)
instance Tag i => Data (Decl' i)
instance Locatable (DeclNote i)
instance Notable (DeclNote i)
instance Tag i => Fv (N (DeclNote i) a) i
instance Tag i => Dv (N (DeclNote i) a) i
