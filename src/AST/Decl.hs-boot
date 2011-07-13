-- vim: ft=haskell
{-# LANGUAGE
      FlexibleInstances,
      MultiParamTypeClasses,
      TypeFamilies,
      TypeSynonymInstances #-}
{-# OPTIONS_GHC -w #-}
module AST.Decl where

import AST.Notable
import AST.Ident (Id, Fv, Dv)

import Data.Data (Data, Typeable1)

data DeclNote i
data Decl' i
type Decl i = N (DeclNote i) (Decl' i)

instance Typeable1 DeclNote
instance Typeable1 Decl'
instance Id i => Data (DeclNote i)
instance Id i => Data (Decl' i)
instance Locatable (DeclNote i)
instance Notable (DeclNote i)
instance Id i => Fv (N (DeclNote i) a) i
instance Id i => Dv (N (DeclNote i) a) i
