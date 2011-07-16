-- vim: ft=haskell
{-# LANGUAGE
      FlexibleInstances,
      MultiParamTypeClasses,
      TypeFamilies,
      TypeSynonymInstances #-}
{-# OPTIONS_GHC -w #-}
module AST.Decl where

import AST.Notable
import AST.Ident (Tag, Fv, Dv)

import Data.Data (Data, Typeable1)

data DeclNote i
data Decl' i
type Decl i = N (DeclNote i) (Decl' i)

instance Typeable1 DeclNote
instance Typeable1 Decl'
instance Tag i => Data (DeclNote i)
instance Tag i => Data (Decl' i)
instance Locatable (DeclNote i)
instance Notable (DeclNote i)
instance Tag i => Fv (N (DeclNote i) a) i
instance Tag i => Dv (N (DeclNote i) a) i
