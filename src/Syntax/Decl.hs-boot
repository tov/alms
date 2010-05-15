-- vim: ft=haskell
{-# LANGUAGE
      FlexibleInstances,
      TypeFamilies,
      TypeSynonymInstances #-}
{-# OPTIONS_GHC -w #-}
module Syntax.Decl where

import Syntax.Notable
import Syntax.Ident (Id, Fv, Dv)

import Data.Data (Data)

data DeclNote i
data Decl' i
type Decl i = N (DeclNote i) (Decl' i)

instance Data i => Data (DeclNote i)
instance Data i => Data (Decl' i)
instance Locatable (DeclNote i)
instance Notable (DeclNote i)
instance Fv (N (DeclNote i) a)
instance Dv (N (DeclNote i) a)
