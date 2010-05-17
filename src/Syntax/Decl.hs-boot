-- vim: ft=haskell
{-# LANGUAGE
      FlexibleInstances,
      MultiParamTypeClasses,
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

instance Id i => Data (DeclNote i)
instance Id i => Data (Decl' i)
instance Locatable (DeclNote i)
instance Notable (DeclNote i)
instance Id i => Fv (N (DeclNote i) a) i
instance Id i => Dv (N (DeclNote i) a) i
