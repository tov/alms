module Syntax.Ident where

import Data.Data (Data)

class Id i

data TyVar i

instance Data i => Data (TyVar i)
instance Id i   => Ord (TyVar i)
