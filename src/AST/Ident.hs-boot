module AST.Ident where

import Data.Data (Data, Typeable1)

class Id i

data TyVar i

instance Typeable1 TyVar
instance Data i => Data (TyVar i)
instance Id i   => Ord (TyVar i)
instance Id i   => Eq (TyVar i)
