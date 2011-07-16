module AST.Ident where

import Data.Data (Data, Typeable1)

class Tag i

data TyVar i

instance Typeable1 TyVar
instance Data i => Data (TyVar i)
instance Tag i   => Ord (TyVar i)
instance Tag i   => Eq (TyVar i)
