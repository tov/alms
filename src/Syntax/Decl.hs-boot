-- vim: ft=haskell
module Syntax.Decl where

import Data.Generics (Data)
import Loc (Locatable, Relocatable)

data Decl i

instance Data i => Data (Decl i)
instance Locatable (Decl i)
instance Relocatable (Decl i)
