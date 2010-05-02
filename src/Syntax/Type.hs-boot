module Syntax.Type (TyTag, getTdByName) where

import Data.Generics (Data)

data TyTag

instance Data TyTag

getTdByName :: String -> Maybe TyTag
