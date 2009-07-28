{-# LANGUAGE
      DeriveDataTypeable #-}
module Loc (
  Loc, file, line, col,
  initial, bogus, isBogus,
  scrub,
  Locatable(..), Relocatable(..), (<<@), cloneLoc,
  toSourcePos, fromSourcePos
) where

import Data.Typeable ()
import Data.Generics
import Text.ParserCombinators.Parsec.Pos

newtype Loc = Loc { toSourcePos :: SourcePos }
  deriving (Eq, Ord, Typeable)

fromSourcePos :: SourcePos -> Loc
fromSourcePos  = Loc

new :: String -> Int -> Int -> Loc
new f l c = fromSourcePos (newPos f l c)

file :: Loc -> String
file  = sourceName . toSourcePos

line :: Loc -> Int
line  = sourceLine . toSourcePos

col  :: Loc -> Int
col   = sourceColumn . toSourcePos

initial :: String -> Loc
initial = fromSourcePos . initialPos

bogus   :: Loc
bogus    = new "<bogus>" (-1) (-1)

isBogus :: Loc -> Bool
isBogus loc = case (file loc, line loc, col loc) of
  ("<bogus>", -1, -1) -> True
  _                   -> False

class Locatable a where
  getLoc   :: a -> Loc

class Relocatable a where
  setLoc   :: a -> Loc -> a

(<<@) :: Relocatable a => a -> Loc -> a
(<<@)  = setLoc

instance Locatable Loc where
  getLoc   = id

instance Relocatable Loc where
  setLoc _ = id

instance Locatable a => Locatable (Maybe a) where
  getLoc Nothing    = bogus
  getLoc (Just a)   = getLoc a

instance Relocatable a => Relocatable (Maybe a) where
  setLoc Nothing _  = Nothing
  setLoc (Just a) l = Just (setLoc a l)

instance Locatable a => Locatable [a] where
  getLoc []              = bogus
  getLoc (x:xs)
    | isBogus (getLoc x) = getLoc xs
    | otherwise          = getLoc x

instance Relocatable a => Relocatable [a] where
  setLoc [] _            = []
  setLoc (x:xs) l        = (setLoc x l:xs)

instance (Locatable a, Locatable b) => Locatable (Either a b) where
  getLoc (Left x)  = getLoc x
  getLoc (Right x) = getLoc x

instance (Relocatable a, Relocatable b) => Relocatable (Either a b) where
  setLoc (Left x)  l = Left (setLoc x l)
  setLoc (Right x) l = Right (setLoc x l)

instance (Locatable a, Locatable b) => Locatable (a, b) where
  getLoc (x, y)
    | not (isBogus (getLoc x)) = getLoc x
    | otherwise                = getLoc y

instance (Relocatable a, Relocatable b) => Relocatable (a, b) where
  setLoc (x, y) l        = (setLoc x l, y)

instance (Locatable a, Locatable b, Locatable c) =>
         Locatable (a, b, c) where
  getLoc (x, y, z)
    | not (isBogus (getLoc x)) = getLoc x
    | not (isBogus (getLoc y)) = getLoc y
    | otherwise                = getLoc z

instance (Relocatable a, Relocatable b, Relocatable c) =>
         Relocatable (a, b, c) where
  setLoc (x, y, z) l           = (setLoc x l, y, z)

instance (Locatable a, Locatable b, Locatable c, Locatable d) =>
         Locatable (a, b, c, d) where
  getLoc (x, y, z, v)
    | not (isBogus (getLoc x)) = getLoc x
    | not (isBogus (getLoc y)) = getLoc y
    | not (isBogus (getLoc z)) = getLoc z
    | otherwise                = getLoc v

instance (Relocatable a, Relocatable b, Relocatable c, Relocatable d) =>
         Relocatable (a, b, c, d) where
  setLoc (x, y, z, v) l        = (setLoc x l, y, z, v)

instance (Locatable a, Locatable b, Locatable c, Locatable d, Locatable e) =>
         Locatable (a, b, c, d, e) where
  getLoc (x, y, z, v, w)
    | not (isBogus (getLoc x)) = getLoc x
    | not (isBogus (getLoc y)) = getLoc y
    | not (isBogus (getLoc z)) = getLoc z
    | not (isBogus (getLoc v)) = getLoc v
    | otherwise                = getLoc w

instance (Relocatable a, Relocatable b, Relocatable c, Relocatable d, Relocatable e) =>
         Relocatable (a, b, c, d, e) where
  setLoc (x, y, z, v, w) l     = (setLoc x l, y, z, v, w)

instance Relocatable b => Relocatable (a -> b) where
  setLoc f loc x = setLoc (f x) loc

cloneLoc :: (Relocatable a, Locatable b) => a -> b -> a
cloneLoc a b = setLoc a (getLoc b)

scrub :: Data a => a -> a
scrub a = everywhere (mkT bogosify) a where
  bogosify :: Loc -> Loc
  bogosify  = const bogus

instance Show Loc where
  showsPrec p loc = showsPrec p (toSourcePos loc)

tyLoc  :: DataType
tyLoc   = mkDataType "Loc.Loc" [conLoc]
conLoc :: Constr
conLoc  = mkConstr tyLoc "Loc" [] Prefix

instance Data Loc where
  gfoldl f z loc = z new `f` file loc `f` line loc `f` col loc
  gunfold k z c  = case constrIndex c of
                     1 -> k (k (k (z new)))
                     _ -> error "gunfold"
  toConstr _     = conLoc
  dataTypeOf _   = tyLoc

