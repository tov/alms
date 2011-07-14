-- | Source locations
{-# LANGUAGE
      DeriveDataTypeable,
      TypeFamilies #-}
module Data.Loc (
  -- * Type and constructors
  Loc(..),
  initial, spanLocs, mkBogus, bogus,
  -- * Destructors
  isBogus, startOfLoc, endOfLoc,

  -- * Generic function for clearing source locations everywhere
  scrub, scrubWhen,

  -- * For locating things
  -- ** Datatype interface
  {-
  Located(..), mkBogL, bogL,
  -}

  -- ** Type class interface
  Locatable(..), Relocatable(..), (<<@),

  -- * Interface to 'Parsec' and 'TH' source positions
  toSourcePos, fromSourcePos, fromSourcePosSpan, fromTHLoc
) where

import Util.Bogus

import Data.Generics (Typeable, Data, everywhere, mkT)
import Text.ParserCombinators.Parsec.Pos
import qualified Language.Haskell.TH as TH

-- | Source locations
data Loc = Loc {
    file  :: !String,
    line1 :: !Int,
    col1  :: !Int,
    line2 :: !Int,
    col2  :: !Int
  }
  deriving (Eq, Ord, Typeable, Data)

-- | Construct a location spanning two locations; assumes the locations
--   are correctly ordered.
spanLocs :: Loc -> Loc -> Loc
spanLocs loc1 loc2
  | isBogus loc2 = loc1
  | isBogus loc1 = loc2
  | otherwise    =
      Loc (file loc1) (line1 loc1) (col1 loc1) (line2 loc2) (col2 loc2)

-- | Get a single-point location from the start of a span
startOfLoc :: Loc -> Loc
startOfLoc loc = Loc (file loc) (line1 loc) (col1 loc) (line1 loc) (col1 loc)

-- | Get a single-point location from the end of a span
endOfLoc :: Loc -> Loc
endOfLoc loc = Loc (file loc) (line2 loc) (col2 loc) (line2 loc) (col2 loc)

-- | Extract a 'Parsec' source position
toSourcePos :: Loc -> SourcePos
toSourcePos loc = newPos (file loc) (line1 loc) (col1 loc)

-- | Create from a 'Parsec' source position
fromSourcePos :: SourcePos -> Loc
fromSourcePos pos
  = Loc (sourceName pos) (sourceLine pos) (sourceColumn pos)
                         (sourceLine pos) (sourceColumn pos)

-- | Create a span from two 'Parsec' source positions
fromSourcePosSpan :: SourcePos -> SourcePos -> Loc
fromSourcePosSpan pos1 pos2
  = Loc (sourceName pos1) (sourceLine pos1) (sourceColumn pos1)
                          (sourceLine pos2) (sourceColumn pos2)

fromTHLoc :: TH.Loc -> Loc
fromTHLoc loc = Loc (TH.loc_filename loc)
                    (fst (TH.loc_start loc))
                    (snd (TH.loc_start loc))
                    (fst (TH.loc_end loc))
                    (snd (TH.loc_end loc))

-- | The initial location for a named source file
initial :: String -> Loc
initial = fromSourcePos . initialPos

-- | A named bogus location; useful to provide default locations
--   for generated code without losing real locations.
mkBogus :: String -> Loc
mkBogus s = Loc s (-1) (-1) (-1) (-1)

-- | The bogus location.
--   (Avoids need for @Maybe Loc@ and lifting)
instance Bogus Loc where
  bogus    = mkBogus "<bogus>"

instance IsBogus Loc where
  isBogus (Loc _ (-1) _ _ _) = True
  isBogus _                  = False

-- | A value with a location attached
{-
data Located a = L {
                   locatedLoc :: !Loc,
                   locatedVal :: !a
                 }
  deriving (Eq, Ord, Typeable, Data)

mkBogL :: String -> a -> Located a
mkBogL  = L . mkBogus

bogL :: a -> Located a
bogL  = mkBogL "<bogus>"

instance Show a => Show (Located a) where
  showsPrec p = showsPrec p . locatedVal

instance Viewable (Located a) where
  type View (Located a) = a
  view = locatedVal
-}

-- | Class for types that carry source locations
class Locatable a where
  getLoc   :: a -> Loc

-- | Class for types that can have their source locations updated
class Relocatable a where
  setLoc   :: a -> Loc -> a

{-
instance Locatable (Located a) where
  getLoc (L loc _) = loc

instance Relocatable (Located a) where
  setLoc (L _ a) loc = L loc a
-}

instance Locatable Loc where
  getLoc   = id

instance Relocatable Loc where
  setLoc a b
    | isBogus b = a
    | otherwise = b

instance Locatable a => Locatable (Maybe a) where
  getLoc Nothing    = bogus
  getLoc (Just a)   = getLoc a

instance Relocatable a => Relocatable (Maybe a) where
  setLoc Nothing _  = Nothing
  setLoc (Just a) l = l `seq` a `seq` Just (setLoc a l)

instance Locatable a => Locatable [a] where
  getLoc = foldr spanLocs bogus . map getLoc

instance (Locatable a, Locatable b) => Locatable (Either a b) where
  getLoc (Left x)  = getLoc x
  getLoc (Right x) = getLoc x

instance (Relocatable a, Relocatable b) => Relocatable (Either a b) where
  setLoc (Left x)  l = Left (setLoc x l)
  setLoc (Right x) l = Right (setLoc x l)

instance (Locatable a, Locatable b) => Locatable (a, b) where
  getLoc (x, y) = getLoc x `spanLocs` getLoc y

instance (Locatable a, Locatable b, Locatable c) =>
         Locatable (a, b, c) where
  getLoc (x, y, z) = getLoc x `spanLocs` getLoc y `spanLocs` getLoc z

instance (Locatable a, Locatable b, Locatable c, Locatable d) =>
         Locatable (a, b, c, d) where
  getLoc (x, y, z, v) = getLoc x `spanLocs` getLoc y `spanLocs` getLoc z
                          `spanLocs` getLoc v

instance (Locatable a, Locatable b, Locatable c, Locatable d, Locatable e) =>
         Locatable (a, b, c, d, e) where
  getLoc (x, y, z, v, w) = getLoc x `spanLocs` getLoc y `spanLocs` getLoc z
                             `spanLocs` getLoc v `spanLocs` getLoc w

instance Relocatable b => Relocatable (a -> b) where
  setLoc f loc x = setLoc (f x) loc

-- | Copy the source location from the second operand to the first
(<<@)  :: (Relocatable a, Locatable b) => a -> b -> a
a <<@ b = setLoc a (getLoc b)

-- | Bogosify all source locations (as far as SYB can find them)
scrub :: Data a => a -> a
scrub = scrubWhen (const True)

-- | Bogosify all source locations satisfying a predicate
--   (as far as SYB can find them)
scrubWhen :: Data a => (Loc -> Bool) -> a -> a
scrubWhen p a = everywhere (mkT bogosify) a where
  bogosify loc | p loc     = bogus
               | otherwise = loc

instance Show Loc where
  showsPrec _ loc
    | isBogus loc = showString (showFile (file loc))
    | otherwise   =
        showString (showFile (file loc)) . showString " (" .
        showCoords . showString ")"
    where
    showCoords =
      if line1 loc == line2 loc then
        showString "line " . shows (line1 loc) . showString ", " .
        if col1 loc + 1 >= col2 loc then
          showString "column " . shows (col1 loc)
        else
          showString "columns " . shows (col1 loc) .
          showString "-" . shows (col2 loc)
      else
        showString "line " . shows (line1 loc) .
        showString ", col. " . shows (col1 loc) .
        showString " to line " . shows (line2 loc) .
        showString ", col. " . shows (col2 loc)
    showFile "-" = "<stdin>"
    showFile s   =
      let shown = show s
       in if shown == '"' : s ++ "\""
            then shown
            else s

