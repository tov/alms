{-# LANGUAGE
      FlexibleInstances
      #-}
module PprClass (
  -- * Documents
  Doc,
  -- * Pretty-printing class
  Ppr(..), IsInfix(..), ListStyle(..),
  -- ** Helpers
  ppr0, ppr1, pprDepth,
  -- ** Context operations
  prec, mapPrec, prec1, descend, atPrec, atDepth,
  askPrec, askDepth,
  trimList, trimCat,
  -- *** For type name shortening
  TyNames(..), tyNames0,
  setTyNames, askTyNames, enterTyNames, lookupTyNames,
  -- * Pretty-printing combinators
  (>+>), (>?>), ifEmpty,
  vcat, sep, cat, fsep, fcat,
  -- * Renderers
  render, renderS, printDoc, printPpr, hPrintDoc, hPrintPpr,
  -- ** Instance helpers
  showFromPpr, pprFromShow,
  -- * Re-exports
  module Util.PrettyPrint
) where

import Util.PrettyPrint hiding (Doc(..), render, vcat, sep, cat, fsep, fcat)
import qualified Util.PrettyPrint as P

import Syntax.Ident (QLid, Uid, Renamed)

import System.IO (Handle, stdout, hPutChar, hPutStr)

-- | Context for pretty-printing.
data PprContext
  = PprContext {
      pcPrec   :: !Int,
      pcDepth  :: !Int,
      pcTyName :: !TyNames
  }

data TyNames =
  TyNames {
    tnLookup   :: Int -> QLid Renamed -> QLid Renamed,
    tnEnter    :: Uid Renamed -> TyNames
  }

-- | Default context
pprContext0 :: PprContext
pprContext0  = PprContext {
  pcPrec   = 0,
  pcDepth  = -1,
  pcTyName = tyNames0
}

tyNames0 :: TyNames
tyNames0  = TyNames {
  tnLookup = const id,
  tnEnter  = const tyNames0
}

type Doc = P.Doc PprContext

data ListStyle 
  = ListStyle {
    listStyleBegin, listStyleEnd, listStylePunct :: Doc,
    listStyleDelimitEmpty, listStyleDelimitSingleton :: Bool,
    listStyleJoiner :: [Doc] -> Doc
  }

-- | Class for pretty-printing at different types
--
-- Minimal complete definition is one of:
--
-- * 'pprPrec'
--
-- * 'ppr'
class Ppr p where
  -- | Print current precedence
  ppr     :: p -> Doc
  -- | Print at the specified enclosing precedence
  pprPrec :: Int -> p -> Doc
  -- | Print a list in the default style
  pprList :: [p] -> Doc
  -- | Print a list in the specified style
  pprStyleList :: ListStyle -> [p] -> Doc
  -- | Style for printing lists
  listStyle   :: [p] -> ListStyle
  --
  --
  ppr         = asksD pcPrec . flip pprPrec
  pprPrec p   = prec p . ppr
  pprList xs  = pprStyleList (listStyle xs) xs
  --
  pprStyleList st [] =
    if listStyleDelimitEmpty st
      then listStyleBegin st <> listStyleEnd st
      else mempty
  pprStyleList st [x] =
    if listStyleDelimitSingleton st
      then listStyleBegin st <> ppr x <> listStyleEnd st
      else ppr x
  pprStyleList st xs  =
    listStyleBegin st <>
      listStyleJoiner st (punctuate (listStylePunct st) (map ppr xs))
    <> listStyleEnd st
  --
  listStyle _ = ListStyle {
    listStyleBegin            = lparen,
    listStyleEnd              = rparen,
    listStylePunct            = comma,
    listStyleDelimitEmpty     = False,
    listStyleDelimitSingleton = False,
    listStyleJoiner           = fsep
  }

-- | Print at top level.
ppr0      :: Ppr p => p -> Doc
ppr0       = atPrec 0 . ppr

-- | Print at next level.
ppr1      :: Ppr p => p -> Doc
ppr1       = prec1 . ppr

-- | Print to the given depth.
pprDepth  :: Ppr p => Int -> p -> Doc
pprDepth d = atDepth d . ppr

-- | Enter the given precedence level, drawing parentheses if necessary,
--   and count it as a descent in depth as well.
prec :: Int -> Doc -> Doc
prec p doc = asksD pcPrec $ \p' ->
  if p' > p
    then descend $ parens (atPrec (min p 0) doc)
    else atPrec p doc

-- | Adjust the precedence with the given function.
mapPrec :: (Int -> Int) -> Doc -> Doc
mapPrec f doc = askPrec (\p -> prec (f p) doc)

-- | Go to the next (tigher) precedence level.
prec1 :: Doc -> Doc
prec1  = mapD (\e -> e { pcPrec = pcPrec e + 1 })

-- | Descend a level, elliding if the level counter runs out
descend :: Doc -> Doc
descend doc = askD $ \e ->
  case pcDepth e of
    -1 -> doc
    0  -> text "..."
    k  -> localD e { pcDepth = k - 1 } doc

-- | Set the precedence, but check or draw parentheses
atPrec   :: Int -> Doc -> Doc
atPrec p  = mapD (\e -> e { pcPrec = p })

-- | Set the precedence, but check or draw parentheses
atDepth  :: Int -> Doc -> Doc
atDepth k = mapD (\e -> e { pcDepth = k })

-- | Find out the precedence
askPrec :: (Int -> Doc) -> Doc
askPrec  = asksD pcPrec

-- | Find out the depth
askDepth :: (Int -> Doc) -> Doc
askDepth  = asksD pcDepth

-- | Change the type name lookup function
setTyNames   :: TyNames -> Doc -> Doc
setTyNames f  = mapD (\e -> e { pcTyName = f })

-- | Retrieve the type name lookup function
askTyNames   :: (TyNames -> Doc) -> Doc
askTyNames    = asksD pcTyName

-- | Render a document with a module opened
enterTyNames :: Uid Renamed -> Doc -> Doc
enterTyNames u doc = askTyNames $ \tn ->
  setTyNames (tnEnter tn u) doc

-- | Look up a type name in the rendering context
lookupTyNames :: Int -> QLid Renamed -> (QLid Renamed -> Doc) -> Doc
lookupTyNames tag ql kont = askTyNames $ \tn ->
  kont (tnLookup tn tag ql)

-- | Trim a list to (about) the given number of elements, with
--   "..." in the middle.
trimList :: Int -> [Doc] -> [Doc]
trimList (-1) ds = ds
trimList n2   ds = if k <= 2 * n
                     then ds
                     else take n ds ++ text "... " : drop (k - n) ds
  where
    n = (n2 + 1) `div` 2
    k = length ds

-- | Lift a concatenation function to respect depth.
trimCat :: ([Doc] -> Doc) -> [Doc] -> Doc
trimCat xcat docs = asksD pcDepth $ \d -> case d of
  -1 -> xcat docs
  _  -> atDepth ((d + 1) `div` 2) (xcat (trimList d docs))

vcat, sep, cat, fsep, fcat :: [Doc] -> Doc
vcat = trimCat P.vcat
sep  = trimCat P.sep
cat  = trimCat P.cat
fsep = trimCat P.fsep
fcat = trimCat P.fcat

instance Ppr a => Ppr [a] where
  ppr = pprList

instance Ppr a => Ppr (Maybe a) where
  pprPrec _ Nothing  = mempty
  pprPrec p (Just a) = pprPrec p a

-- | Class to check if a particular thing will print infix.  Adds
--   an operation to print at the given precedence only if the given
--   thing is infix.  (We use this for printing arrows without too
--   many parens.)
class Ppr a => IsInfix a where
  isInfix  :: a -> Bool
  pprRight :: a -> Doc
  pprRight a =
    if isInfix a
      then ppr a
      else ppr0 a

instance Ppr Int       where ppr = int
instance Ppr Integer   where ppr = integer
instance Ppr Double    where ppr = double

instance Ppr Char where
  ppr            = text . show
  pprStyleList _ = text

instance Ppr (P.Doc PprContext)  where ppr = id
instance Show (P.Doc PprContext) where showsPrec = showFromPpr

-- Render a document in the preferred style, given a string continuation
renderS :: Doc -> ShowS
renderS doc rest = fullRenderIn pprContext0 PageMode 80 1.1 each rest doc
  where each (Chr c) s'  = c:s'
        each (Str s) s'  = s++s'
        each (PStr s) s' = s++s'

-- Render a document in the preferred style
render :: Doc -> String
render doc = renderS doc ""

-- Render and display a document in the preferred style
printDoc :: Doc -> IO ()
printDoc  = hPrintDoc stdout

-- Pretty-print, render and display in the preferred style
printPpr :: Ppr a => a -> IO ()
printPpr  = hPrintPpr stdout

-- Render and display a document in the preferred style
hPrintDoc :: Handle -> Doc -> IO ()
hPrintDoc h = fullRenderIn pprContext0 PageMode 80 1.1 each (putChar '\n')
  where each (Chr c) io  = hPutChar h c >> io
        each (Str s) io  = hPutStr h s >> io
        each (PStr s) io = hPutStr h s >> io

hPrintPpr :: Ppr a => Handle -> a -> IO ()
hPrintPpr h = hPrintDoc h . ppr

showFromPpr :: Ppr a => Int -> a -> ShowS
showFromPpr p t = renderS (pprPrec p t)

pprFromShow :: Show a => Int -> a -> Doc
pprFromShow p t = text (showsPrec p t "")

--
-- Some indentation operations
--

liftEmpty :: (Doc -> Doc -> Doc) -> Doc -> Doc -> Doc
liftEmpty joiner d1 d2 = askD f where
  f e | isEmptyIn e d1 = d2
      | isEmptyIn e d2 = d1
      | otherwise      = joiner d1 d2

ifEmpty :: Doc -> Doc -> Doc -> Doc
ifEmpty dc dt df = askD $ \e ->
  if isEmptyIn e dc
    then dt
    else df

(>+>) :: Doc -> Doc -> Doc
(>+>) = flip hang 2

(>?>) :: Doc -> Doc -> Doc
(>?>)  = liftEmpty (>+>)

infixr 5 >+>, >?>

