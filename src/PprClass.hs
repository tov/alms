module PprClass (
  -- * Pretty-printing class
  Ppr(..), IsInfix(..),
  -- * Pretty-printing combinators
  parensIf, (>+>), (>?>),
  -- * Renderers
  render, renderS, printDoc, printPpr,
  -- ** Instance helpers
  showFromPpr, pprFromShow,
  -- * Re-exports
  module Text.PrettyPrint
) where

import Text.PrettyPrint hiding (render)

-- | Class for pretty-printing at different types
--
-- Minimal complete definition is one of:
--
-- * 'pprPrec'
--
-- * 'ppr'
class Ppr p where
  -- | Print at the specified enclosing precedence
  pprPrec :: Int -> p -> Doc
  -- | Print at top-level precedence
  ppr     :: p -> Doc
  -- | Print a list at the specified enclosing precedence with
  --   the specified style
  pprPrecStyleList :: Int -> ListStyle -> [p] -> Doc
  -- | Print a list at the specified enclosing precedence
  pprPrecList :: Int -> [p] -> Doc
  -- | Print a list at top-level precedence
  pprList     :: [p] -> Doc
  -- | Style for printing lists
  listStyle   :: [p] -> ListStyle
  --
  ppr         = pprPrec 0
  pprPrec _   = ppr
  pprPrecStyleList _ st [] =
    if listStyleDelimitEmpty st
      then listStyleBegin st <> listStyleEnd st
      else empty
  pprPrecStyleList p st [x] =
    if listStyleDelimitSingleton st
      then listStyleBegin st <> ppr x <> listStyleEnd st
      else pprPrec p x
  pprPrecStyleList _ st xs  =
    listStyleBegin st <>
      listStyleJoiner st (punctuate (listStylePunct st) (map ppr xs))
    <> listStyleEnd st
  pprPrecList p xs = pprPrecStyleList p (listStyle xs) xs
  pprList          = pprPrecList 0
  listStyle _ = ListStyle {
    listStyleBegin            = lparen,
    listStyleEnd              = rparen,
    listStylePunct            = comma,
    listStyleDelimitEmpty     = False,
    listStyleDelimitSingleton = False,
    listStyleJoiner           = fsep
  }

data ListStyle = ListStyle {
  listStyleBegin, listStyleEnd, listStylePunct :: Doc,
  listStyleDelimitEmpty, listStyleDelimitSingleton :: Bool,
  listStyleJoiner :: [Doc] -> Doc
}

-- | Conditionally add parens around the given 'Doc'
parensIf :: Bool -> Doc -> Doc
parensIf True  doc = parens doc
parensIf False doc = doc

instance Ppr a => Ppr [a] where
  pprPrec = pprPrecList

instance Ppr a => Ppr (Maybe a) where
  pprPrec _ Nothing  = empty
  pprPrec p (Just a) = pprPrec p a

class Ppr a => IsInfix a where
  isInfix  :: a -> Bool
  pprRight :: Int -> a -> Doc
  pprRight p a =
    if isInfix a
      then pprPrec p a
      else ppr a

instance Ppr Doc where
  ppr = id

instance Ppr Int where
  ppr = int

-- Render a document in the preferred style, given a string continuation
renderS :: Doc -> ShowS
renderS doc rest = fullRender PageMode 80 1.1 each rest doc
  where each (Chr c) s'  = c:s'
        each (Str s) s'  = s++s'
        each (PStr s) s' = s++s'

-- Render a document in the preferred style
render :: Doc -> String
render doc = renderS doc ""

-- Render and display a document in the preferred style
printDoc :: Doc -> IO ()
printDoc = fullRender PageMode 80 1.1 each (putChar '\n')
  where each (Chr c) io  = putChar c >> io
        each (Str s) io  = putStr s >> io
        each (PStr s) io = putStr s >> io

-- Pretty-print, render and display in the preferred style
printPpr :: Ppr a => a -> IO ()
printPpr = printDoc . ppr

showFromPpr :: Ppr a => Int -> a -> ShowS
showFromPpr p t = renderS (pprPrec p t)

pprFromShow :: Show a => Int -> a -> Doc
pprFromShow p t = text (showsPrec p t "")

liftEmpty :: (Doc -> Doc -> Doc) -> Doc -> Doc -> Doc
liftEmpty joiner d1 d2
  | isEmpty d1 = d2
  | isEmpty d2 = d1
  | otherwise  = joiner d1 d2

(>+>) :: Doc -> Doc -> Doc
(>+>) = flip hang 2

(>?>) :: Doc -> Doc -> Doc
(>?>)  = liftEmpty (>+>)

infixr 5 >+>, >?>

