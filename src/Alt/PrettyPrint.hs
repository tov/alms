{- | A layer over 'P.Doc' for propagating context information.  (I think
     Template Haskell has a version of this.) -}
module Alt.PrettyPrint (
  -- * Environment-parameterized pretty-printing document
  Doc(..),
  -- ** Environment operations
  mapD, askD, asksD, localD,
  -- * Document combinators
  -- ** Binary operations
  ($$), ($+$), (<+>), (<>),
  -- ** Unary operations
  braces, brackets, doubleQuotes, quotes, parens,
  -- ** List operations
  cat, fcat, fsep, hcat, hsep, sep, vcat,
  -- ** Miscellaneous operations
  nest, hang, punctuate,
  -- ** Nullary operations (documents)
  colon, comma, equals, lbrace, lbrack,
  lparen, rbrace, rbrack, rparen, semi, space,
  -- *** Unary functions returning documents
  char, double, float, int, integer, ptext, rational, text, zeroWidthText,
  -- * Rendering and queries
  toDocIn, isEmptyIn, renderIn, renderStyleIn, fullRenderIn,
  toDoc, isEmpty, render, renderStyle, fullRender,
  -- ** Rendering constants
  P.Mode(..), P.Style(..), P.TextDetails(..), P.style,
  -- * Module exports
  module Data.Monoid,
) where

import qualified Text.PrettyPrint as P
import Control.Applicative
import Data.Monoid hiding ((<>))

-- Document parameterized by type @e@.
newtype Doc e = Doc { unDoc :: e -> P.Doc }

--
-- Environment manipulation
--

mapD     :: (e' -> e) -> Doc e -> Doc e'
mapD f d  = Doc (unDoc d . f)

askD     :: (e -> Doc e) -> Doc e
askD f    = Doc (unDoc <$> f <*> id)

asksD    :: (e -> a) -> (a -> Doc e) -> Doc e
asksD g f = askD (f . g)

localD   :: e' -> Doc e' -> Doc e
localD    = mapD . const

--
-- Lifts
--

liftD0   :: P.Doc -> Doc e
liftD0    = Doc . const

liftD    :: (P.Doc -> P.Doc) -> Doc e -> Doc e
liftD f d = Doc (f <$> unDoc d)

liftD2 :: (P.Doc -> P.Doc -> P.Doc) ->
            Doc e -> Doc e -> Doc e
liftD2 f d1 d2 = Doc (f <$> unDoc d1 <*> unDoc d2)

liftDList :: ([P.Doc] -> P.Doc) -> [Doc e] -> Doc e
liftDList f ds = Doc (\e -> f [ d e | Doc d <- ds ])

--
-- Pretty-printing combinators
--

($$), ($+$), (<+>), (<>) :: Doc e -> Doc e -> Doc e
($$)   = liftD2 (P.$$)
($+$)  = liftD2 (P.$+$)
(<+>)  = liftD2 (P.<+>)
(<>)   = liftD2 (P.<>)

infixl 5 $$, $+$
infixl 6 <+>, <>

braces, brackets, doubleQuotes, parens, quotes :: Doc e -> Doc e
braces       = liftD P.braces
brackets     = liftD P.brackets
doubleQuotes = liftD P.doubleQuotes
quotes       = liftD P.quotes
parens       = liftD P.parens

nest      :: Int -> Doc e -> Doc e
nest         = liftD . P.nest

hang      :: Doc e -> Int -> Doc e -> Doc e
hang d1 n    = liftD2 (flip P.hang n) d1

punctuate :: Doc e -> [Doc e] -> [Doc e]
punctuate _  []     = []
punctuate _  [d]    = [d]
punctuate d1 (d:ds) = d<>d1 : punctuate d1 ds

cat, fcat, fsep, hcat, hsep, sep, vcat :: [Doc e] -> Doc e
cat   = liftDList P.cat
fcat  = liftDList P.fcat
fsep  = liftDList P.fsep
hcat  = liftDList P.hcat
hsep  = liftDList P.hsep
sep   = liftDList P.sep
vcat  = liftDList P.vcat

char            :: Char -> Doc e
double          :: Double -> Doc e
float           :: Float -> Doc e
int             :: Int -> Doc e
integer         :: Integer -> Doc e
ptext           :: String -> Doc e
rational        :: Rational -> Doc e
text            :: String -> Doc e
zeroWidthText   :: String -> Doc e

char             = liftD0 . P.char
double           = liftD0 . P.double
float            = liftD0 . P.float
int              = liftD0 . P.int
integer          = liftD0 . P.integer
ptext            = liftD0 . P.ptext
rational         = liftD0 . P.rational
text             = liftD0 . P.text
zeroWidthText    = liftD0 . P.zeroWidthText

colon, comma, equals, lbrace, lbrack, lparen, rbrace,
  rbrack, rparen, semi, space :: Doc e
colon   = liftD0 P.colon
comma   = liftD0 P.comma
equals  = liftD0 P.equals
lbrace  = liftD0 P.lbrace
lbrack  = liftD0 P.lbrack
lparen  = liftD0 P.lparen
rbrace  = liftD0 P.rbrace
rbrack  = liftD0 P.rbrack
rparen  = liftD0 P.rparen
semi    = liftD0 P.semi
space   = liftD0 P.space

--
-- Rendering and queries
--

toDocIn :: e -> Doc e -> P.Doc
toDocIn  = flip unDoc

isEmptyIn :: e -> Doc e -> Bool
isEmptyIn e = P.isEmpty . toDocIn e

renderIn :: e -> Doc e -> String
renderIn e  = P.render . toDocIn e

renderStyleIn :: e -> P.Style -> Doc e -> String
renderStyleIn e sty = P.renderStyle sty . toDocIn e

fullRenderIn :: e ->
                P.Mode -> Int -> Float ->
                (P.TextDetails -> a -> a) -> a ->
                Doc e -> a
fullRenderIn e mode cols ribbon f z =
  P.fullRender mode cols ribbon f z . toDocIn e

toDoc    :: Monoid e => Doc e -> P.Doc
toDoc     = toDocIn mempty

isEmpty :: Monoid e => Doc e -> Bool
isEmpty  = isEmptyIn mempty

render :: Monoid e => Doc e -> String
render  = renderIn mempty

renderStyle :: Monoid e => P.Style -> Doc e -> String
renderStyle = renderStyleIn mempty

fullRender :: Monoid e =>
              P.Mode -> Int -> Float ->
              (P.TextDetails -> a -> a) -> a ->
              Doc e -> a
fullRender = fullRenderIn mempty

instance Monoid (Doc e) where
  mempty   = liftD0 P.empty
  mappend  = (<>)
  mconcat  = hcat
