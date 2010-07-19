module Message.Parser (
  parseMessageQ, tokensT, messageP,
) where

import Loc
import Message.AST
import Util

import Data.Char
import Language.Haskell.TH
import Text.ParserCombinators.Parsec

-- | Given the string representation of a message, parse it,
--   using the Template Haskell monad to get an initial source
--   location and for errors.
parseMessageQ :: String -> Q MessageV
parseMessageQ str0 = do
  loc  <- location
  toks <- either (fail . show) return $
    parse (setPosition (toSourcePos (fromTHLoc loc)) *> tokensT)
          "" str0
  either (fail . show) return $
    parse messageP "" toks

--
-- Lexer
--

data Token
  = BTag String
  | ETag String
  | Word String
  | Chars String
  | Whitespace String
  | AntiTok String String
  deriving (Eq, Show)

tokensT :: CharParser () [(SourcePos, Token)]
tokensT  = many (getPosition |*| tokenT) <* eof

tokenT :: CharParser () Token
tokenT  = choice [charsT, tagT, wordT, whitespaceT, antiT]

charsT :: CharParser () Token
charsT  = tstring "<exact>" *>
          (Chars <$> manyTill anyChar (tstring "</exact>"))

tagT :: CharParser () Token
tagT = between (char '<') (char '>') $
  option BTag (ETag <$ char '/')
  <*> many1 lower

wordT :: CharParser () Token
wordT = Word <$> many1 wordChar
  where wordChar = satisfy (\x -> not (isSpace x || x `elem` "<&$"))
               <|> '&' <$ tstring "&amp;"
               <|> '$' <$ tstring "&dollar;"
               <|> '<' <$ tstring "&lt;"
               <|> '>' <$ tstring "&gt;"

whitespaceT :: CharParser () Token
whitespaceT  = Whitespace <$> many1 space

antiT :: CharParser () Token
antiT = char '$' *> (inner <|> between (char '<') (char '>') inner)
  where inner = combine <$> many1 alphaNum
                        <*> optionMaybe (char ':' *> many1 alphaNum)
            <|> AntiTok "" <$> (char ':' *> many1 alphaNum)
        combine name Nothing     = AntiTok "" name
        combine tag  (Just name) = AntiTok tag name

tstring :: String -> CharParser () String
tstring  = try . string

--
-- Token parsers
--

type P a = GenParser (SourcePos, Token) () a

tsatisfy      :: (Token -> Maybe a) -> P a
tsatisfy check = token show fst (check . snd)

exact :: P String
exact = tsatisfy check where
  check (Chars s) = Just s
  check _         = Nothing

btag  :: String -> P ()
btag s = tsatisfy check where
  check (BTag s') | s == s' = Just ()
  check _                   = Nothing

etag  :: String -> P ()
etag s = tsatisfy check where
  check (ETag s') | s == s' = Just ()
  check _                   = Nothing

word  :: P String
word   = tsatisfy check where
  check (Word s) = Just s
  check _        = Nothing

whitespace :: P ()
whitespace  = tsatisfy check where
  check (Whitespace _) = Just ()
  check _              = Nothing

ws   :: P ()
ws    = () <$ many whitespace

anti :: Bool -> P (String, String)
anti v = tsatisfy check where
  check (AntiTok tag name) 
    | elem tag vtags == v = Just (tag, name)
  check _                  = Nothing

vtags :: [String]
vtags  = ["ol", "ul", "br", "p", "dl", "indent"]

intag     :: String -> P a -> P a
intag s    = between (btag s) (etag s)

intagV    :: String -> P a -> P a
intagV s p = intag s (ws *> p) <* ws

pretag  :: String -> P a -> P a
pretag s p = between (btag s *> ws) (optional (etag s)) p <* ws

--
-- Parser
--

messageP :: P MessageV
messageP  = ws *> parseV <* eof

-- | Vertical-mode message
parseV  :: P MessageV
parseV   = option emptyMsg parse1V

-- | Vertical-mode message, non-empty
parse1V :: P MessageV
parse1V  = wrapMany (Stack Separated) <$> many1skip paragraphV (btag "p" *> ws)

paragraphV :: P MessageV
paragraphV  = wrapMany (Stack Broken) <$> many1skip lineV (btag "br" *> ws)

lineV      :: P MessageV
lineV       = antiV
          <|> blockV
          <|> indentV
          <|> quoteV
          <|> listV
          <|> tableV
          <|> parse1H

antiV      :: P MessageV
antiV       = uncurry AntiMsg <$> anti True <* ws

blockV     :: P MessageV
blockV      = Block <$> intagV "block" parseH

indentV    :: P MessageV
indentV     = Indent <$> intagV "indent" parseV

quoteV     :: P MessageV
quoteV      = Quote <$> intagV "qq" parseV

listV      :: P MessageV
listV       = Stack Numbered <$> intagV "ol" items
          <|> Stack Bulleted <$> intagV "ul" items
  where items = many1skip parse1V (btag "li" *> ws)

tableV     :: P MessageV
tableV      = (Indent . Table) <$> intagV "dl" items
  where items = many $
           (unwords <$> pretag "dt" (manyskip word whitespace))
           |*| pretag "dd" parseV

-- | Horizontal-mode message, non-empty
parse1H :: P (Message d)
parse1H  = Flow <$> many1skip itemH whitespace

-- | Horizontal-mode message
parseH  :: P (Message d)
parseH   = Flow <$> manyskip itemH whitespace

-- | A horizontal item, either text or special
itemH    :: P (Message d)
itemH     = trailingH "" <|> do
  start <- word
  option (Exact start) (trailingH start)

-- | Special horizontal markup, maybe with some leading or
--   trailing word
trailingH :: String -> P (Message d)
trailingH start = makeSurround start <$> specialH <*> option "" word

-- | Special horizontal markup: quotations, exact, and antiquotes
specialH :: P (Message d)
specialH  = Quote <$> intag "q" parseH
        <|> Exact <$> exact
        <|> uncurry AntiMsg <$> anti False

makeSurround :: String -> Message d -> String -> Message d
makeSurround ""    m ""  = m
makeSurround start m end = Surround start end m

-- | Combine, but only if there's more than one
wrapMany :: ([a] -> a) -> [a] -> a
wrapMany _ [x] = x
wrapMany w xs  = w xs

emptyMsg :: Message d
emptyMsg  = Exact ""

--
-- Auxiliary
--

(|*|) :: Applicative f => f a -> f b -> f (a, b)
a |*| b = (,) <$> a <*> b

(|:|) :: Applicative f => f a -> f [a] -> f [a]
a |:| b = (:) <$> a <*> b

infixl 4 |*|, |:|

-- | Parse a list of things, skipping optional things
manyskip  :: P a -> P b -> P [a]
manyskip save skip  = save |:| manyskip save skip
                  <|> skip *> manyskip save skip
                  <|> pure []

-- | Parse a list of things (at least one), skipping optional things
many1skip :: P a -> P b -> P [a]
many1skip save skip = save |:| manyskip save skip
                  <|> skip *> many1skip save skip
                  <|> pzero

