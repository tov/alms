module Message.Parser (
  parseMessageQ, tokensT, messageP,
) where

import Data.Loc
import Message.AST
import Util
import Alt.Parsec

import Prelude ()
import Data.Char
import Language.Haskell.TH

-- | Given the string representation of a message, parse it,
--   using the Template Haskell monad to get an initial source
--   location and for errors.
parseMessageQ :: String -> Q (Message V)
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

tokensT :: Parsec String () [(SourcePos, Token)]
tokensT  = many (getPosition |*| tokenT) <* eof

tokenT :: Parsec String () Token
tokenT  = choice [charsT, tagT, wordT, whitespaceT, antiT]

charsT :: Parsec String () Token
charsT  = tstring "<exact>" *>
          (Chars <$> manyTill anyChar (tstring "</exact>"))

tagT :: Parsec String () Token
tagT = between (char '<') (char '>') $
  option BTag (ETag <$ char '/')
  <*> many1 lower

wordT :: Parsec String () Token
wordT = Word <$> many1 wordChar
  where wordChar = satisfy (\x -> not (isSpace x || x `elem` "<&$"))
               <|> '&' <$ tstring "&amp;"
               <|> '$' <$ tstring "&dollar;"
               <|> '<' <$ tstring "&lt;"
               <|> '>' <$ tstring "&gt;"

whitespaceT :: Parsec String () Token
whitespaceT  = Whitespace <$> many1 space

antiT :: Parsec String () Token
antiT = char '$' *> (inner <|> between (char '<') (char '>') inner)
  where inner = combine <$> ident
                        <*> optionMaybe (char ':' *> ident)
            <|> AntiTok "" <$> (char ':' *> ident)
        combine name Nothing     = AntiTok "" name
        combine tag  (Just name) = AntiTok tag name

ident :: Parsec String () String
ident  = many1 digit
     <|> lower |:| many (alphaNum <|> oneOf "'_")

tstring :: String -> Parsec String () String
tstring  = try . string

--
-- Token parsers
--

type P a = Parsec [(SourcePos, Token)] () a

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
    | isDTag v tag  = Just (tag, name)
  check _           = Nothing

isDTag :: Bool -> String -> Bool
isDTag _ "msg"     = True
isDTag v ('v':_)   = v
isDTag v ('h':_)   = not v
isDTag v ('q':tag) = isDTag v tag
isDTag v tag       = v == elem tag vtags
  where vtags = ["ol", "ul", "br", "p", "dl", "indent"]

intag     :: String -> P a -> P a
intag s    = between (btag s) (etag s)

intagV    :: String -> P a -> P a
intagV s p = intag s (ws *> p) <* ws

pretag  :: String -> P a -> P a
pretag s p = between (btag s *> ws) (optional (etag s)) p <* ws

--
-- Parser
--

messageP :: P (Message V)
messageP  = ws *> parseV <* eof

-- | Vertical-mode message
parseV  :: P (Message V)
parseV   = option emptyMsg parse1V

-- | Vertical-mode message, non-empty
parse1V :: P (Message V)
parse1V  = wrapMany (Stack Separated) <$> many1skip paragraphV (btag "p" *> ws)

paragraphV :: P (Message V)
paragraphV  = wrapMany (Stack Broken) <$> many1skip lineV (btag "br" *> ws)

lineV      :: P (Message V)
lineV       = antiV
          <|> indentV
          <|> quoteV
          <|> listV
          <|> tableV
          <|> parse1H

antiV      :: P (Message V)
antiV       = uncurry AntiMsg <$> anti True <* ws

indentV    :: P (Message V)
indentV     = Indent <$> intagV "indent" parseV

quoteV     :: P (Message V)
quoteV      = Quote <$> intagV "qq" parseV

listV      :: P (Message V)
listV       = Stack Numbered <$> intagV "ol" items
          <|> Stack Bulleted <$> intagV "ul" items
  where items = many1skip parse1V (btag "li" *> ws)

tableV     :: P (Message V)
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
                  <|> mzero

