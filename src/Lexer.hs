-- | Lexer setup for parsec
module Lexer (
  -- * Class for saving pre-whitespace position
  T.TokenEnd(..),
  -- * Identifier tokens
  isUpperIdentifier, lid, uid,

  -- * Operators
  semis, bang, star, slash, plus,
  sharpLoad, sharpInfo, sharpPrec,
  lolli, arrow, funbraces,
  lambda, forall, exists, mu,
  qualbox,
  qualU, qualA, qdisj, qconj,
  opP,

  -- * Token parsers from Parsec
  identifier, reserved, operator, reservedOp, charLiteral,
  stringLiteral, natural, integer, integerOrFloat, float,
  naturalOrFloat, decimal, hexadecimal, octal, symbol, lexeme,
  whiteSpace, parens, braces, angles, brackets, squares, semi, comma,
  colon, dot, semiSep, semiSep1, commaSep, commaSep1
) where

import Prec
import Util

import Data.Char
import Text.ParserCombinators.Parsec
import qualified Token as T

tok :: T.TokenEnd st => T.TokenParser st
tok = T.makeTokenParser T.LanguageDef {
    T.commentStart   = "(*",
    T.commentEnd     = "*)",
    T.commentLine    = "--",
    T.nestedComments = True,
    T.identStart     = upper <|> lower <|> oneOf "_",
    T.identLetter    = alphaNum <|> oneOf "_'",
    T.opStart        = satisfy isOpStart,
    T.opLetter       = satisfy isOpLetter,
    T.reservedNames  = ["fun", "λ",
                        "if", "then", "else",
                        "match", "with", "as", "_",
                        "try",
                        "local", "open", "exception",
                        "let", "rec", "and", "in",
                        "Pack",
                        "interface", "abstype", "end",
                        "module", "struct",
                        "sig", "val", "include",
                        "all", "ex", "mu", "μ", "of",
                        "type", "qualifier"],
    T.reservedOpNames = ["|", "=", ":", ":>", "->", "→", "⊸",
                         "∀", "∃" ],
    T.caseSensitive = True
  }

isOpStart, isOpLetter :: Char -> Bool
isOpStart c
  | isAscii c = c `elem` "!$%&*+-/<=>?@^|~"
  | otherwise = case generalCategory c of
      ConnectorPunctuation  -> True
      DashPunctuation       -> True
      OtherPunctuation      -> True
      MathSymbol            -> True
      CurrencySymbol        -> True
      OtherSymbol           -> True
      _                     -> False
isOpLetter c
  | isAscii c = c `elem` "!$%&*+-/<=>?@^|~.:"
  | otherwise = case generalCategory c of
      ConnectorPunctuation  -> True
      DashPunctuation       -> True
      OtherPunctuation      -> True
      MathSymbol            -> True
      CurrencySymbol        -> True
      OtherSymbol           -> True
      ModifierSymbol        -> True -- not in OpStart
   -- OpenPunctuation
   -- ClosePunctuation
   -- InitialQuote
   -- FinalQuote
      _                     -> False

identifier      :: T.TokenEnd st => CharParser st String
identifier       = T.identifier tok
reserved        :: T.TokenEnd st => String -> CharParser st ()
reserved         = T.reserved tok
operator        :: T.TokenEnd st => CharParser st String
operator         = T.operator tok
reservedOp      :: T.TokenEnd st => String -> CharParser st ()
reservedOp       = T.reservedOp tok
charLiteral     :: T.TokenEnd st => CharParser st Char
charLiteral      = T.charLiteral tok
stringLiteral   :: T.TokenEnd st => CharParser st String
stringLiteral    = T.stringLiteral tok
natural         :: T.TokenEnd st => CharParser st Integer
natural          = T.natural tok
integer         :: T.TokenEnd st => CharParser st Integer
integer          = lexeme $ try $ do
  sign <- choice [
            char '+' >> return id,
            char '-' >> return negate,
            return id
          ]
  nat  <- natural
  return (sign nat)
integerOrFloat  :: T.TokenEnd st => CharParser st (Either Integer Double)
integerOrFloat   = lexeme $ try $ do
  sign <- choice [
            char '+' >> return id,
            char '-' >> return (either (Left . negate) (Right . negate)),
            return id
          ]
  nof  <- naturalOrFloat
  return (sign nof)
 
float           :: T.TokenEnd st => CharParser st Double
float            = T.float tok
naturalOrFloat  :: T.TokenEnd st => CharParser st (Either Integer Double)
naturalOrFloat   = T.naturalOrFloat tok
decimal         :: T.TokenEnd st => CharParser st Integer
decimal          = T.decimal tok
hexadecimal     :: T.TokenEnd st => CharParser st Integer
hexadecimal      = T.hexadecimal tok
octal           :: T.TokenEnd st => CharParser st Integer
octal            = T.octal tok
symbol          :: T.TokenEnd st => String -> CharParser st String
symbol           = T.symbol tok
lexeme          :: T.TokenEnd st => CharParser st a -> CharParser st a
lexeme           = T.lexeme tok
whiteSpace      :: T.TokenEnd st => CharParser st ()
whiteSpace       = T.whiteSpace tok
parens          :: T.TokenEnd st => CharParser st a -> CharParser st a
parens           = T.parens tok
braces          :: T.TokenEnd st => CharParser st a -> CharParser st a
braces           = T.braces tok
angles          :: T.TokenEnd st => CharParser st a -> CharParser st a
angles           = T.angles tok
brackets        :: T.TokenEnd st => CharParser st a -> CharParser st a
brackets         = T.brackets tok
squares         :: T.TokenEnd st => CharParser st a -> CharParser st a
squares          = T.squares tok
semi            :: T.TokenEnd st => CharParser st String
semi             = T.semi tok
comma           :: T.TokenEnd st => CharParser st String
comma            = T.comma tok
colon           :: T.TokenEnd st => CharParser st String
colon            = T.reservedOp tok ":" >> return ":"
dot             :: T.TokenEnd st => CharParser st String
dot              = T.dot tok
semiSep         :: T.TokenEnd st => CharParser st a -> CharParser st [a]
semiSep          = T.semiSep tok
semiSep1        :: T.TokenEnd st => CharParser st a -> CharParser st [a]
semiSep1         = T.semiSep1 tok
commaSep        :: T.TokenEnd st => CharParser st a -> CharParser st [a]
commaSep         = T.commaSep tok
commaSep1       :: T.TokenEnd st => CharParser st a -> CharParser st [a]
commaSep1        = T.commaSep1 tok

-- | The @#load@ pragma
sharpLoad       :: T.TokenEnd st => CharParser st ()
sharpLoad        = reserved "#l" <|> reserved "#load"

-- | The @#info@ pragma
sharpInfo       :: T.TokenEnd st => CharParser st ()
sharpInfo        = reserved "#i" <|> reserved "#info"

-- | The @#prec@ pragma
sharpPrec       :: T.TokenEnd st => CharParser st ()
sharpPrec        = reserved "#p" <|> reserved "#prec"

-- | @!@, which has special meaning in let patterns
bang            :: T.TokenEnd st => CharParser st String
bang             = symbol "!"

-- | The @-o@ type operator, which violates our other lexer rules
lolli           :: T.TokenEnd st => CharParser st ()
lolli            = reserved "-o" <|> reservedOp "⊸"

-- | The @->@ type operator
arrow           :: T.TokenEnd st => CharParser st ()
arrow            = reservedOp "->" <|> reservedOp "→"

-- | The left part of the $-_>$ operator
funbraceLeft    :: T.TokenEnd st => CharParser st ()
funbraceLeft     = try (symbol "-") >> return ()

-- | The right part of the $-_>$ operator
funbraceRight   :: T.TokenEnd st => CharParser st ()
funbraceRight    = try (symbol ">") >> return ()

-- | The left part of the $-[_]>$ operator
oldFunbraceLeft    :: T.TokenEnd st => CharParser st ()
oldFunbraceLeft     = try (symbol "-[") >> return ()

-- | The right part of the $-[_]>$ operator
oldFunbraceRight   :: T.TokenEnd st => CharParser st ()
oldFunbraceRight    = try (symbol "]>") >> return ()

funbraces       :: T.TokenEnd st => CharParser st a -> CharParser st a
funbraces        = liftM2 (<|>) (between oldFunbraceLeft oldFunbraceRight)
                                (between funbraceLeft funbraceRight)

-- | The left part of the $|[_]$ annotation
qualboxLeft     :: T.TokenEnd st => CharParser st ()
qualboxLeft      = try (symbol "|[") >> return ()

-- | The right part of the $|[_]$ annotation
qualboxRight    :: T.TokenEnd st => CharParser st ()
qualboxRight     = try (symbol "]") >> return ()

qualbox         :: T.TokenEnd st => CharParser st a -> CharParser st a
qualbox          = between qualboxLeft qualboxRight

-- | The function keyword
lambda          :: T.TokenEnd st => CharParser st ()
lambda           = reserved "fun" <|> reservedOp "λ" <|> reservedOp "Λ"

-- | The universal quantifier keyword
forall          :: T.TokenEnd st => CharParser st ()
forall           = reserved "all" <|> reservedOp "∀"

-- | The existential quantifier keyword
exists          :: T.TokenEnd st => CharParser st ()
exists           = reserved "ex" <|> reservedOp "∃"

-- | The recursive type binder
mu              :: T.TokenEnd st => CharParser st ()
mu               = reserved "mu" <|> reservedOp "μ"

-- | @;@, @;;@, ...
semis           :: T.TokenEnd st => CharParser st String
semis            = lexeme (many1 (char ';'))

-- | @*@, which is reserved in types but not in expressions
star            :: T.TokenEnd st => CharParser st String
star             = symbol "*" <|> symbol "×"

-- | @/@, which is reserved in types but not in expressions
slash           :: T.TokenEnd st => CharParser st String
slash            = symbol "/"

-- | @+@, which is reserved in types but not in expressions
plus            :: T.TokenEnd st => CharParser st String
plus             = symbol "+"

-- | Qualifier @U@ (not reserved)
qualU    :: T.TokenEnd st => CharParser st ()
qualU     = reserved "U"
-- | Qualifier @A@ (not reserved)
qualA    :: T.TokenEnd st => CharParser st ()
qualA     = reserved "A"

-- | Infix operator for qualifier disjunction
qdisj           :: T.TokenEnd st => CharParser st ()
qdisj            = reservedOp "," <|> reservedOp "\\/" <|> reservedOp "⋁"

-- | Infix operator for qualifier conjunction
qconj           :: T.TokenEnd st => CharParser st ()
qconj            = reservedOp "/\\" <|> reservedOp "⋀"

-- | Is the string an uppercase identifier?  (Special case: @true@ and
--   @false@ are consider uppercase.)
isUpperIdentifier :: String -> Bool
isUpperIdentifier "true"  = True
isUpperIdentifier "false" = True
isUpperIdentifier "()"    = True
isUpperIdentifier (c:_)   = isUpper c
isUpperIdentifier _       = False

-- | Lex a lowercase identifer
lid        :: T.TokenEnd st => CharParser st String
lid              = try $ do
  s <- identifier
  if isUpperIdentifier s
    then pzero <?> "lowercase identifier"
    else return s
-- | Lex an uppercase identifer
uid        :: T.TokenEnd st => CharParser st String
uid              = try $ do
  s <- identifier <|> symbol "()"
  if isUpperIdentifier s
    then return s
    else pzero <?> "uppercase identifier"

-- | Accept an operator having the specified precedence
opP :: T.TokenEnd st => Prec -> CharParser st String
opP p = try $ do
  op <- operator
  if precOp op == p
    then return op
    else pzero

