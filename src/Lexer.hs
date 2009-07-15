module Lexer (
  identifier, reserved, operator, reservedOp, charLiteral, stringLiteral,
  natural, integer, float, naturalOrFloat, decimal, hexadecimal, octal,
  symbol, lexeme, whiteSpace, parens, braces, angles, brackets, squares,
  semi, comma, colon, dot, semiSep, semiSep1, commaSep, commaSep1,

  isUpperIdentifier, lid, uid,
  sharpLoad,
  lolli, arrow, star,
  qualU, qualA, langC, langA,
  opP
) where

import Util
import Prec

import Data.Char (isUpper)
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as T

tok :: T.TokenParser st
tok = T.makeTokenParser T.LanguageDef {
    T.commentStart   = "(*",
    T.commentEnd     = "*)",
    T.commentLine    = "--",
    T.nestedComments = True,
    T.identStart     = upper <|> lower <|> oneOf "_",
    T.identLetter    = alphaNum <|> oneOf "_'",
    T.opStart        = oneOf "!$%&*+-/<=>?@^|~",
    T.opLetter       = oneOf "!$%&*+-/<=>?@^|~.:",
    T.reservedNames  = ["fun",
                        "if", "then", "else",
                        "match", "with", "as", "_",
                        "let", "rec", "and", "in",
                        "interface", "abstype", "end",
                        "all", "mu", "of",
                        "type", "qualifier"],
    T.reservedOpNames = ["|", "=", ":", ":>", "->"],
    T.caseSensitive = True
  }

identifier      :: CharParser st String
identifier       = T.identifier tok
reserved        :: String -> CharParser st ()
reserved         = T.reserved tok
operator        :: CharParser st String
operator         = T.operator tok
reservedOp      :: String -> CharParser st ()
reservedOp       = T.reservedOp tok
charLiteral     :: CharParser st Char
charLiteral      = T.charLiteral tok
stringLiteral   :: CharParser st String
stringLiteral    = T.stringLiteral tok
natural         :: CharParser st Integer
natural          = T.natural tok
integer         :: CharParser st Integer
integer          = lexeme $ try $ do
  sign <- choice [
            char '+' >> return id,
            char '-' >> return negate,
            return id
          ]
  nat  <- natural
  return (sign nat)
float           :: CharParser st Double
float            = T.float tok
naturalOrFloat  :: CharParser st (Either Integer Double)
naturalOrFloat   = T.naturalOrFloat tok
decimal         :: CharParser st Integer
decimal          = T.decimal tok
hexadecimal     :: CharParser st Integer
hexadecimal      = T.hexadecimal tok
octal           :: CharParser st Integer
octal            = T.octal tok
symbol          :: String -> CharParser st String
symbol           = T.symbol tok
lexeme          :: CharParser st a -> CharParser st a
lexeme           = T.lexeme tok
whiteSpace      :: CharParser st ()
whiteSpace       = T.whiteSpace tok
parens          :: CharParser st a -> CharParser st a
parens           = T.parens tok
braces          :: CharParser st a -> CharParser st a
braces           = T.braces tok
angles          :: CharParser st a -> CharParser st a
angles           = T.angles tok
brackets        :: CharParser st a -> CharParser st a
brackets         = T.brackets tok
squares         :: CharParser st a -> CharParser st a
squares          = T.squares tok
semi            :: CharParser st String
semi             = T.semi tok
comma           :: CharParser st String
comma            = T.comma tok
colon           :: CharParser st String
colon            = T.colon tok
dot             :: CharParser st String
dot              = T.dot tok
semiSep         :: CharParser st a -> CharParser st [a]
semiSep          = T.semiSep tok
semiSep1        :: CharParser st a -> CharParser st [a]
semiSep1         = T.semiSep1 tok
commaSep        :: CharParser st a -> CharParser st [a]
commaSep         = T.commaSep tok
commaSep1       :: CharParser st a -> CharParser st [a]
commaSep1        = T.commaSep1 tok

sharpLoad       :: CharParser st ()
sharpLoad        = try (symbol "#load") >> return ()

lolli           :: CharParser st ()
lolli            = try (symbol "-o") >> return ()

arrow           :: CharParser st ()
arrow            = try (symbol "->") >> return ()

star            :: CharParser st ()
star             = symbol "*" >> return ()

qualU, qualA    :: CharParser st ()
qualU            = symbol "U" >> return ()
qualA            = symbol "A" >> return ()

langC, langA    :: CharParser st ()
langC            = symbol "C" >> return ()
langA            = symbol "A" >> return ()

isUpperIdentifier :: String -> Bool
isUpperIdentifier "true"  = True
isUpperIdentifier "false" = True
isUpperIdentifier (c:_)   = isUpper c
isUpperIdentifier _       = False

lid, uid        :: CharParser st String
lid              = try $ do
  s <- identifier
  if isUpperIdentifier s
    then pzero <?> "lowercase identifier"
    else return s
uid              = try $ do
  s <- identifier
  if isUpperIdentifier s
    then return s
    else pzero <?> "uppercase identifier"

opP :: Prec -> CharParser st String
opP p = try $ do
  op <- operator
  if precOp op == p
    then return op
    else pzero

