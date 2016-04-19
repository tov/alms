-- | Lexer setup for parsec
module Syntax.Lexer (
  -- * Class for saving pre-whitespace position
  T.TokenEnd(..),
  -- * Identifier tokens
  isUpperIdentifier, lid, uid,
  llabel, ulabel,

  -- * Operators
  opP,
  cons, semis, bang, star,
  pragma,
  lolli, arrow, funbraces, plusbraces,
  lambda, forall, exists, mu,
  qualbox,
  qualU, qualA, qjoin, qjoinArr, ellipsis,
  variantInj, variantEmb,
  sigilU, sigilA,
  markCovariant, markContravariant, markInvariant, markOmnivariant,
  markQVariant,

  -- * Token parsers from Parsec
  identifier, reserved, operator, reservedOp, charLiteral,
  stringLiteral, natural, integer, integerOrFloat, float,
  naturalOrFloat, decimal, hexadecimal, octal, symbol, lexeme,
  whiteSpace, parens, braces, angles, brackets, squares, semi, comma,
  colon, dot, semiSep, semiSep1, commaSep, commaSep1
) where

import Syntax.Prec
import Util
import Alt.Parsec
import qualified Alt.Token as T

import Prelude ()
import Data.Char
import qualified Data.List as List

type CharParser st a = Parsec String st a

tok :: T.TokenEnd st => T.TokenParser st
tok = T.makeTokenParser T.LanguageDef {
    T.commentStart   = "(*",
    T.commentEnd     = "*)",
    T.commentLine    = "--",
    T.nestedComments = True,
    T.identStart     = noλμ $ upper <|> lower <|> oneOf "_",
    T.identLetter    = alphaNum <|> oneOf "_'′₀₁₂₃₄₅₆₇₈₉⁰¹²³⁴⁵⁶⁷⁸⁹ᵢⱼₐₑₒₓⁱⁿ",
    T.opStart        = satisfy isOpStart <|> plusNoBrace,
    T.opLetter       = satisfy isOpLetter <|> plusNoBrace,
    T.reservedNames  = ["fun", "λ", "function",
                        "if", "then", "else",
                        "match", "with", "as", "_",
                        "try",
                        "local", "open", "exception",
                        "let", "rec", "and", "in",
                        "interface", "abstype", "end",
                        "module", "struct",
                        "sig", "val", "include",
                        "all", "ex", "mu", "μ", "of",
                        "type", "qualifier" ],
    T.reservedOpNames = ["|", "=", ":", ":>", "->", "→", "⊸",
                         "∀", "∃", "⋁", "\\/", "...", "…", "::", "∷",
                         "&&", "||" ],
    T.caseSensitive = True
  }
  -- 'λ' is not an identifier character, so that we can use it as
  -- a reserved operator. Otherwise, we'd need a space after it.
  where noλμ p      = notFollowedBy (char 'λ' <|> char 'μ') *> p
        plusNoBrace = char '+' <* notFollowedBy (char '}')

isOpStart, isOpLetter :: Char -> Bool
isOpStart c
  | isAscii c = c `elem` "!$%&*-/<=>?@^|~"
  | otherwise = case generalCategory c of
      ConnectorPunctuation  -> True
      DashPunctuation       -> True
      OtherPunctuation      -> True
      MathSymbol            -> True
      CurrencySymbol        -> True
      OtherSymbol           -> True
      ModifierSymbol        -> True
      OpenPunctuation       -> True
      ClosePunctuation      -> True
      _                     -> False
isOpLetter c
  | isAscii c = c `elem` "!$%&*-/<=>?@^|~.:"
  | otherwise = case generalCategory c of
      ConnectorPunctuation  -> True
      DashPunctuation       -> True
      OtherPunctuation      -> True
      MathSymbol            -> True
      CurrencySymbol        -> True
      OtherSymbol           -> True
      ModifierSymbol        -> True
      OpenPunctuation       -> True
      ClosePunctuation      -> True
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

-- | Parse a pragma or a prefix thereof
pragma          :: T.TokenEnd st ⇒ String → CharParser st ()
pragma name      = try $ do
  char '#'
  s ← lid
  guard (s `List.isPrefixOf` name)

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
funbraceLeft     = () <$ symbol "-"

-- | The right part of the $-_>$ operator
funbraceRight   :: T.TokenEnd st => CharParser st ()
funbraceRight    = () <$ symbol ">"

-- | The left part of the $-[_]>$ operator
oldFunbraceLeft    :: T.TokenEnd st => CharParser st ()
oldFunbraceLeft     = () <$ try (symbol "-[")

-- | The right part of the $-[_]>$ operator
oldFunbraceRight   :: T.TokenEnd st => CharParser st ()
oldFunbraceRight    = () <$ try (symbol "]>")

funbraces       :: T.TokenEnd st => CharParser st a -> CharParser st a
funbraces        = liftM2 (<|>) (between oldFunbraceLeft oldFunbraceRight)
                                (between funbraceLeft funbraceRight)

-- | Curly braces with + symbols
plusbraces      :: T.TokenEnd st => CharParser st a -> CharParser st a
plusbraces       = between (try (symbol "{+")) (try (symbol "+}"))

-- | The left part of the $|[_]$ annotation
qualboxLeft     :: T.TokenEnd st => CharParser st ()
qualboxLeft      = () <$ try (symbol "|[")

-- | The right part of the $|[_]$ annotation
qualboxRight    :: T.TokenEnd st => CharParser st ()
qualboxRight     = () <$ symbol "]"

qualbox         :: T.TokenEnd st => CharParser st a -> CharParser st a
qualbox          = between qualboxLeft qualboxRight

-- | The function keyword
lambda          :: T.TokenEnd st => CharParser st ()
lambda           = reserved "fun" <|> reservedOp "λ"

-- | The universal quantifier keyword
forall          :: T.TokenEnd st => CharParser st ()
forall           = reserved "all" <|> reservedOp "∀"

-- | The existential quantifier keyword
exists          :: T.TokenEnd st => CharParser st ()
exists           = reserved "ex" <|> reservedOp "∃"

-- | The recursive type binder
mu              :: T.TokenEnd st => CharParser st ()
mu               = reserved "mu" <|> reservedOp "μ"

-- | The list constructor
cons            :: T.TokenEnd st => CharParser st ()
cons             = reservedOp "::" <|> reservedOp "∷"

-- | @;@, @;;@, ...
semis           :: T.TokenEnd st => CharParser st String
semis            = lexeme (many1 (char ';'))

-- | @*@, which gets special treatment for unicode
star            :: T.TokenEnd st => CharParser st String
star             = symbol "*" <|> symbol "×"

-- | Qualifier @U@ (not reserved)
qualU    :: T.TokenEnd st => CharParser st ()
qualU     = reserved "U"
-- | Qualifier @A@ (not reserved)
qualA    :: T.TokenEnd st => CharParser st ()
qualA     = reserved "A"

-- | Infix operator for qualifier disjunction
qjoin           :: T.TokenEnd st => CharParser st String
qjoin            = "\\/" <$ (reservedOp "\\/" <|> reservedOp "⋁")

-- | Infix operator for qualifier disjunction in type arrows
qjoinArr        :: T.TokenEnd st => CharParser st ()
qjoinArr         = reservedOp "," <|> reservedOp "\\/" <|> reservedOp "⋁"

-- | Postfix ellipsis type operator
ellipsis        :: T.TokenEnd st => CharParser st ()
ellipsis         = () <$ (reservedOp "..." <|> reservedOp "…")

-- | Marker for open variant injection
variantInj      :: T.TokenEnd st => CharParser st ()
variantInj       = () <$ symbol "`"

-- | Marker for open variant embedding
variantEmb      :: T.TokenEnd st => CharParser st ()
variantEmb       = () <$ symbol "#"

-- | Marker for unlimited type variables
sigilU   :: T.TokenEnd st => CharParser st ()
sigilU    = () <$ symbol "'"

-- | Marker for affine type variables
sigilA   :: T.TokenEnd st => CharParser st ()
sigilA    = () <$ symbol "`"

markCovariant, markContravariant, markInvariant, markOmnivariant,
  markQVariant :: T.TokenEnd st => CharParser st ()

markCovariant        = () <$ symbol "+"
markContravariant    = () <$ symbol "-"
markInvariant        = () <$ symbol "="
markOmnivariant      = () <$ symbol "0"
markQVariant         = () <$ symbol "Q"

-- | Is the string an uppercase identifier?  (Special case: @true@ and
--   @false@ are consider uppercase.)
isUpperIdentifier :: String -> Bool
isUpperIdentifier "true"  = True
isUpperIdentifier "false" = True
isUpperIdentifier "()"    = True
isUpperIdentifier "[]"    = True
isUpperIdentifier "::"    = True
isUpperIdentifier (c:_)   = isUpper c
isUpperIdentifier _       = False

-- | Lex a lowercase identifer
lid        :: T.TokenEnd st => CharParser st String
lid              = try $ do
  s <- identifier
  if isUpperIdentifier s
    then mzero <?> "lowercase identifier"
    else return s

-- | Lex an uppercase identifer
uid        :: T.TokenEnd st => CharParser st String
uid              = try $ do
  s <- identifier <|> symbol "()" <|> symbol "[]"
  if isUpperIdentifier s
    then return s
    else mzero <?> "uppercase identifier"

-- | Lex a record label
llabel     :: T.TokenEnd st => CharParser st String
llabel           = try $ do
  c:s <- identifier
  if isLower c
    then return (toUpper c : s)
    else mzero <?> "record field label"

-- | Lex a variant label
ulabel     :: T.TokenEnd st => CharParser st String
ulabel           = try $ do
  s@(c:_) <- identifier
  if isUpper c
    then return s
    else mzero <?> "variant constructor label"

-- | Accept an operator having the specified precedence
opP :: T.TokenEnd st => Prec -> CharParser st String
opP p = try $ do
  op <- operator
  if precOp op == p
    then return op
    else mzero

