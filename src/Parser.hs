module Parser (
  P, parse,
  parseProg, parseMods, parseMod, parseType, parseExpr,
  pp, pms, pm, pt, pe
) where

import Syntax

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Token
import Text.ParserCombinators.Parsec.Expr

type St  = ()
type P a = CharParser St a

tok :: TokenParser st
tok = makeTokenParser LanguageDef {
    commentStart   = "(*",
    commentEnd     = "*)",
    commentLine    = "--",
    nestedComments = True,
    identStart     = upper <|> lower <|> oneOf "_",
    identLetter    = alphaNum <|> oneOf "_'",
    opStart        = oneOf "~!@#$%^&*-+=<>/?\\|",
    opLetter       = oneOf "~!@#$%^&*-+=<>/?\\|",
    reservedNames  = ["if", "then", "else",
                      "let", "in",
                      "module", "interface",
                      "all", "A", "C"],
    reservedOpNames = ["->", "*", "=", "\\", "^", ":", ":>"],
    caseSensitive = True
  }

(>>!) :: P a -> (a -> b) -> P b
(>>!)  = flip fmap

varp :: P Var
varp  = identifier tok >>! Var

tyvarp :: P TyVar
tyvarp  = do
  char '\''
  q <- choice
       [ char '<' >> return Qa,
         return Qu ]
  x <- varp
  return (TV x q)

identp :: P (Expr w)
identp  = do
  s <- identifier tok
  if s `elem` constants
    then return (exCon s)
    else return (exVar (Var s))

typep :: Language w => P (Type w)
typep = type0 where
  type0 = choice
          [ do reserved tok "all"
               tvs <- many tyvarp
               dot tok
               t   <- type0
               return (foldr TyAll t tvs),
            type5 ]
  type5 = typeExpr type6
  type6 = tyarg >>= tyapp'

  -- We have sugar for product and arrow types:
  typeExpr :: P (Type w) -> P (Type w)
  typeExpr = buildExpressionParser
    [[ Infix  (reservedOp tok "*"  >> return tyPair) AssocLeft ],
     [ Infix  (reservedOp tok "->" >> return tyArr) AssocRight,
       Infix  (lexeme tok lolli    >> return tyLol) AssocRight ]]
    where lolli = do
                    char '-'
                    char 'o'
                    notFollowedBy (alphaNum <|> oneOf "'_")

  -- This uses ScopedTypeVariables to reify the Language type:
  tyarg :: Language w => P [Type w]
  tyarg  = choice
           [ do args <- parens tok (commaSep1 tok typep)
                return args,
             do tv   <- tyvarp
                return [TyVar tv],
             do tc   <- identifier tok
                return [TyCon tc []],
             do t <- braces tok (langMapType typep)
                return [t] ]

  tyapp' :: [Type w] -> P (Type w)
  tyapp' [t] = option t $ do
                 tc <- identifier tok
                 tyapp' [TyCon tc [t]]
  tyapp' ts  = do
                 tc <- identifier tok
                 tyapp' [TyCon tc ts]

progp :: P Prog
progp  = do
  ms <- choice
          [ do ms <- modsp
               reserved tok "in"
               return ms,
            return [] ]
  e  <- exprp
  return (Prog ms e)

modsp :: P [Mod]
modsp  = many1 modp <|> return []

modp :: P Mod
modp  = choice
  [ do optional (reserved tok "module")
       lang <- squares tok languagep
       case lang of
         'C' -> modbodyp MdC
         _   -> modbodyp MdA,
    do reserved tok "interface"
       x    <- varp
       reservedOp tok ":>"
       t    <- typep
       reservedOp tok "="
       y    <- varp
       return (MdInt x t y) ]
  where
    languagep :: P Char
    languagep  = choice
      [ do reserved tok "C"; return 'C',
        do reserved tok "A"; return 'A' ]
    modbodyp :: Language w => (Var -> Type w -> Expr w -> Mod) -> P Mod
    modbodyp f = do
      x    <- varp
      colon tok
      t    <- typep
      reservedOp tok "="
      e    <- exprp
      return (f x t e)

exprp :: Language w => P (Expr w)
exprp = expr0 where
  expr0 = choice
    [ do reserved tok "let"
         makeLet <- choice
           [ do x    <- varp
                args <- argsp
                return (exLet x . args),
             parens tok $ do
                x  <- varp
                comma tok
                y  <- varp
                return (exLetPair (x, y)) ]
         reservedOp tok "="
         e1 <- expr0
         reserved tok "in"
         e2 <- expr0
         return (makeLet e1 e2),
      do reserved tok "if"
         ec <- expr0
         reserved tok "then"
         et <- expr0
         reserved tok "else"
         ef <- expr0
         return (exIf ec et ef),
      do reservedOp tok "\\" <|> reservedOp tok "^"
         build <- choice
           [ argsp,
             do x  <- varp
                colon tok
                t  <- typep
                return (exAbs x t) ]
         dot tok
         expr0 >>! build,
      expr1 ]
  expr1 = do e1 <- expr9
             choice
               [ do semi tok
                    e2 <- expr0
                    return (exSeq e1 e2),
                 return e1 ]
  expr9 = chainl1 expr10 (return exApp)
  expr10 = do
             e  <- exprA
             ts <- many . squares tok $ commaSep1 tok typep
             return (foldl exTApp e (concat ts))
  exprA = choice
    [ identp,
      integer tok       >>! exInt,
      stringLiteral tok >>! exStr,
      parens tok (exprN1 <|> return (exCon "()"))
    ]
  exprN1 = do
    e1 <- expr0
    choice
      [ do colon tok
           t1 <- typep
           reservedOp tok ":>"
           t2 <- typep
           return (exCast e1 t1 t2),
        do comma tok
           e2 <- expr0
           return (exPair e1 e2),
        return e1]

argsp :: Language w => P (Expr w -> Expr w)
argsp  = foldr (.) id `fmap` many1 argp

argp :: Language w => P (Expr w -> Expr w)
argp  = choice
        [ tyvarp >>! exTAbs,
          parens tok $ do
            x <- varp
            reservedOp tok ":"
            t <- typep
            return (exAbs x t) ]

finish :: CharParser st a -> CharParser st a
finish p = do
  optional (whiteSpace tok)
  r <- p
  eof
  return r

parseProg     :: P Prog
parseMods     :: P [Mod]
parseMod      :: P Mod
parseType     :: Language w => P (Type w)
parseExpr     :: Language w => P (Expr w)
parseProg      = finish progp
parseMods      = finish modsp
parseMod       = finish modp
parseType      = finish typep
parseExpr      = finish exprp

-- Convenience functions for quick-and-dirty parsing:

pp  :: String -> Prog
pp   = makeQaD parseProg

pms :: String -> [Mod]
pms  = makeQaD parseMods

pm  :: String -> Mod
pm   = makeQaD parseMod

pt  :: Language w => String -> Type w
pt   = makeQaD parseType

pe  :: Language w => String -> Expr w
pe   = makeQaD parseExpr

makeQaD :: P a -> String -> a
makeQaD parser =
  either (error . show) id . runParser parser () "<string>"

