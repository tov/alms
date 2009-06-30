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
                      "match", "with",
                      "let", "rec", "and", "in",
                      "module", "interface",
                      "all", "A", "C"],
    reservedOpNames = ["|", "->", "*", "=", "\\", "^", ":", ":>"],
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

identp :: P (Expr () w)
identp  = do
  s <- identifier tok
  if s `elem` constants
    then return (exCon s)
    else return (exVar (Var s))

typep :: Language w => P (Type () w)
typep = type0 where
  type0 = choice
          [ do reserved tok "all"
               tvs <- many tyvarp
               dot tok
               t   <- type0
               return (foldr TyAll t tvs),
            do reserved tok "mu"
               tv  <- tyvarp
               dot tok
               t   <- type0
               return (TyMu tv t),
            type5 ]
  type5 = typeExpr type6
  type6 = tyarg >>= tyapp'

  -- We have sugar for product and arrow types:
  typeExpr :: P (Type () w) -> P (Type () w)
  typeExpr = buildExpressionParser
    [[ Infix  (reservedOp tok "*"  >> return tyTuple) AssocLeft ],
     [ Infix  (reservedOp tok "->" >> return tyArr) AssocRight,
       Infix  (lexeme tok lolli    >> return tyLol) AssocRight ]]
    where lolli = do
                    char '-'
                    char 'o'
                    notFollowedBy (alphaNum <|> oneOf "'_")

  -- This uses ScopedTypeVariables to reify the Language type:
  tyarg :: Language w => P [Type () w]
  tyarg  = choice
           [ do args <- parens tok (commaSep1 tok typep)
                return args,
             do tv   <- tyvarp
                return [TyVar tv],
             do tc   <- identifier tok
                return [TyCon tc [] ()],
             do t <- braces tok (langMapType typep)
                return [t] ]

  tyapp' :: [Type () w] -> P (Type () w)
  tyapp' [t] = option t $ do
                 tc <- identifier tok
                 tyapp' [TyCon tc [t] ()]
  tyapp' ts  = do
                 tc <- identifier tok
                 tyapp' [TyCon tc ts ()]

progp :: P (Prog ())
progp  = do
  ms <- choice
          [ do ms <- modsp
               reserved tok "in"
               return ms,
            return [] ]
  e  <- exprp
  return (Prog ms e)

modsp :: P [Mod ()]
modsp  = many1 modp <|> return []

modp :: P (Mod ())
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
    modbodyp :: Language w =>
                (Var -> Maybe (Type () w) -> Expr () w -> Mod ()) ->
                P (Mod ())
    modbodyp f = do
      x    <- varp
      t    <- optionMaybe $ colon tok >> typep
      reservedOp tok "="
      e    <- exprp
      return (f x t e)

exprp :: Language w => P (Expr () w)
exprp = expr0 where
  expr0 = choice
    [ do reserved tok "let"
         let finishLet makeLet = do
               reservedOp tok "="
               e1 <- expr0
               reserved tok "in"
               e2 <- expr0
               return (makeLet e1 e2)
         choice
           [ do reserved tok "rec"
                bs <- flip sepBy1 (reserved tok "and") $ do
                  x    <- varp
                  let argsloop :: Language w =>
                                  (Type () w -> Type () w -> Type () w) ->
                                  P (Type () w -> Type () w,
                                     Expr () w -> Expr () w)
                      argsloop arr0 = choice
                        [ do tv <- tyvarp
                             (ft, fe) <- argsloop arr0
                             return (TyAll tv . ft, exTAbs tv . fe),
                          do arr <- option arr0 $ do
                               reservedOp tok "|"
                               return tyLol
                             (y, t) <- parens tok $ do
                               y <- varp
                               colon tok
                               t <- typep
                               return (y, t)
                             (ft, fe) <- argsloop arr
                             return (arr t . ft, exAbs y t . fe),
                          return (id, id) ]
                  (ft, fe) <- argsloop tyArr
                  colon tok
                  t    <- typep
                  reservedOp tok "="
                  e    <- expr0
                  return (Binding x (ft t) (fe e))
                reserved tok "in"
                e2 <- expr0
                return (exLetRec bs e2),
             do x    <- varp
                args <- argsp
                finishLet (exLet x . args),
             do (x, y) <- parens tok $ do
                  x  <- varp
                  comma tok
                  y  <- varp
                  return (x, y)
                finishLet (exLetPair (x, y)) ],
      do reserved tok "if"
         ec <- expr0
         reserved tok "then"
         et <- expr0
         reserved tok "else"
         ef <- expr0
         return (exIf ec et ef),
      do reserved tok "match"
         e1 <- expr0
         reserved tok "with"
         optional (reservedOp tok "|")
         c2 <- identifier tok
         x2 <- varp
         reservedOp tok "->"
         e2 <- expr0
         reservedOp tok "|"
         c3 <- identifier tok
         x3 <- varp
         reservedOp tok "->"
         e3 <- expr0
         case (c2, c3) of
           ("Left", "Right") -> return $ exCase e1 (x2, e2) (x3, e3)
           ("Right", "Left") -> return $ exCase e1 (x3, e3) (x2, e2)
           _                 -> fail "Unrecognized patterns in match",
      do reservedOp tok "\\" <|> reservedOp tok "^"
         build <- choice
           [ argsp1,
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

argsp1 :: Language w => P (Expr () w -> Expr () w)
argsp1  = foldr (.) id `fmap` many1 argp

argsp :: Language w => P (Expr () w -> Expr () w)
argsp  = foldr (.) id `fmap` many argp

argp :: Language w => P (Expr () w -> Expr () w)
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

parseProg     :: P (Prog ())
parseMods     :: P [Mod ()]
parseMod      :: P (Mod ())
parseType     :: Language w => P (Type () w)
parseExpr     :: Language w => P (Expr () w)
parseProg      = finish progp
parseMods      = finish modsp
parseMod       = finish modp
parseType      = finish typep
parseExpr      = finish exprp

-- Convenience functions for quick-and-dirty parsing:

pp  :: String -> Prog ()
pp   = makeQaD parseProg

pms :: String -> [Mod ()]
pms  = makeQaD parseMods

pm  :: String -> Mod ()
pm   = makeQaD parseMod

pt  :: Language w => String -> Type () w
pt   = makeQaD parseType

pe  :: Language w => String -> Expr () w
pe   = makeQaD parseExpr

makeQaD :: P a -> String -> a
makeQaD parser =
  either (error . show) id . runParser parser () "<string>"

