module Parser (
  P, parse,
  parseProg, parseDecls, parseDecl,
    parseMod, parseTyDec, parseType, parseExpr, parsePatt,
  pp, pds, pd, pm, ptd, pt, pe, px
) where

import Util
import Syntax
import Lexer

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr

type St  = ()
type P a = CharParser St a

(>>!) :: P a -> (a -> b) -> P b
(>>!)  = flip fmap

delimList :: P pre -> (P [a] -> P [a]) -> P sep -> P a -> P [a]
delimList before around delim each =
  choice [
    before >> choice [
      around (each `sepBy` delim),
      each >>! \x -> [x]
    ],
    return []
  ]

uidp :: P Uid
uidp  = uid >>! Uid

lidp :: P Lid
lidp  = lid >>! Lid

operatorp :: P Lid
operatorp  = try (parens operator) >>! Lid

oplevelp :: Prec -> P Lid
oplevelp  = liftM Lid . opP

varp :: P Lid
varp  = lidp <|> operatorp

tyvarp :: P TyVar
tyvarp  = do
  char '\''
  q <- choice
       [ char '<' >> return Qa,
         return Qu ]
  x <- lidp
  return (TV x q)

identp :: P (Expr () w)
identp  = do
  s <- identifier
  if isUpperIdentifier s
    then return (exCon (Uid s))
    else return (exVar (Lid s))

typep :: Language w => P (Type () w)
typep = type0 where
  type0 = choice
          [ do reserved "all"
               tvs <- many tyvarp
               dot
               t   <- type0
               return (foldr TyAll t tvs),
            do reserved "mu"
               tv  <- tyvarp
               dot
               t   <- type0
               return (TyMu tv t),
            type5 ]
  type5 = typeExpr type6
  type6 = tyarg >>= tyapp'

  -- We have sugar for product and arrow types:
  typeExpr :: P (Type () w) -> P (Type () w)
  typeExpr = buildExpressionParser
    [[ Infix  (star   >> return tyTuple) AssocLeft ],
     [ Infix  (arrow  >> return tyArr)   AssocRight,
       Infix  (lolli  >> return tyLol)   AssocRight ]]

  -- This uses ScopedTypeVariables to reify the Language type:
  tyarg :: Language w => P [Type () w]
  tyarg  = choice
           [ do args <- parens $ commaSep1 typep
                return args,
             do tv   <- tyvarp
                return [TyVar tv],
             do tc   <- lidp
                return [TyCon tc [] ()],
             do t <- braces (langMapType typep)
                return [t] ]

  tyapp' :: [Type () w] -> P (Type () w)
  tyapp' [t] = option t $ do
                 tc <- lidp
                 tyapp' [TyCon tc [t] ()]
  tyapp' ts  = do
                 tc <- lidp
                 tyapp' [TyCon tc ts ()]

progp :: P (Prog ())
progp  = do
  ds <- choice
          [ do ds <- many1 declp
               reserved "in"
               return ds,
            return [] ]
  e  <- exprp
  return (Prog ds e)

declp :: P (Decl ())
declp  = choice [
           tyDecp >>! DcTyp,
           modp   >>! DcMod
         ]

tyDecp :: P (TyDec ())
tyDecp  = do
  reserved "type"
  lang   <- brackets languagep
  params <- delimList (return ()) parens comma paramp
  let variances = map fst params
      tvs       = map snd params
  name   <- lidp
  case lang of
    LC -> choice [
      do
        reservedOp "="
        choice [
          altsp >>! TdDatC name tvs,
          typep >>! TdSynC name tvs ],
      do
        return (TdAbsC name tvs) ]
    LA -> choice [
      do
        reservedOp "="
        choice [
          altsp >>! TdDatA name tvs,
          typep >>! TdSynA name tvs ],
      do
        quals <- delimList (reserved "qualifier") parens (symbol "\\/") qualp
        return (TdAbsA name tvs variances quals) ]
  where
    paramp = do
      v  <- variancep
      tv <- tyvarp
      return (v, tv)
    variancep = choice
      [ char '+' >> return Covariant,
        char '-' >> return Contravariant,
        char '0' >> return Omnivariant,
        char '1' >> return Invariant,
        return Invariant ]
    qualp = choice
      [ litqualp >>! Right,
        tyvarp   >>! Left ]
    litqualp = choice
      [ qualU    >> return Qu,
        qualA    >> return Qa ]
    altsp :: Language w => P [(Uid, Maybe (Type () w))]
    altsp  = sepBy1 altp (reservedOp "|")
    altp  :: Language w => P (Uid, Maybe (Type () w))
    altp   = do
      k <- uidp
      t <- optionMaybe $ do
        reserved "of"
        typep
      return (k, t)

modp :: P (Mod ())
modp  = choice
  [ do optional (reserved "module")
       lang <- brackets languagep
       case lang of
         LC -> modbodyp MdC
         LA -> modbodyp MdA,
    do reserved "interface"
       x    <- varp
       reservedOp ":>"
       t    <- typep
       reservedOp "="
       y    <- varp
       return (MdInt x t y) ]
  where
    modbodyp :: Language w =>
                (Lid -> Maybe (Type () w) -> Expr () w -> Mod ()) ->
                P (Mod ())
    modbodyp f = do
      x    <- varp
      t    <- optionMaybe $ colon >> typep
      reservedOp "="
      e    <- exprp
      return (f x t e)

data Lang = LC | LA deriving (Eq, Show, Ord)
languagep :: P Lang
languagep  = choice
  [ do langC; return LC,
    do langA; return LA ]

exprp :: Language w => P (Expr () w)
exprp = expr0 where
  expr0 = choice
    [ do reserved "let"
         let finishLet makeLet = do
               reservedOp "="
               e1 <- expr0
               reserved "in"
               e2 <- expr0
               return (makeLet e1 e2)
         choice
           [ do reserved "rec"
                bs <- flip sepBy1 (reserved "and") $ do
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
                               reservedOp "|"
                               return tyLol
                             (y, t) <- parens $ do
                               y <- pattp
                               colon
                               t <- typep
                               return (y, t)
                             (ft, fe) <- argsloop arr
                             return (arr t . ft, exAbs y t . fe),
                          return (id, id) ]
                  (ft, fe) <- argsloop tyArr
                  colon
                  t    <- typep
                  reservedOp "="
                  e    <- expr0
                  return (Binding x (ft t) (fe e))
                reserved "in"
                e2 <- expr0
                return (exLetRec bs e2),
             do x    <- pattp
                args <- argsp
                finishLet (exLet x . args) ],
      do reserved "if"
         ec <- expr0
         reserved "then"
         et <- expr0
         reserved "else"
         ef <- expr0
         return (exCase ec [(PaCon (Uid "true")  Nothing, et),
                            (PaCon (Uid "false") Nothing, ef)]),
      do reserved "match"
         e1 <- expr0
         reserved "with"
         optional (reservedOp "|")
         clauses <- flip sepBy1 (reservedOp "|") $ do
           xi <- pattp
           reservedOp "->"
           ei <- expr0
           return (xi, ei)
         return (exCase e1 clauses),
      do reservedOp "\\" <|> reservedOp "^"
         build <- choice
           [ argsp1,
             do x  <- pattp
                colon
                t  <- typep
                return (exAbs x t) ]
         dot
         expr0 >>! build,
      expr1 ]
  expr1 = do e1 <- expr3
             choice
               [ do semi
                    e2 <- expr0
                    return (exSeq e1 e2),
                 return e1 ]
  expr3 = chainl1 expr4 (opappp (Left 3))
  expr4 = chainr1 expr5 (opappp (Right 4))
  expr5 = chainl1 expr6 (opappp (Left 5))
  expr6 = chainl1 expr7 (opappp (Left 6))
  expr7 = chainr1 expr8 (opappp (Right 7))
  expr8 = do
    ops <- many (oplevelp (Right 8))
    arg <- expr9
    return (foldr (\op arg' -> exVar op `exApp` arg') arg ops)
  expr9 = chainl1 expr10 (return exApp)
  expr10 = do
             e  <- exprA
             ts <- many . brackets $ commaSep1 typep
             return (foldl exTApp e (concat ts))
  exprA = choice
    [ identp,
      integer       >>! exInt,
      charLiteral   >>! (exInt . fromIntegral . fromEnum),
      stringLiteral >>! exStr,
      operatorp     >>! exVar,
      parens (exprN1 <|> return (exCon (Uid "()")))
    ]
  exprN1 = do
    e1 <- expr0
    choice
      [ do colon
           t1 <- typep
           reservedOp ":>"
           t2 <- typep
           return (exCast e1 t1 t2),
        do comma
           es <- commaSep1 expr0
           return (foldl exPair e1 es),
        return e1 ]

opappp :: Prec -> P (Expr () w -> Expr () w -> Expr () w)
opappp p = do
  op <- oplevelp p
  return (\e1 e2 -> (exVar op `exApp` e1) `exApp` e2)

argsp1 :: Language w => P (Expr () w -> Expr () w)
argsp1  = foldr (.) id `fmap` many1 argp

argsp :: Language w => P (Expr () w -> Expr () w)
argsp  = foldr (.) id `fmap` many argp

argp :: Language w => P (Expr () w -> Expr () w)
argp  = choice
        [ tyvarp >>! exTAbs,
          parens $ do
            x <- pattp
            reservedOp ":"
            t <- typep
            return (exAbs x t) ]

pattp :: P Patt
pattp  = patt0 where
  patt0 = do
    x <- patt9
    choice
      [ do
          reserved "as"
          y <- varp
          return (PaAs x y),
        return x
      ]
  patt9 = choice
    [ do
        u <- uidp
        x <- optionMaybe (try pattA)
        return (PaCon u x),
      pattA ]
  pattA = choice
    [ reserved "_"  >>  return PaWild,
      varp          >>! PaVar,
      integer       >>! PaInt,
      charLiteral   >>! (PaInt . fromIntegral . fromEnum),
      stringLiteral >>! PaStr,
      parens pattN1
    ]
  pattN1 = do
    xs <- commaSep patt0
    case xs of
      []    -> return (PaCon (Uid "()") Nothing)
      x:xs' -> return (foldl PaPair x xs')

finish :: CharParser st a -> CharParser st a
finish p = do
  optional (whiteSpace)
  r <- p
  eof
  return r

parseProg     :: P (Prog ())
parseDecls    :: P [Decl ()]
parseDecl     :: P (Decl ())
parseMod      :: P (Mod ())
parseTyDec    :: P (TyDec ())
parseType     :: Language w => P (Type () w)
parseExpr     :: Language w => P (Expr () w)
parsePatt     :: P Patt
parseProg      = finish progp
parseDecls     = finish (many declp)
parseDecl      = finish declp
parseMod       = finish modp
parseTyDec     = finish tyDecp
parseType      = finish typep
parseExpr      = finish exprp
parsePatt      = finish pattp

-- Convenience functions for quick-and-dirty parsing:

pp  :: String -> Prog ()
pp   = makeQaD parseProg

pds :: String -> [Decl ()]
pds  = makeQaD parseDecls

pd  :: String -> Decl ()
pd   = makeQaD parseDecl

pm  :: String -> Mod ()
pm   = makeQaD parseMod

ptd :: String -> (TyDec ())
ptd  = makeQaD parseTyDec

pt  :: Language w => String -> Type () w
pt   = makeQaD parseType

pe  :: Language w => String -> Expr () w
pe   = makeQaD parseExpr

px  :: String -> Patt
px   = makeQaD parsePatt

makeQaD :: P a -> String -> a
makeQaD parser =
  either (error . show) id . runParser parser () "<string>"

