module Parser (
  P, parse,
  parseProg, parseDecls, parseDecl,
    parseMod, parseTyDec, parseType, parseExpr, parsePatt,
  pp, pds, pd, pm, ptd, pt, pe, px
) where

import Util
import Prec
import Syntax
import Lexer

import Text.ParserCombinators.Parsec
import System.IO.Unsafe (unsafePerformIO)

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

chainl1last :: P a -> P (a -> a -> a) -> P a -> P a
chainl1last each sep final = start where
    start  = each >>= loop
    loop a = option a $ do
               build <- sep
               choice
                 [ each >>= loop . build a,
                   final >>= return . build a ]

chainr1last :: P a -> P (a -> a -> a) -> P a -> P a
chainr1last each sep final = start where
    start  = do
      a       <- each
      builder <- loop
      return (builder a)
    loop   = option id $ do
               build <- sep
               choice
                 [ do
                     b       <- each
                     builder <- loop
                     return (\a -> a `build` builder b),
                   do
                     b       <- final
                     return (\a -> a `build` b) ]

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

typep  :: Language w => P (Type () w)
typep   = typepP 0

typepP :: Language w => Int -> P (Type () w)
typepP 0 = choice
           [ do reserved "all"
                tvs <- many tyvarp
                dot
                t   <- typepP 0
                return (foldr TyAll t tvs),
             do reserved "mu"
                tv  <- tyvarp
                dot
                t   <- typepP 0
                return (TyMu tv t),
             typepP 5 ]
typepP 1 = typepP 2
typepP 2 = typepP 3
typepP 3 = typepP 4
typepP 4 = typepP 5
typepP 5 = chainr1last (typepP 6) tyop5 (typepP 0) where
             tyop5 = choice [
                       arrow >> return tyArr,
                       lolli >> return tyLol
                     ]
typepP 6 = chainl1last (typepP 7) tyop6 (typepP 0) where
             tyop6 = star >> return tyTuple
typepP 7 = tyarg >>= tyapp'
  where
  -- This uses ScopedTypeVariables to reify the Language type:
  tyarg :: Language w => P [Type () w]
  tyarg  = choice
           [ do args <- parens $ commaSep1 (typepP 0)
                return args,
             do tv   <- tyvarp
                return [TyVar tv],
             do tc   <- lidp
                return [TyCon tc [] ()],
             do t <- braces (langMapType (typepP 0))
                return [t] ]

  tyapp' :: [Type () w] -> P (Type () w)
  tyapp' [t] = option t $ do
                 tc <- lidp
                 tyapp' [TyCon tc [t] ()]
  tyapp' ts  = do
                 tc <- lidp
                 tyapp' [TyCon tc ts ()]
typepP _ = typepP 0

progp :: P (Prog ())
progp  = choice [
           do ds <- declsp
              when (null ds) pzero
              e  <- optionMaybe (reserved "in" >> exprp)
              return (Prog ds e),
           exprp >>! (Prog [] . Just)
         ]

declsp :: P [Decl ()]
declsp  = choice [
            do
              d  <- declp
              ds <- declsp
              return (d : ds),
            do
              sharpLoad
              file <- stringLiteral
              let contents = unsafePerformIO (readFile file)
              ds <- case parse parseProg file contents of
                Left e   -> fail (show e)
                Right p  -> return (prog2decls p)
              ds' <- declsp
              return (ds ++ ds'),
            return []
          ]

declp :: P (Decl ())
declp  = choice [
           tyDecp >>! DcTyp,
           modp   >>! DcMod,
           do
             reserved "abstype"
             lang <- brackets languagep
             at   <- abstyp lang
             reserved "with"
             ds <- declsp
             reserved "end"
             return (DcAbs at ds)
         ]

tyDecp :: P TyDec
tyDecp  = do
  reserved "type"
  lang   <- brackets languagep
  case lang of
    LC -> do
      tvs  <- paramsp
      name <- lidp
      choice [
        do
          reservedOp "="
          choice [
            altsp >>! TdDatC name tvs,
            typep >>! TdSynC name tvs ],
        do
          return (TdAbsC name tvs) ]
    LA -> do
      (arity, tvs) <- paramsVp
      name         <- lidp
      choice [
        do
          unless (all (== Invariant) arity) pzero
          reservedOp "="
          choice [
            altsp >>! TdDatA name tvs,
            typep >>! TdSynA name tvs ],
        do
          quals <- qualsp
          return (TdAbsA name tvs arity quals) ]

modp :: P (Mod ())
modp  = choice
  [ do lang <- try $ do
         optional (reserved "let")
         brackets languagep
       case lang of
         LC -> modbodyp MdC
         LA -> modbodyp MdA,
    do try $ do
         reserved "let"
         reserved "interface"
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
    modbodyp build = do
      f <- varp
      (fixt, fixe) <- afargsp
      t <- optionMaybe $ colon >> typep
      reservedOp "="
      e <- exprp
      return (build f (fmap fixt t) (fixe e))

abstyp :: Lang -> P AbsTy
abstyp LC = do
  tvs  <- paramsp
  name <- lidp
  reservedOp "="
  alts <- altsp
  return (AbsTyC name tvs alts)
abstyp LA = do
  (arity, tvs) <- paramsVp
  name         <- lidp
  quals        <- qualsp
  reservedOp "="
  alts         <- altsp
  return (AbsTyA name tvs arity quals alts)

paramsp  :: P [TyVar]
paramsp   = delimList (return ()) parens comma tyvarp

paramsVp :: P ([Variance], [TyVar])
paramsVp  = delimList (return ()) parens comma paramVp >>! unzip

qualsp   :: P [Either TyVar Q]
qualsp    = delimList (reserved "qualifier") parens (symbol "\\/") qualp

paramVp :: P (Variance, TyVar)
paramVp = do
  v  <- variancep
  tv <- tyvarp
  return (v, tv)

variancep :: P Variance
variancep = choice
  [ char '+' >> return Covariant,
    char '-' >> return Contravariant,
    char '0' >> return Omnivariant,
    char '1' >> return Invariant,
    return Invariant ]

qualp :: P (Either TyVar Q)
qualp = choice
  [ litqualp >>! Right,
    tyvarp   >>! Left ]

litqualp :: P Q
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
                  (ft, fe) <- afargsp
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
      do reserved "fun"
         build <- choice
           [ argsp1,
             do x  <- pattp
                colon
                t  <- typepP (precArr + 1)
                return (exAbs x t) ]
         arrow
         expr0 >>! build,
      expr1 ]
  expr1 = do e1 <- expr3
             choice
               [ do semi
                    e2 <- expr0
                    return (exSeq e1 e2),
                 return e1 ]
  expr3 = chainl1last expr4 (opappp (Left 3))  expr0
  expr4 = chainr1last expr5 (opappp (Right 4)) expr0
  expr5 = chainl1last expr6 (opappp (Left 5))  expr0
  expr6 = chainl1last expr7 (opappp (Left 6))  expr0
  expr7 = chainr1last expr8 (opappp (Right 7)) expr0
  expr8 = expr9
  expr9 = chainl1 expr10 (return exApp)
  expr10 = do
    ops <- many (oplevelp (Right 10))
    arg <- expr11
    return (foldr (\op arg' -> exVar op `exApp` arg') arg ops)
  expr11 = do
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

afargsp :: Language w =>
           P (Type () w -> Type () w, Expr () w -> Expr () w)
afargsp = loop tyArr where
  loop arr0 = choice
    [ do (tvt, tve) <- tyargp
         (ft, fe) <- loop arr0
         return (tvt . ft, tve . fe),
      do arr <- option arr0 $ do
           reservedOp "|"
           return tyLol
         (ft,  fe)  <- vargp arr
         (fts, fes) <- loop arr
         return (ft . fts, fe . fes),
      return (id, id) ]

argsp1 :: Language w => P (Expr () w -> Expr () w)
argsp1  = foldr (.) id `fmap` many1 argp

argsp :: Language w => P (Expr () w -> Expr () w)
argsp  = foldr (.) id `fmap` many argp

argp :: Language w => P (Expr () w -> Expr () w)
argp  = (tyargp <|> vargp const) >>! snd

vargp :: Language w =>
         (Type () w -> Type () w -> Type () w) ->
         P (Type () w -> Type () w, Expr () w -> Expr () w)
vargp arr = parens $ choice
              [ do
                  x <- pattp
                  reservedOp ":"
                  t <- typep
                  return (arr t, exAbs x t),
               return (arr tyUnit, exAbs PaWild tyUnit) ]
  where tyUnit = tyGround "unit"

tyargp :: Language w =>
          P (Type () w -> Type () w, Expr () w -> Expr () w)
tyargp  = do
  tvs <- liftM return tyvarp <|> brackets (commaSep1 tyvarp)
  return (\t -> foldr TyAll t tvs, \e -> foldr exTAbs e tvs)

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
parseTyDec    :: P TyDec
parseType     :: Language w => P (Type () w)
parseExpr     :: Language w => P (Expr () w)
parsePatt     :: P Patt
parseProg      = finish progp
parseDecls     = finish declsp
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

ptd :: String -> TyDec
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

