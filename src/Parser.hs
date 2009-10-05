{-# LANGUAGE RelaxedPolyRec #-}
module Parser (
  P, parse,
  parseProg, parseDecls, parseDecl,
    parseLet, parseTyDec, parseType, parseExpr, parsePatt,
  pp, pds, pd, pl, ptd, pt, pe, px
) where

import Util
import Prec
import Syntax
import Loc
import Lexer

import Text.ParserCombinators.Parsec hiding (parse)
import System.IO.Unsafe (unsafePerformIO)
import System.FilePath ((</>), dropFileName)

data Lang = LC | LA deriving (Eq, Show, Ord)
type St   = Maybe Lang
type P a  = CharParser St a

(>>!) :: P a -> (a -> b) -> P b
(>>!)  = flip fmap

parse   :: P a -> SourceName -> String -> Either ParseError a
parse p  = runParser p Nothing

withState :: St -> P a -> P a
withState st p = do
  st0 <- getState
  setState st
  r <- p
  setState st0
  return r

curLoc :: P Loc
curLoc  = getPosition >>! fromSourcePos

addLoc :: Relocatable a => P a -> P a
addLoc p = do
  loc <- curLoc
  a   <- p
  return (a <<@ loc)

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

-- Just uppercase identifiers
uidp :: P Uid
uidp  = uid >>! Uid

-- Just lowercase identifiers
lidp :: P Lid
lidp  = lid >>! Lid

-- Just operators
operatorp :: P Lid
operatorp  = try (parens operator) >>! Lid

-- Add a path before something
pathp :: P ([Uid] -> b) -> P b
pathp p = try $ do
  path <- many $ try $ liftM2 const uidp dot
  make <- p
  return (make path)

-- Qualified uppercase identifiers:
--  - module names occurences
--  - datacons in patterns (though path is ignored)
quidp :: P QUid
quidp  = pathp (uidp >>! flip J)

-- Qualified lowercase identifiers:
--  - tycon ocurences
qlidp :: P QLid
qlidp  = pathp (lidp >>! flip J)

-- Lowercase identifiers and operators
--  - variable bindings
varp :: P Lid
varp  = lidp <|> operatorp

-- Qualified lowercase identifers and operators
--  - variable occurences
qvarp :: P QLid
qvarp  = pathp (varp >>! flip J)

-- Identifier expressions
identp :: P (Expr () w)
identp  = addLoc $ pathp $ choice
  [ do v <- varp
       return $ \path -> exVar (J path v),
    do c <- uidp
       return $ \path -> exCon (J path c) ]

-- Type variables
tyvarp :: P TyVar
tyvarp  = do
  char '\''
  q <- choice
       [ char '<' >> return Qa,
         return Qu ]
  x <- lidp
  return (TV x q)

oplevelp :: Prec -> P Lid
oplevelp  = liftM Lid . opP

typep  :: Language w => P (Type () w)
typep   = typepP 0

typepP :: Language w => Int -> P (Type () w)
typepP 0 = choice
  [ do tc <- choice
         [ reserved "all" >> return tyAll,
           reserved "ex"  >> return tyEx,
           reserved "mu"  >> return TyMu ]
       tvs <- many tyvarp
       dot
       t   <- typepP 0
       return (foldr tc t tvs),
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
             do tc   <- qlidp
                return [TyCon tc [] ()],
             do t <- braces (langMapType (typepP 0))
                return [t] ]

  tyapp' :: [Type () w] -> P (Type () w)
  tyapp' [t] = option t $ do
                 tc <- qlidp
                 tyapp' [TyCon tc [t] ()]
  tyapp' ts  = do
                 tc <- qlidp
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
              base <- sourceName `liftM` getPosition
              path <- inDirectoryOf base `liftM` stringLiteral
              let contents = unsafePerformIO $ readFile path
              ds <- case parse parseProg path contents of
                Left e   -> fail (show e)
                Right p  -> return (prog2decls p)
              ds' <- declsp
              return (ds ++ ds'),
            return []
          ]
  where inDirectoryOf "-"  path = path
        inDirectoryOf base path = dropFileName base </> path

declp :: P (Decl ())
declp  = addLoc $ choice [
           tyDecp  >>! dcTyp,
           letp    >>! dcLet,
           do
             reserved "open"
             modexpp >>! dcOpn,
           do
             reserved "module"
             n <- uidp
             reservedOp "="
             b <- modexpp
             return (dcMod n b),
           do
             reserved "local"
             ds0 <- declsp
             reserved "with"
             ds1 <- declsp
             reserved "end"
             return (dcLoc ds0 ds1),
           enterdecl "abstype" $ \tl lang -> do
             at   <- abstyp tl lang
             reserved "with"
             ds <- declsp
             reserved "end"
             return (dcAbs at ds)
         ]

modexpp :: P (ModExp ())
modexpp  = choice [
             enterdecl "struct" $ \tl lang -> do
               ds <- declsp
               reserved "end"
               return $ case lang of
                 LC -> MeStrC tl ds
                 LA -> MeStrA tl ds,
             quidp >>! MeName
           ]

tyDecp :: P TyDec
tyDecp  =
  enterdecl "type" $ \tl lang ->
  case lang of
    LC -> do
      tds <- sepBy1 tyDecCp (reserved "and")
      return (TyDecC tl tds)
    LA -> do
      tds <- sepBy1 tyDecAp (reserved "and")
      return (TyDecA tl tds)
  where
    tyDecCp = do
      tvs  <- paramsp
      name <- lidp
      choice [
        do
          reservedOp "="
          choice [
            typep >>! TdSynC name tvs,
            altsp >>! TdDatC name tvs ],
        do
          return (TdAbsC name tvs) ]
    tyDecAp = do
      (arity, tvs) <- paramsVp
      name         <- lidp
      choice [
        do
          unless (all (== Invariant) arity) pzero
          reservedOp "="
          choice [
            typep >>! TdSynA name tvs,
            altsp >>! TdDatA name tvs ],
        do
          quals <- qualsp
          return (TdAbsA name tvs arity quals) ]

letp :: P (Let ())
letp  =  do
  reserved "let"
  tl   <- toplevelp
  choice [
    do reserved "interface"
       x    <- varp
       reservedOp ":>"
       t    <- typep
       reservedOp "="
       y    <- qvarp
       return (LtInt tl x t y),
    do lang <- languagep
       withState (Just lang) $
         case lang of
           LC -> letbodyp (LtC tl)
           LA -> letbodyp (LtA tl)
    ]
  where
    letbodyp :: Language w =>
                (Lid -> Maybe (Type () w) -> Expr () w -> Let ()) ->
                P (Let ())
    letbodyp build = do
      f <- varp
      (fixt, fixe) <- afargsp
      t <- optionMaybe $ colon >> typep
      reservedOp "="
      e <- exprp
      return (build f (fmap fixt t) (fixe e))

abstyp :: Bool -> Lang -> P AbsTy
abstyp tl LC = do
  tds <- flip sepBy (reserved "and") $ do
    tvs  <- paramsp
    name <- lidp
    reservedOp "="
    alts <- altsp
    return (TdDatC name tvs alts)
  return (AbsTyC tl tds)
abstyp tl LA = do
  tds <- flip sepBy (reserved "and") $ do
    (arity, tvs) <- paramsVp
    name         <- lidp
    quals        <- qualsp
    reservedOp "="
    alts         <- altsp
    return (arity, quals, TdDatA name tvs alts)
  return (AbsTyA tl tds)

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

toplevelp :: P Bool
toplevelp  = maybe True (const False) `fmap` getState

languagep :: P Lang
languagep  = do
  st <- getState
  case st of
    Nothing   -> brackets $ choice
                 [ do langC; return LC,
                   do langA; return LA ]
    Just lang -> return lang

enterdecl :: String -> (Bool -> Lang -> P a) -> P a
enterdecl name p = do
  reserved name
  tl   <- toplevelp
  lang <- languagep
  withState (Just lang) (p tl lang)

exprp :: Language w => P (Expr () w)
exprp = expr0 where
  expr0 = addLoc $ choice
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
                finishLet (exLet x . args),
             do d    <- declp
                reserved "in"
                e2   <- expr0
                return (exLetDecl d e2) ],
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
           [
             argsp1,
             do
               x  <- pattp
               colon
               t  <- typepP (precArr + 1)
               return (exAbs x t)
           ]
         arrow
         expr0 >>! build,
      expr1 ]
  expr1 = addLoc $ do
            e1 <- expr3
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
  expr9 = choice
            [ chainl1 expr10 (addLoc (return exApp)),
              do
                reserved "Pack"
                t1 <- brackets typep
                parens $ do
                  t2 <- typep
                  comma
                  e  <- exprN1
                  return (exPack t1 t2 e)
                ]
  expr10 = do
    ops <- many $ addLoc $ oplevelp (Right 10) >>! exBVar
    arg <- expr11
    return (foldr exApp arg ops)
  expr11 = do
             e  <- exprA
             ts <- many . brackets $ commaSep1 typep
             return (foldl exTApp e (concat ts))
  exprA = addLoc $ choice
    [ identp,
      integerOrFloat >>! either exInt exFloat,
      charLiteral    >>! (exInt . fromIntegral . fromEnum),
      stringLiteral  >>! exStr,
      parens (exprN1 <|> return (exBCon (Uid "()")))
    ]
  exprN1 = addLoc $ do
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

-- Parse an infix operator at given precedence
opappp :: Prec -> P (Expr () w -> Expr () w -> Expr () w)
opappp p = do
  loc <- curLoc
  op  <- oplevelp p
  return (\e1 e2 -> (exBVar op <<@ loc `exApp` e1) `exApp` e2)

-- Zero or more of (pat:typ, ...), (), or tyvar, recognizing '|'
-- to introduce affine arrows
afargsp :: Language w =>
           P (Type () w -> Type () w, Expr () w -> Expr () w)
afargsp = loop tyArr where
  loop arrcon0 = do
    arrcon <- option arrcon0 $ do
      reservedOp "|"
      return tyLol
    choice
      [ do (tvt, tve) <- tyargp
           (ft, fe) <- loop arrcon
           return (tvt . ft, tve . fe),
        do (ft,  fe)  <- vargp arrcon
           (fts, fes) <- loop arrcon
           return (ft . fts, fe . fes),
        return (id, id) ]

-- One or more of (pat:typ, ...), (), tyvar
argsp1 :: Language w => P (Expr () w -> Expr () w)
argsp1  = foldr (.) id `fmap` many1 argp

-- Zero or more of (pat:typ, ...), (), tyvar
argsp :: Language w => P (Expr () w -> Expr () w)
argsp  = foldr (.) id `fmap` many argp

-- Parse a (pat:typ, ...), (), or tyvar
argp :: Language w => P (Expr () w -> Expr () w)
argp  = (tyargp <|> vargp const) >>! snd

-- Parse a (pat:typ, ...) or () argument
vargp :: Language w =>
         (Type () w -> Type () w -> Type () w) ->
         P (Type () w -> Type () w, Expr () w -> Expr () w)
vargp arrcon = do
  loc    <- curLoc
  (p, t) <- paty
  return (arrcon t, exAbs p t <<@ loc)

-- Parse a (pat:typ, ...) or () argument
paty :: Language w => P (Patt, Type () w)
paty  = do
  (p, mt) <- pamty
  case (p, mt) of
    (_, Just t) -> return (p, t)
    (PaCon (Uid "()") Nothing, Nothing)
                -> return (p, tyGround "unit")
    _           -> pzero <?> ":"

-- Parse a (), (pat:typ, ...) or (pat) argument
pamty :: Language w => P (Patt, Maybe (Type () w))
pamty  = parens $ choice
           [
             do
               (p, mt) <- pamty
               maybe (maybecolon p) (morepts p) mt,
             do
               p <- pattp
               maybecolon p,
             return (PaCon (Uid "()") Nothing, Nothing)
           ]
  where
    maybecolon p = choice
      [
        do
          colon
          t <- typep
          morepts p t,
        moreps p
      ]
    moreps p = do
      ps <- many (comma >> pattp)
      return (foldl PaPair p ps, Nothing)
    morepts p0 t0 = do
      (ps, ts) <- liftM unzip . many $ do
        comma
        choice
          [
            do
              (p, mt) <- pamty
              case mt of
                Just t  -> return (p, t)
                Nothing -> colonType p,
            do
              p <- pattp
              colonType p
          ]
      return (foldl PaPair p0 ps, Just (foldl tyTuple t0 ts))
    colonType p = do
      colon
      t <- typep
      return (p, t)

-- Parse a sequence of one or more tyvar arguments
tyargp :: Language w =>
          P (Type () w -> Type () w, Expr () w -> Expr () w)
tyargp  = do
  tvs <- liftM return loctv <|> brackets (commaSep1 loctv)
  return (\t -> foldr (\(_,   tv) -> tyAll tv) t tvs,
          \e -> foldr (\(loc, tv) -> exTAbs tv <<@ loc) e tvs)
    where
  loctv = liftM2 (,) curLoc tyvarp

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
        reserved "Pack"
        parens $ do
          tv <- tyvarp
          comma
          x  <- pattN1
          return (PaPack tv x),
      do
        J _ u <- quidp
        x     <- optionMaybe (try pattA)
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
parseLet      :: P (Let ())
parseTyDec    :: P TyDec
parseType     :: Language w => P (Type () w)
parseExpr     :: Language w => P (Expr () w)
parsePatt     :: P Patt
parseProg      = finish progp
parseDecls     = finish declsp
parseDecl      = finish declp
parseLet       = finish letp
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

pl  :: String -> Let ()
pl   = makeQaD parseLet

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
  either (error . show) id . parse parser "<string>"
