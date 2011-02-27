{-# LANGUAGE
      PatternGuards,
      ScopedTypeVariables,
      TypeFamilies,
      TypeSynonymInstances #-}
-- | Parser
module Parser (
  -- * The parsing monad
  P, parse,
  -- ** Errors
  ParseError,
  -- ** Quasiquote parsing
  parseQuasi,
  -- ** File and REPL command parsing
  parseFile,
  REPLCommand(..), parseCommand,
  -- ** Parsers
  parseProg, parseRepl, parseDecls, parseDecl, parseModExp,
    parseTyDec, parseAbsTy, parseType, parseTyPat,
    parseQExp, parseExpr, parsePatt,
    parseCaseAlt, parseBinding,
    parseSigExp, parseSigItem,
  -- * Convenience parsers (quick and dirty)
  pp, pds, pd, pme, ptd, pt, ptp, pqe, pe, px
) where

import Util
import Paths
import Prec
import Syntax
import Sigma
import Lexer
import ErrorMessage (AlmsException(..), Phase(ParserPhase))
import qualified Message.AST as Msg

import qualified Data.Map as M
import qualified Data.List as L
import qualified Language.Haskell.TH as TH
import Text.ParserCombinators.Parsec hiding (parse)
import qualified Text.ParserCombinators.Parsec.Error as PE
import System.IO.Unsafe (unsafePerformIO)

data St   = St {
              stSigma :: Bool,
              stAnti  :: Bool,
              stPos   :: SourcePos
            }

instance TokenEnd St where
  saveTokenEnd = do
    pos <- getPosition
    updateState $ \st -> st { stPos = pos }

-- | A 'Parsec' character parser, with abstract state
type P a  = CharParser St a

state0 :: St
state0 = St {
           stSigma = False,
           stAnti  = False,
           stPos   = toSourcePos bogus
         }

-- | Run a parser, given the source file name, on a given string
parse   :: P a -> SourceName -> String -> Either ParseError a
parse p  = runParser p state0

-- | Run a parser on the given string in quasiquote mode
parseQuasi :: String -> (Maybe Char -> Maybe TH.Name -> P a) -> TH.Q a
parseQuasi str p = do
  setter <- TH.location >>! mkSetter
  let parser = do
        setter
        iflag <- optionMaybe (char '+')
        lflag <- choice [
                   do char '@'
                      choice [ char '=' >> identp_no_ws >>! Just,
                               char '!' >> return Nothing ],
                   char '!' >> return Nothing,
                   return (Just "_loc")
                 ]
        p iflag (fmap TH.mkName lflag)
  case runParser parser state0 { stAnti = True } "<quasi>" str of
    Left e  -> fail (show e)
    Right a -> return a
  where
  mkSetter = setPosition . toSourcePos . fromTHLoc

-- | REPL-level commands
data REPLCommand
  = GetInfoCmd [Ident Raw]
  | GetPrecCmd [String]
  | DeclsCmd [Decl Raw]
  | ParseError AlmsException

-- | Parse a line typed into the REPL
parseCommand :: Int -> String -> String -> REPLCommand
parseCommand row line cmd =
  case parseGetInfo line of
    Just ids -> GetInfoCmd ids
    _ -> case parseGetPrec line of
      Just lids -> GetPrecCmd lids
      _ -> case parseInteractive row cmd of
        Right ast -> DeclsCmd ast
        Left err  -> ParseError (almsParseError err)

-- | Given a file name and source, parse it
parseFile :: Id i => String -> String -> Either AlmsException (Prog i)
parseFile  = (almsParseError +++ id) <$$> parse parseProg

almsParseError :: ParseError -> AlmsException
almsParseError e =
  AlmsException ParserPhase (fromSourcePos (errorPos e)) message
  where
    message =
      Msg.Stack Msg.Broken [
        flow ";" messages,
        (if null messages then id else Msg.Indent)
           (Msg.Table (unlist ++ explist))
      ]
    unlist  = case unexpects of
      []  -> []
      s:_ -> [("unexpected:", Msg.Words s)]
    explist = case expects of
      []  -> []
      _   -> [("expected:", flow "," expects)]
    messages  = [ s | PE.Message s     <- PE.errorMessages e, not$null s ]
    unexpects = [ s | PE.UnExpect s    <- PE.errorMessages e, not$null s ]
             ++ [ s | PE.SysUnExpect s <- PE.errorMessages e, not$null s ]
    expects   = [ s | PE.Expect s      <- PE.errorMessages e, not$null s ]
    flow c         = Msg.Flow . map Msg.Words . punct c . L.nub
    punct _ []     = []
    punct _ [s]    = [s]
    punct c (s:ss) = (s++c) : punct c ss

parseGetInfo :: String -> Maybe [Ident Raw]
parseGetInfo = (const Nothing ||| Just) . runParser parser state0 "-"
  where
    parser = finish $
      sharpInfo *>
        many1 (identp
               <|> fmap Var <$> qlidnatp
               <|> J [] . Var . Syntax.lid <$> (operator <|> semis))

parseGetPrec :: String -> Maybe [String]
parseGetPrec = (const Nothing ||| Just) . runParser parser state0 "-"
  where
    parser = finish $
      sharpPrec *>
        many1 (operator <|> semis)

parseInteractive :: Id i => Int -> String -> Either ParseError [Decl i]
parseInteractive line src = parse p "-" src where
  p = do
    pos <- getPosition
    setPosition (pos `setSourceLine` line)
    optional whiteSpace
    r <- replp
    eof
    return r

withSigma :: Bool -> P a -> P a
withSigma = mapSigma . const

mapSigma :: (Bool -> Bool) -> P a -> P a
mapSigma f p = do
  st <- getState
  setState st { stSigma = f (stSigma st) }
  r <- p
  setState st
  return r

getSigma :: P Bool
getSigma  = stSigma `fmap` getState

-- | Get the ending position of the last token, before trailing whitespace
getEndPosition :: P SourcePos
getEndPosition  = stPos <$> getState

-- | Parse something and return the span of its location
withLoc :: P a -> P (a, Loc)
withLoc p = do
  before <- getPosition
  a      <- p
  after  <- getEndPosition
  return (a, fromSourcePosSpan before after)

addLoc :: Relocatable a => P a -> P a
addLoc  = uncurry (<<@) <$$> withLoc

class Nameable a where
  (@@) :: String -> a -> a

infixr 0 @@

instance Relocatable a => Nameable (P a) where
  s @@ p  = addLoc p <?> s

instance Nameable r => Nameable (a -> r) where
  s @@ p  = \x -> s @@ p x

punit :: P ()
punit  = pure ()

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

foldlp :: (a -> b -> a) -> P a -> P b -> P a
foldlp make start follow = foldl make <$> start <*> many follow

-- Antiquote
antip :: AntiDict -> P Anti
antip dict = antilabels . lexeme . try $ do
    char '$' <?> ""
    (s1, s2) <- (,) <$> option "" (try (option "" identp_no_ws <* char ':'))
                    <*> identp_no_ws
    assertAnti
    case M.lookup s1 dict of
      Just _  -> return (Anti s1 s2)
      Nothing -> unexpected $ "antiquote tag: `" ++ s1 ++ "'"
  where
    antilabels p = do
      st <- getState
      if (stAnti st)
        then labels p [ "antiquote `" ++ key ++ "'"
                      | key <- M.keys dict, key /= "" ]
        else p

identp_no_ws :: P String
identp_no_ws = do
  c <- lower <|> char '_'
  cs <- many (alphaNum <|> oneOf "_'")
  return (c:cs)

-- Fail if we should not recognize antiquotes
assertAnti :: P ()
assertAnti = do
  st <- getState
  unless (stAnti st) (unexpected "antiquote")

-- | Parse an antiquote and inject into syntax
antiblep   :: forall a. Antible a => P a
antiblep    = antip (dictOf (undefined::a)) >>! injAnti

antioptp   :: Antible a => P a -> P (Maybe a)
antioptp    = antioptaroundp id

antioptaroundp :: Antible a =>
                  (P (Maybe a) -> P (Maybe a)) ->
                  P a -> P (Maybe a)
antioptaroundp wrap p = wrap present <|> pure Nothing
  where present = antiblep
              <|> Just <$> antiblep
              <|> Just <$> p

antilist1p       :: Antible a => P b -> P a -> P [a]
antilist1p sep p  = antiblep
                <|> sepBy1 (antiblep <|> p) sep

-- Just uppercase identifiers
uidp :: Id i => P (Uid i)
uidp  = Syntax.uid <$> Lexer.uid
    <|> antiblep
  <?> "uppercase identifier"

-- Just lowercase identifiers
lidp :: Id i => P (Lid i)
lidp  = Syntax.lid <$> Lexer.lid
    <|> antiblep
  <?> "lowercase identifier"

-- Lowercase identifiers or naturals
--  - tycon declarations
lidnatp :: Id i => P (Lid i)
lidnatp = Syntax.lid <$> (Lexer.lid <|> show <$> natural)
      <|> operatorp
      <|> Syntax.lid <$> try (parens semis)
      <|> antiblep
  <?> "type name"

-- Just operators
operatorp :: Id i => P (Lid i)
operatorp  = try (parens operator) >>! Syntax.lid
  <?> "operator name"

-- Add a path before something
pathp :: Id i => P ([Uid i] -> b) -> P b
pathp p = try $ do
  path <- many $ try $ uidp <* dot
  make <- p
  return (make path)

-- Qualified uppercase identifiers:
--  - module names occurences
--  - datacons in patterns (though path is ignored)
quidp :: Id i => P (QUid i)
quidp  = pathp (uidp >>! flip J)
     <|> antiblep
  <?> "uppercase identifier"

-- Qualified lowercase identifiers:
--  - module name identifier lists
qlidp :: Id i => P (QLid i)
qlidp  = pathp (lidp >>! flip J)
     <|> antiblep
  <?> "lowercase identifier"

-- Qualified lowercase identifiers or naturals:
--  - tycon occurences
qlidnatp :: Id i => P (QLid i)
qlidnatp  = pathp (lidnatp >>! flip J)
        <|> antiblep
  <?> "type name"

-- Lowercase identifiers and operators
--  - variable bindings
varp :: Id i => P (Lid i)
varp  = lidp <|> operatorp
  <?> "variable name"

-- Qualified lowercase identifers and operators
--  - variable occurences
-- qvarp :: Id i => P (QLid i)
-- qvarp  = pathp (varp >>! flip J)

-- Identifier expressions
identp :: Id i => P (Ident i)
identp = antiblep
      <|> pathp (flip J <$> (Var <$> varp <|> Con <$> uidp))
  <?> "identifier"

-- Type variables
tyvarp :: Id i => P (TyVar i)
tyvarp  = char '\'' *> (antiblep <|> TV <$> lidp <*> pure Qu)
      <|> char '`'  *> (antiblep <|> TV <$> lidp <*> pure Qa)
  <?> "type variable"

oplevelp :: Id i => Prec -> P (Lid i)
oplevelp  = (<?> "operator") . liftM Syntax.lid . opP

quantp :: P Quant
quantp  = Forall <$ forall
      <|> Exists <$ exists
      <|> antiblep
  <?> "quantifier"

typep  :: Id i => P (Type i)
typep   = typepP precStart

typepP :: Id i => Int -> P (Type i)
typepP p = "type" @@ case () of
  _ | p == precStart
          -> do
               tc <- tyQu <$> quantp
                 <|> tyMu <$  mu
               tvs <- many tyvarp
               dot
               t   <- typepP p
               return (foldr tc t tvs)
             <|> typepP (p + 1)
    | p == precArr
          -> chainr1last
               (typepP (p + 1))
               (choice
                [ tyArr <$ arrow,
                  tyLol <$ lolli,
                  funbraces (tyFun <$> (antiblep <|> Just <$> qExpp)),
                  tybinopp (Right precArr) ])
               (typepP precStart)
    | p == precSemi
          -> chainr1last (typepP (p + 1))
                         (tyBinOp <$> semis)
                         (typepP precStart)
    | Just (Left _) <- fixities p
          -> chainl1last (typepP (p + 1))
                         (tybinopp (Left p))
                         (typepP precStart)
    | Just (Right _) <- fixities p
          -> chainr1last (typepP (p + 1))
                         (tybinopp (Right p))
                         (typepP precStart)
    | p == precApp -- this case ensures termination
          -> tyarg >>= tyapp'
    | p <  precApp
          -> typepP (p + 1)
    | otherwise
          -> typepP precStart
  where
  tyarg :: Id i => P [Type i]
  tyarg  = choice
           [ (:[]) <$> tyatom,
             parens $ antiblep <|> commaSep1 (typepP precStart) ]
  --
  tyatom :: Id i => P (Type i)
  tyatom  = tyVar <$> tyvarp
        <|> tyApp <$> qlidnatp <*> pure []
        <|> antiblep
        <|> tyUn <$ qualU
        <|> tyAf <$ qualA
        <|> do
              ops <- many1 $ addLoc $
                oplevelp (Right precBang) >>! tyApp . J []
              arg <- tyatom <|> parens (typepP precStart)
              return (foldr (\op t -> op [t]) arg ops)
  --
  tyapp' :: Id i => [Type i] -> P (Type i)
  tyapp' [t] = option t $ do
    tc <- qlidnatp
    tyapp' [tyApp tc [t]]
  tyapp' ts  = do
    tc <- qlidnatp
    tyapp' [tyApp tc ts]

tybinopp :: Id i => Prec -> P (Type i -> Type i -> Type i)
tybinopp p = try $ do
  op <- oplevelp p
  when (unLid op == "-") pzero
  return (\t1 t2 -> tyApp (J [] op) [t1, t2])

progp :: Id i => P (Prog i)
progp  = choice [
           do ds <- declsp
              when (null ds) pzero
              e  <- antioptaroundp (reserved "in" `between` punit) exprp
              return (prog ds e),
           antioptp exprp >>! prog []
         ]

replp :: Id i => P [Decl i]
replp  = choice [
           try $ do
             ds <- declsp
             when (null ds) pzero
             eof
             return ds,
           exprp >>! (prog2decls . prog [] . Just)
         ]

declsp :: Id i => P [Decl i]
declsp  = antiblep <|> loop
  where loop =
          choice [
            do
              d  <- declp
              ds <- loop
              return (d : ds),
            (<?> "#load") $ do
              sharpLoad
              name <- stringLiteral
              rel  <- sourceName `liftM` getPosition
              let mcontents = unsafePerformIO $ do
                    mfile <- findAlmsLibRel name rel
                    gmapM readFile mfile
              contents <- case mcontents of
                Just contents -> return contents
                Nothing       -> fail $ "Could not load: " ++ name
              ds <- case parse parseProg name contents of
                Left e   -> fail (show e)
                Right p  -> return (prog2decls p)
              ds' <- loop
              return (ds ++ ds'),
            return []
          ]

declp :: Id i => P (Decl i)
declp  = "declaration" @@ choice [
           do
             reserved "type"
             tyDecsp >>! dcTyp,
           letp,
           do
             reserved "open"
             modexpp >>! dcOpn,
           do
             reserved "module"
             choice [
                 do
                   reserved "type"
                   n <- uidp
                   reservedOp "="
                   s <- sigexpp
                   return (dcSig n s),
                 do
                   n   <- uidp
                   asc <- option id $ do
                     colon
                     sigexpp >>! flip meAsc
                   reservedOp "="
                   b   <- modexpp >>! asc
                   return (dcMod n b)
               ],
           do
             reserved "local"
             ds0 <- declsp
             reserved "with"
             ds1 <- declsp
             reserved "end"
             return (dcLoc ds0 ds1),
           do
             reserved "abstype"
             at <- absTysp
             reserved "with"
             ds <- declsp
             reserved "end"
             return (dcAbs at ds),
           do
             reserved "exception"
             n  <- uidp
             t  <- antioptaroundp (reserved "of" `between` punit) typep
             return (dcExn n t),
           antiblep
         ]

modexpp :: Id i => P (ModExp i)
modexpp  = "structure" @@ foldlp meAsc body ascription where
  body = choice [
           meStr  <$> between (reserved "struct") (reserved "end") declsp,
           meName <$> quidp
                  <*> option [] (antilist1p comma qlidp),
           antiblep
         ]
  ascription = colon *> sigexpp

sigexpp :: Id i => P (SigExp i)
sigexpp  = "signature" @@ do
  se <- choice [
          seSig  <$> between (reserved "sig") (reserved "end")
                             (antiblep <|> many sigitemp),
          seName <$> quidp
                 <*> option [] (antilist1p comma qlidp),
          antiblep
        ]
  specs <- many $ do
    reserved "with"
    reserved "type"
    flip sepBy1 (reserved "and") $ "signature specialization" @@ do
      (tvs, tc) <- tyAppp (antiblep <|>) tyvarp (J []) qlidnatp
      reservedOp "="
      t         <- typep
      return (\sig -> seWith sig tc tvs t)
  return (foldl (flip ($)) se (concat specs))

sigitemp :: Id i => P (SigItem i)
sigitemp = "signature item" @@ choice [
    do
      reserved "val"
      n <- lidp
      colon
      t <- typep
      return (sgVal n t),
    do
      reserved "type"
      sgTyp <$> tyDecsp,
    do
      reserved "module"
      choice [
          do
            reserved "type"
            n <- uidp
            reservedOp "="
            s <- sigexpp
            return (sgSig n s),
          do
            n <- uidp
            colon
            s <- sigexpp
            return (sgMod n s)
        ],
    do
      reserved "include"
      sgInc <$> sigexpp,
    do
      reserved "exception"
      n  <- uidp
      t  <- antioptaroundp (reserved "of" `between` punit) typep
      return (sgExn n t),
    antiblep
  ]

tyDecsp :: Id i => P [TyDec i]
tyDecsp  = antilist1p (reserved "and") tyDecp

tyDecp :: Id i => P (TyDec i)
tyDecp = "type declaration" @@ addLoc $ choice
  [ antiblep
  , do
      optional (reservedOp "|")
      tp    <- typatp
      (name, ps) <- checkHead tp
      case checkTVs ps of
        Just (True, tvs, arity) ->
          reservedOp "=" *>
             (tdDat name tvs <$> altsp
              <|> tryTySyn name ps)
          <|> tdAbs name tvs arity <$> qualsp
        Just (_, tvs, arity) ->
          reservedOp "=" *> tryTySyn name ps
          <|> tdAbs name tvs arity <$> qualsp
        Nothing ->
          reservedOp "=" *> tryTySyn name ps
        ]
  where
  tryTySyn name ps = do
    t    <- typep
    alts <- many $ do
      reservedOp "|"
      tp <- typatp
      (name', ps') <- checkHead tp
      unless (name == name') $
        unexpected $
          "non-matching type operators `" ++ show name' ++
          "' and `" ++ show name ++ "' in type pattern"
      reservedOp "="
      ti <- typep
      return (ps', ti)
    return (tdSyn name ((ps,t):alts))
  --
  checkHead tp = case dataOf tp of
    TpApp (J [] name) ps -> return (name, ps)
    TpApp _ _            -> unexpected "qualified identifier"
    TpVar _ _            -> unexpected "type variable"
    TpAnti _             -> unexpected "antiquote"
  --
  checkTVs [] = return (True, [], [])
  checkTVs (N _ (TpVar tv var):rest) = do
    (b, tvs, vars) <- checkTVs rest
    return (b && var == Invariant, tv:tvs, var:vars)
  checkTVs _ = Nothing

tyAppp :: Id i => (P [a] -> P [a]) -> P a -> (Lid i -> b) -> P b -> P ([a], b)
tyAppp wrap param oper suffix = choice [
  do
    l  <- oplevelp (Right precBang)
    p1 <- param
    return ([p1], oper l),
  try $ do
    p1 <- param
    n <- choice [ semis, operator ]
    when (n == "-" || precOp n == Right precBang) pzero
    p2 <- param
    return ([p1, p2], oper (Syntax.lid n)),
  do
    ps   <- wrap (delimList punit parens comma param)
    name <- suffix
    return (ps, name)
  ]

tyProtp :: Id i => P ([(Variance, TyVar i)], Lid i)
tyProtp  = tyAppp id paramVp id lidnatp

typatp  :: Id i => P (TyPat i)
typatp   = typatpP precStart

typatpP :: Id i => Int -> P (TyPat i)
typatpP p = "type pattern" @@ case () of
  _ | p == precSemi
          -> chainr1last (typatpP (p + 1))
                         (tpBinOp . J [] . Syntax.lid <$> semis)
                         (typatpP precStart)
    | Just (Left _) <- fixities p
          -> chainl1last (typatpP (p + 1))
                         (tpBinOp . J [] <$> oplevelp (Left p))
                         (typatpP precStart)
    | Just (Right _) <- fixities p
          -> chainr1last (typatpP (p + 1))
                         (tpBinOp . J [] <$> oplevelp (Right p))
                         (typatpP precStart)
    | p == precApp -- this case ensures termination
          -> tparg >>= tpapp'
    | p <  precApp
          -> typatpP (p + 1)
    | otherwise
          -> typatpP precStart
  where
  tpBinOp ql tp1 tp2 = tpApp ql [tp1, tp2]
  --
  tparg :: Id i => P [TyPat i]
  tparg  = choice
           [ (:[]) <$> tpatom,
             parens $ antiblep <|> commaSep1 (typatpP precStart) ]
  --
  tpatom :: Id i => P (TyPat i)
  tpatom  = uncurry (flip tpVar) <$> paramVp
        <|> tpApp <$> qlidnatp <*> pure []
        <|> antiblep
        <|> tpApp (qlid "U") [] <$ qualU
        <|> tpApp (qlid "A") [] <$ qualA
        <|> do
              ops <- many1 $ addLoc $
                oplevelp (Right precBang) >>! tpApp . J []
              arg <- tpatom <|> parens (typatpP precStart)
              return (foldr (\op t -> op [t]) arg ops)
  tpapp' :: Id i => [TyPat i] -> P (TyPat i)
  tpapp' [t] = option t $ do
    tc <- qlidnatp
    tpapp' [tpApp tc [t]]
  tpapp' ts  = do
    tc <- qlidnatp
    tpapp' [tpApp tc ts]

letp :: Id i => P (Decl i)
letp  = do
  reserved "let"
  choice [
    do
      reserved "rec"
      bindings <- flip sepBy1 (reserved "and") $ do
        f <- varp
        (sigma, fixt, fixe) <- afargsp
        colon
        t <- typep
        reservedOp "="
        e <- withSigma sigma exprp
        return (bnBind f (fixt t) (fixe e))
      let names    = map (bnvar . dataOf) bindings
          namesExp = foldl1 exPair (map exBVar names)
          namesPat = foldl1 paPair (map paVar names)
          tempVar  = Syntax.lid "#letrec"
          decls0   = [ dcLet (paVar tempVar) Nothing $
                         exLetRec bindings namesExp ]
          decls1   = [ dcLet (paVar (bnvar binding)) Nothing $
                         exLet namesPat (exBVar tempVar) $
                            exBVar (bnvar binding)
                     | N _ binding <- bindings ]
      return $ dcLoc decls0 decls1,
    do
      f <- varp
      (sigma, fixt, fixe) <- afargsp
      t <- antioptaroundp (colon `between` punit) typep
      reservedOp "="
      e <- withSigma sigma exprp
      return (dcLet (paVar f) (fmap fixt t) (fixe e)),
    dcLet <$> pattp
          <*> antioptaroundp (colon `between` punit) typep
          <*  reservedOp "="
          <*> exprp
    ]

absTysp :: Id i => P [AbsTy i]
absTysp = antilist1p (reserved "and") $ absTyp

absTyp :: Id i => P (AbsTy i)
absTyp  = addLoc $ antiblep <|> do
  ((arity, tvs), name) <- tyProtp >>! first unzip
  quals        <- qualsp
  reservedOp "="
  alts         <- altsp
  return (absTy arity quals (tdDat name tvs alts))

paramVp :: Id i => P (Variance, TyVar i)
paramVp = do
  v  <- variancep
  tv <- tyvarp
  return (v, tv)

variancep :: P Variance
variancep =
  choice
    [ char '+' >> return Covariant,
      char '-' >> return Contravariant,
      char '*' >> return Omnivariant,
      char '=' >> return Invariant,
      return Invariant ]

qualsp   :: Id i => P (QExp i)
qualsp    = option minBound $
  (reserved "qualifier" <|> reservedOp ":") *> qExpp

qExpp :: Id i => P (QExp i)
qExpp  = "qualifier expression" @@ qexp where
  qexp  = addLoc $ qeDisj <$> sepBy1 qterm qdisj
  qterm = addLoc $ qeConj <$> sepBy1 qfact qconj
  qfact = addLoc $ parens qexp <|> qatom
  qatom = addLoc $
          qeLit Qu <$  qualU
      <|> qeLit Qa <$  qualA
      <|> clean    <$> tyvarp
      <|> qeLid    <$> lidp
      <|> antiblep
  qeLid = qeVar . flip TV Qa
  clean (TV _ Qu) = minBound
  clean tv        = qeVar tv

altsp :: Id i => P [(Uid i, Maybe (Type i))]
altsp  = sepBy1 altp (reservedOp "|")

altp  :: Id i => P (Uid i, Maybe (Type i))
altp   = do
  k <- try $ uidp <* try (dot *> pzero <|> punit)
  t <- optionMaybe $ do
    reserved "of"
    typep
  return (k, t)

exprp :: Id i => P (Expr i)
exprp = expr0 where
  onlyOne [x] = [x True]
  onlyOne xs  = map ($ False) xs
  mark  = ("expression" @@)
  expr0 = mark $ choice
    [ do reserved "let"
         choice
           [ do reserved "rec"
                bs <- antilist1p (reserved "and") $ bindingp
                reserved "in"
                e2 <- expr0
                return (exLetRec bs e2),
             do (x, sigma, lift) <- pattbangp
                if sigma
                  then do
                    reservedOp "="
                    e1 <- expr0
                    reserved "in"
                    e2 <- withSigma True expr0
                    return (lift True (flip exLet e1) x e2)
                  else do
                    (sigma', args) <- argsp
                    reservedOp "="
                    e1 <- withSigma sigma' expr0
                    reserved "in"
                    e2 <- expr0
                    return (exLet x (args e1) e2),
             do reserved "let"
                unexpected "let",
             do d    <- withSigma False declp
                reserved "in"
                e2   <- expr0
                return (exLetDecl d e2) ],
      do reserved "if"
         ec  <- expr0
         clt <- addLoc $ do
           reserved "then"
           caClause (paCon (quid "true") Nothing) <$> expr0
         clf <- addLoc $ do
           reserved "else"
           caClause (paCon (quid "false") Nothing) <$> expr0
         return (exCase ec [clt, clf]),
      do reserved "match"
         e1 <- expr0
         reserved "with"
         choice [
           exCase e1 <$> antiblep,
           do
             optional (reservedOp "|")
             clauses <- flip sepBy1 (reservedOp "|") preCasealtp
             return (exCase e1 (onlyOne clauses)) ],
      do reserved "try"
         e1 <- expr0
         reserved "with"
         optional (reservedOp "|")
         clauses <- flip sepBy1 (reservedOp "|") $ addLoc $ do
           (xi, sigma, lift) <- pattbangp
           arrow
           ei <- mapSigma (sigma ||) expr0
           return $
             lift False
                  (\xi' ei' ->
                     -- TODO: Make this robust to redefinition of
                     -- Left and Right
                     caClause (paCon (quid "Left") (Just xi')) ei')
                  xi ei
         let tryQ = qlid $
                      "INTERNALS.Exn.tryfun"
         return $
           exCase (exApp (exVar tryQ)
                         (exAbs paWild tyUnit
                            e1)) $
             caClause (paCon (quid "Right")
                             (Just (paVar (Syntax.lid "x"))))
                      (exVar (qlid "x"))
             :
             clauses ++
             [caClause
                (paCon (quid "Left")
                       (Just (paVar (Syntax.lid "e"))))
                (exApp (exVar (qlid "INTERNALS.Exn.raise"))
                       (exVar (qlid "e")))
              ],
      do lambda
         (sigma, build) <- choice
           [
             argsp1,
             do
               (x, sigma, lift) <- pattbangp
               colon
               t <- typepP (precArr + 1)
               return (sigma, lift True (flip exAbs t) x)
           ]
         arrow
         withSigma sigma expr0 >>! build,
      expr1 ]
  expr1 = mark $ do
            e1 <- expr3
            choice
              [ do semi
                   e2 <- expr0
                   return (exSeq e1 e2),
                return e1 ]
  expr3 = mark $ chainl1last expr4 (opappp (Left 3))  expr0
  expr4 = mark $ chainr1last expr5 (opappp (Right 4)) expr0
  expr5 = mark $ chainl1last expr6 (opappp (Left 5))  expr0
  expr6 = mark $ chainl1last expr7 (opappp (Left 6))  expr0
  expr7 = expr8
  expr8 = mark $ chainr1last expr9 (opappp (Right 8)) expr0
  expr9 = mark $ choice
            [ chainl1 expr10 (addLoc (return exApp)),
              do
                reserved "Pack"
                t1 <- antioptaroundp brackets typep
                parens $ do
                  t2 <- typep
                  comma
                  e  <- exprN1
                  return (exPack t1 t2 e)
                ]
  expr10 = mark $ do
    ops <- many $ addLoc $ oplevelp (Right 10) >>! exBVar
    arg <- expr11
    return (foldr exApp arg ops)
  expr11 = mark $ do
             e  <- exprA
             ts <- many . brackets $ commaSep1 typep
             return (foldl exTApp e (concat ts))
  exprA = mark $ choice
    [ identp          >>! exId,
      litp            >>! exLit,
      antiblep,
      parens (exprN1 <|> return (exBCon (Syntax.uid "()")))
    ]
  exprN1 = mark $ do
    e1 <- expr0
    choice
      [ do colon
           t1 <- typep
           let e1' = exCast e1 t1 False
           option e1' $ do
             reservedOp ":>"
             t2 <- typep
             return (exCast e1' t2 True),
        do reservedOp ":>"
           t2 <- typep
           return (exCast e1 t2 True),
        do comma
           es <- commaSep1 expr0
           return (foldl exPair e1 es),
        return e1 ]

preCasealtp :: Id i => P (Bool -> CaseAlt i)
preCasealtp = "match clause" @@ (const <$> antiblep) <|> do
    (xi, sigma, lift) <- pattbangp
    arrow
    ei <- mapSigma (sigma ||) exprp
    return (\b -> lift b caClause xi ei)

casealtp :: Id i => P (CaseAlt i)
casealtp  = preCasealtp >>! ($ False)

bindingp :: Id i => P (Binding i)
bindingp = "let rec binding" @@ antiblep <|> do
  x    <- varp
  (sigma, ft, fe) <- afargsp
  colon
  t    <- typep
  reservedOp "="
  e    <- withSigma sigma exprp
  return (bnBind x (ft t) (fe e))

-- Parse an infix operator at given precedence
opappp :: Id i => Prec -> P (Expr i -> Expr i -> Expr i)
opappp p = do
  op  <- addLoc (oplevelp p >>! exBVar)
  return (\e1 e2 -> op `exApp` e1 `exApp` e2)

-- Zero or more of (pat:typ, ...), (), or tyvar, recognizing '|'
-- to introduce affine arrows
afargsp :: Id i => P (Bool, Type i -> Type i, Expr i -> Expr i)
afargsp = loop tyArr where
  loop arrcon0 = do
    arrcon <- option arrcon0 $ choice
      [ tyFun . Just <$> qualbox qExpp, -- XXX update for implicit arrows
        do
          reservedOp "|"
          return tyLol ]
    choice
      [ do (tvt, tve) <- tyargp
           (b, ft, fe) <- loop arrcon
           return (b, tvt . ft, tve . fe),
        do (b, ft, fe) <- vargp arrcon
           if b
              then return (b, ft, fe)
              else do
                (b', fts, fes) <- loop arrcon
                return (b', ft . fts, fe . fes),
        return (False, id, id) ]

-- One or more of (pat:typ, ...), (), tyvar
argsp1 :: Id i => P (Bool, Expr i -> Expr i)
argsp1  = do
           (b, fe) <- argp
           if b
             then return (b, fe)
             else second (fe .) `fmap` option (False, id) argsp1

-- Zero or more of (pat:typ, ...), (), tyvar
argsp :: Id i => P (Bool, Expr i -> Expr i)
argsp  = option (False, id) $ do
           (b, fe) <- argp
           if b
             then return (b, fe)
             else second (fe .) `fmap` argsp

-- Parse a (pat:typ, ...), (), or tyvar
argp :: Id i => P (Bool, Expr i -> Expr i)
argp  = choice [
          do
            (_, fe)    <- tyargp
            return (False, fe),
          do
            (b, _, fe) <- vargp const
            return (b, fe)
        ]

-- Parse a (pat:typ, ...) or () argument
vargp :: Id i =>
         (Type i -> Type i -> Type i) ->
         P (Bool, Type i -> Type i, Expr i -> Expr i)
vargp arrcon = do
  inBang        <- bangp
  ((p, t), loc) <- withLoc paty
  return (inBang, arrcon t, condSigma inBang True (flip exAbs t) p <<@ loc)

-- Parse a (pat:typ, ...) or () argument
paty :: Id i => P (Patt i, Type i)
paty  = do
  (p, mt) <- pamty
  case (dataOf p, mt) of
    (_, Just t) -> return (p, t)
    (PaCon (J [] (Uid _ "()")) Nothing, Nothing)
                -> return (p, tyUnit)
    (PaWild, Nothing)
                -> return (p, tyAf)
    _           -> pzero <?> ":"

-- Parse a (), (pat:typ, ...) or (pat) argument
pamty :: Id i => P (Patt i, Maybe (Type i))
pamty  = choice
  [ (paWild, Nothing) <$ reserved "_",
    parens $ do
      tvs <- many (tyvarp <* comma)
      (p, mt) <- choice
        [ do
            (p, mt) <- pamty
            maybe (maybecolon p) (morepts p) mt,
          do
            p <- pattp
            maybecolon p,
          return (paCon (quid "()") Nothing, Nothing)
        ]
      return (foldr paPack p tvs,
              fmap (\t -> foldr tyEx t tvs) mt)
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
      return (foldl paPair p ps, Nothing)
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
      return (foldl paPair p0 ps, Just (foldl tyTuple t0 ts))
    colonType p = do
      colon
      t <- typep
      return (p, t)

-- Parse a sequence of one or more tyvar arguments
tyargp :: Id i => P (Type i -> Type i, Expr i -> Expr i)
tyargp  = do
  tvs <- liftM return loctv <|> brackets (commaSep1 loctv)
  return (\t -> foldr (\(tv, _  ) -> tyAll tv) t tvs,
          \e -> foldr (\(tv, loc) -> exTAbs tv <<@ loc) e tvs)
    where
  loctv = withLoc tyvarp

pattbangp :: Id i =>
             P (Patt i, Bool,
                Bool -> (Patt i -> Expr i -> b) -> Patt i -> Expr i -> b)
pattbangp = do
  inSigma <- getSigma
  inBang  <- bangp
  x       <- pattp
  let trans = inBang && not inSigma
      wrap  = inBang && inSigma
  return (condMakeBang wrap x, inBang, condSigma trans)

condSigma :: Id i =>
             Bool -> Bool ->
             (Patt i -> Expr i -> a) ->
             Patt i -> Expr i -> a
condSigma True  = exSigma
condSigma False = const id

condMakeBang :: Id i => Bool -> Patt i -> Patt i
condMakeBang True  = makeBangPatt
condMakeBang False = id

bangp :: P Bool
bangp  = (bang >> return True) <|> return False

pattp :: Id i => P (Patt i)
pattp  = patt0 where
  mark  = ("pattern" @@)
  patt0 = mark $ do
    x <- patt9
    choice
      [ do
          reserved "as"
          y <- varp
          return (paAs x y),
        return x
      ]
  patt9 = mark $ choice
    [ do
        reserved "Pack"
        parens $ do
          tv <- tyvarp
          comma
          x  <- pattN1
          return (paPack tv x),
      paCon <$> quidp
            <*> antioptp (try pattA),
      pattA ]
  pattA = mark $ choice
    [ paWild <$  reserved "_",
      paVar  <$> varp,
      paLit  <$> litp,
      paCon  <$> quidp
             <*> pure Nothing,
      antiblep,
      parens pattN1
    ]
  pattN1 = mark $ choice
    [ paPack <$> try (tyvarp <* comma)
             <*> pattN1,
      do
        xs <- commaSep patt0
        case xs of
          []    -> return (paCon (quid "()") Nothing)
          x:xs' -> return (foldl paPair x xs') ]

litp :: P Lit
litp = (<?> "literal") $ choice [
         integerOrFloat >>! either LtInt LtFloat,
         charLiteral    >>! (LtInt . fromIntegral . fromEnum),
         stringLiteral  >>! LtStr,
         antiblep
       ]

finish :: P a -> P a
finish p = do
  optional (whiteSpace)
  r <- p
  eof
  return r

-- | Parse a program
parseProg     :: Id i => P (Prog i)
-- | Parse a REPL line
parseRepl     :: Id i => P [Decl i]
-- | Parse a sequence of declarations
parseDecls    :: Id i => P [Decl i]
-- | Parse a declaration
parseDecl     :: Id i => P (Decl i)
-- | Parse a module expression
parseModExp   :: Id i => P (ModExp i)
-- | Parse a type declaration
parseTyDec    :: Id i => P (TyDec i)
-- | Parse a abstype declaration
parseAbsTy    :: Id i => P (AbsTy i)
-- | Parse a type
parseType     :: Id i => P (Type i)
-- | Parse a type pattern
parseTyPat    :: Id i => P (TyPat i)
-- | Parse a qualifier expression
parseQExp     :: Id i => P (QExp i)
-- | Parse an expression
parseExpr     :: Id i => P (Expr i)
-- | Parse a pattern
parsePatt     :: Id i => P (Patt i)
-- | Parse a case alternative
parseCaseAlt  :: Id i => P (CaseAlt i)
-- | Parse a let rec binding
parseBinding  :: Id i => P (Binding i)
-- | Parse a signature
parseSigExp   :: Id i => P (SigExp i)
-- | Parse a signature item
parseSigItem  :: Id i => P (SigItem i)

parseProg      = finish progp
parseRepl      = finish replp
parseDecls     = finish declsp
parseDecl      = finish declp
parseModExp    = finish modexpp
parseTyDec     = finish tyDecp
parseAbsTy     = finish absTyp
parseType      = finish typep
parseTyPat     = finish typatp
parseQExp      = finish qExpp
parseExpr      = finish exprp
parsePatt      = finish pattp
parseCaseAlt   = finish casealtp
parseBinding   = finish bindingp
parseSigExp    = finish sigexpp
parseSigItem   = finish sigitemp

-- Convenience functions for quick-and-dirty parsing:

-- | Parse a program
pp  :: String -> Prog Renamed
pp   = makeQaD parseProg

-- | Parse a sequence of declarations
pds :: String -> [Decl Renamed]
pds  = makeQaD parseDecls

-- | Parse a declaration
pd  :: String -> Decl Renamed
pd   = makeQaD parseDecl

pme :: String -> ModExp Renamed
pme  = makeQaD parseModExp

-- | Parse a type declaration
ptd :: String -> TyDec Raw
ptd  = makeQaD parseTyDec

-- | Parse a type
pt  :: String -> Type Renamed
pt   = makeQaD parseType

-- | Parse a type pattern
ptp :: String -> TyPat Renamed
ptp  = makeQaD parseTyPat

-- | Parse a qualifier expression
pqe :: String -> QExp Renamed
pqe  = makeQaD parseQExp

-- | Parse an expression
pe  :: String -> Expr Renamed
pe   = makeQaD parseExpr

-- | Parse a pattern
px  :: String -> Patt Renamed
px   = makeQaD parsePatt

makeQaD :: P a -> String -> a
makeQaD parser =
  either (error . show) id . runParser parser state0 "<string>"
