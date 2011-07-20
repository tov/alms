-- | Parser
module Syntax.Parser (
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

import Util hiding (before, lift)
import Paths
import AST
import Syntax.Prec
import Syntax.Lexer as Lexer
import Error (AlmsError(..), Phase(ParserPhase))
import qualified Message.AST as Msg
import Alt.Parsec hiding (parse)

import Prelude ()
import qualified Data.Map as M
import qualified Data.List as L
import qualified Language.Haskell.TH as TH
import qualified Text.ParserCombinators.Parsec.Error as PE
import System.IO.Unsafe (unsafePerformIO)

data St   = St {
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
           stAnti  = False,
           stPos   = toSourcePos bogus
         }

-- | Run a parser, given the source file name, on a given string
parse   :: P a -> SourceName -> String -> Either ParseError a
parse p  = runParser p state0

-- | Run a parser on the given string in quasiquote mode
parseQuasi :: String ->
              (String -> String -> Maybe TH.Name -> P a) ->
              TH.Q a
parseQuasi str p = do
  loc <- fromTHLoc <$> TH.location
  let parser = do
        setPosition (toSourcePos loc)
        iflag <- (++) <$> option "" (string "+")
                      <*> option "" (string "'")
        lflag <- choice [
                   do char '@'
                      choice [ char '=' >> identp_no_ws >>! Just,
                               char '!' >> return Nothing ],
                   char '!' >> return Nothing,
                   return (Just "_loc")
                 ]
        p (file loc) iflag (fmap TH.mkName lflag)
  either (fail . show) return $
    runParser parser state0 { stAnti = True } "<quasi>" str

-- | REPL-level commands
data REPLCommand
  = GetInfoCmd [Ident Raw]
  | GetPrecCmd [String]
  | DeclsCmd [Decl Raw]
  | ParseError AlmsError

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
parseFile :: Tag i => String -> String -> Either AlmsError (Prog i)
parseFile  = (almsParseError +++ id) <$$> parse parseProg

almsParseError :: ParseError -> AlmsError
almsParseError e =
  AlmsError ParserPhase (fromSourcePos (errorPos e)) message
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
    messages  = [ s | PE.Message s     <- PE.errorMessages e, not $ null s ]
    unexpects = [ s | PE.UnExpect s    <- PE.errorMessages e, not $ null s ]
             ++ [ s | PE.SysUnExpect s <- PE.errorMessages e, not $ null s ]
    expects   = [ s | PE.Expect s      <- PE.errorMessages e, not $ null s ]
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
               <|> J [] . Var . ident <$> (operator <|> qjoin))

parseGetPrec :: String -> Maybe [String]
parseGetPrec = (const Nothing ||| Just) . runParser parser state0 "-"
  where
    parser = finish $
      sharpPrec *>
        many1 (operator <|> qjoin)

parseInteractive :: Tag i => Int -> String -> Either ParseError [Decl i]
parseInteractive line src = parse p "-" src where
  p = do
    pos <- getPosition
    setPosition (pos `setSourceLine` line)
    optional whiteSpace
    r <- replp
    eof
    return r

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

antilistp :: Antible a => P b -> P a -> P [a]
antilistp  = option [] <$$> antilist1p

-- Just uppercase identifiers
uidp :: Tag i => P (Uid i)
uidp  = ident <$> Lexer.uid
    <|> antiblep
  <?> "uppercase identifier"

-- Just lowercase identifiers
lidp :: Tag i => P (Lid i)
lidp  = ident <$> Lexer.lid
    <|> antiblep
  <?> "lowercase identifier"

-- Just uppercase row labels
ulabelp :: Tag i => P (Uid i)
ulabelp  = ident <$> Lexer.ulabel
    <|> antiblep
  <?> "variant constructor label"

-- Just lowercase row labels
llabelp :: Tag i => P (Uid i)
llabelp  = ident <$> Lexer.llabel
    <|> antiblep
  <?> "record field label"

-- Infix operator at the given precdence
oplevelp :: Tag i => Prec -> P (Lid i)
oplevelp p = ident <$> opP p
  <?> "infix operator"

-- Just parenthesized operators
operatorp :: Tag i => P (Lid i)
operatorp  = ident <$> try (parens (operator <|> semis))
  <?> "operator name"

-- Lowercase identifiers or naturals
--  - tycon declarations
lidnatp :: Tag i => P (Lid i)
lidnatp = ident <$> (Lexer.lid <|> show <$> natural)
      <|> operatorp
      <|> antiblep
  <?> "type name"

-- Type identifiers (unqualified)
typidp :: Tag i => P (TypId i)
typidp  = antiblep
      <|> TypId <$> (lidnatp <|> operatorp)
      <|> ident "A" <$ qualA
      <|> ident "U" <$ qualU
  <?> "type constructor"

-- Infix type identifiers
typopp  :: Tag i => Prec → P (TypId i)
typopp p = TypId <$> oplevelp p
  <?> "infix type operator"

-- Variable bindings
varidp :: Tag i => P (VarId i)
varidp  = antiblep
      <|> VarId <$> (lidp <|> operatorp)
  <?> "variable name"

-- Infix variable occurrences
varopp  :: Tag i => Prec → P (VarId i)
varopp p = VarId <$> oplevelp p
  <?> "infix operator"

-- Data constructor names
conidp :: Tag i => P (ConId i)
conidp  = antiblep
      <|> ConId <$> uidp
  <?> "data constructor"

-- Module names
modidp :: Tag i => P (ModId i)
modidp  = antiblep
      <|> ModId <$> uidp
  <?> "module name"

-- Module type names
sigidp :: Tag i => P (SigId i)
sigidp  = antiblep
      <|> SigId <$> uidp
  <?> "module type (signature) name"

-- Add a path before something
pathp :: (Tag i, Antible b) => P ([ModId i] -> b) -> P b
pathp p = (antiblep <|>) . try $ do
  path <- many $ try $ modidp <* dot
  make <- p
  return (make path)

-- Qualified type identifiers
qtypidp :: Tag i => P (QTypId i)
qtypidp  = pathp (flip J <$> typidp)
  <?> "(qualified) type constructor"

-- Qualified variable occurrences
qvaridp :: Tag i => P (QVarId i)
qvaridp  = pathp (flip J <$> varidp)
  <?> "(qualified) variable name"

-- Qualified data constructor names
qconidp :: Tag i => P (QConId i)
qconidp  = pathp (flip J <$> conidp)
  <?> "(qualified) data constructor"

-- Qualified module names
qmodidp :: Tag i => P (QModId i)
qmodidp  = pathp (flip J <$> modidp)
  <?> "(qualified) module name"

-- Qualified module type names
qsigidp :: Tag i => P (QSigId i)
qsigidp  = pathp (flip J <$> sigidp)
  <?> "(qualified) module type name"

-- Identifiers
identp :: Tag i => P (Ident i)
identp = pathp (flip J <$> (Var . unTypId <$> typidp <|> Con <$> uidp))
  <?> "identifier"

-- Type variables
tyvarp :: Tag i => P (TyVar i)
tyvarp  = try $ "type variable" @@
            sigilU *> tv Qu
        <|> sigilA *> tv Qa
  where tv q = antiblep <|> TV <$> lidp <*> pure q <*> pure bogus

-- open variant injection constructor
varinjp ∷ Tag i ⇒ P (Uid i)
varinjp = try (variantInj *> ulabelp)
  <?> "open variant constructor"

-- open variant embedding constructor
varembp ∷ Tag i ⇒ P (Uid i)
varembp = try (variantEmb *> ulabelp)
  <?> "open variant constructor"

quantp :: P Quant
quantp  = Forall <$ forall
      <|> Exists <$ exists
      <|> antiblep
  <?> "quantifier"

typep  :: Tag i => P (Type i)
typep   = typepP precStart

typepP :: Tag i => Int -> P (Type i)
typepP p = "type" @@ case () of
  _ | p == precStart
          -> tyrowp1 <|> next
    | p == precDot
          -> do
               tc <- tyQu <$> quantp
                 <|> tyMu <$  mu
               tvs <- many tyvarp
               dot
               t   <- typepP p
               return (foldr tc t tvs)
             <|> next
    | p == precArr
          -> chainr1last
               next
               (choice
                [ tyArr <$ arrow,
                  tyLol <$ lolli,
                  funbraces (flip tyFun <$> (antiblep <|> Just <$> qExpp)),
                  tybinopp (Right precArr) ])
               (typepP precStart)
    | p == precTySemi
          -> chainr1last next
                         (tyAppN <$> (semis <|> qjoin))
                         (typepP precStart)
    | Just (Left _) <- fixities p
          -> chainl1last next
                         (tybinopp (Left p))
                         (typepP precStart)
    | Just (Right _) <- fixities p
          -> chainr1last next
                         (tybinopp (Right p))
                         (typepP precStart)
    | p == precApp -- this case ensures termination
          -> tyarg >>= tyapp'
    | p <  precApp
          -> next
    | otherwise
          -> typepP precStart
  where
  tyarg :: Tag i => P [Type i]
  tyarg  = parens (antiblep <|> commaSep1 (typepP precMin))
       <|> (:[]) <$> tyatom
  --
  tyatom :: Tag i => P (Type i)
  tyatom  = tyVar <$> tyvarp
        <|> tyApp <$> qtypidp <*> pure []
        <|> antiblep
        <|> variantp
        <|> recordp
        <|> parens (typepP precMin)
        <|> do
              ops <- many1 $ addLoc $
                typopp (Right precBang) >>! tyApp . J []
              arg <- tyatom
              return (foldr (\op t -> op [t]) arg ops)
  --
  tyapp' :: Tag i => [Type i] -> P (Type i)
  tyapp' [t] = option t $
    do
      tc <- qtypidp
      tyapp' [tyApp tc [t]]
    <|>
    do
      ellipsis
      tyapp' [tyRowDots t]
  tyapp' ts  = do
    tc <- qtypidp
    tyapp' [tyApp tc ts]
  --
  next = typepP (p + 1)

variantp ∷ Tag i ⇒ P (Type i)
variantp = AST.tyVariant <$> brackets tyrowp

tyrowp1 ∷ Tag i ⇒ P (Type i)
tyrowp1 = AST.tyRow <$> varinjp
                       <*> option AST.tyUnit
                             (reserved "of" *> typepP precStart)
                       <*> option AST.tyRowEnd
                             (reservedOp "|" *> tyrowp)

tyrowp ∷ Tag i ⇒ P (Type i)
tyrowp = "row type" @@
         antiblep
     <|> tyrowp1
     <|> AST.tyVar    <$> tyvarp
     <|> AST.tyRowEnd <$  whiteSpace

recordp ∷ Tag i ⇒ P (Type i)
recordp = AST.tyRecord <$$> braces $
  recrowp <|> AST.tyRowEnd <$ whiteSpace

recrowp ∷ Tag i ⇒ P (Type i)
recrowp = antiblep
      <|> AST.tyRow <$> llabelp <* colon
                       <*> typepP precStart
                       <*> option AST.tyRowEnd (comma *> recrowp)
      <|> AST.tyVar <$> tyvarp

tybinopp :: Tag i => Prec -> P (Type i -> Type i -> Type i)
tybinopp p = try $ do
  op <- typopp p
  when (idName op == "-") pzero
  return (\t1 t2 -> tyApp (J [] op) [t1, t2])

progp :: Tag i => P (Prog i)
progp  = choice [
           do ds <- declsp
              when (null ds) pzero
              e  <- antioptaroundp (reserved "in" `between` punit) exprp
              return (prog ds e),
           antioptp exprp >>! prog []
         ]

replp :: Tag i => P [Decl i]
replp  = choice [
           try $ do
             ds <- declsp
             when (null ds) pzero
             eof
             return ds,
           exprp >>! (prog2decls . prog [] . Just)
         ]

declsp :: Tag i => P [Decl i]
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
                    traverse readFile mfile
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

declp :: Tag i => P (Decl i)
declp  = "declaration" @@ choice [
           do
             tid ← try $
               reserved "type" *> typidp <* reservedOp "=" <* reserved "type"
             rhs ← qtypidp
             return (dcAli tid rhs),
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
                   n <- sigidp
                   reservedOp "="
                   s <- sigexpp
                   return (dcSig n s),
                 do
                   n   <- modidp
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
             n  <- conidp
             t  <- antioptaroundp (reserved "of" `between` punit) typep
             return (dcExn n t),
           antiblep
         ]

modexpp :: Tag i => P (ModExp i)
modexpp  = "structure" @@ foldlp meAsc body ascription where
  body = choice [
           meStr  <$> between (reserved "struct") (reserved "end") declsp,
           meName <$> qmodidp
                  <*> antilistp comma qvaridp,
           antiblep
         ]
  ascription = colon *> sigexpp

sigexpp :: Tag i => P (SigExp i)
sigexpp  = "signature" @@ do
  se <- choice [
          seSig  <$> between (reserved "sig") (reserved "end")
                             (antiblep <|> many sigitemp),
          seName <$> qsigidp
                 <*> antilistp comma qvaridp,
          antiblep
        ]
  specs <- many $ do
    reserved "with"
    reserved "type"
    flip sepBy1 (reserved "and") $ "signature specialization" @@ do
      (tvs, tc) <- tyAppp (antiblep <|>) tyvarp (J []) qtypidp
      reservedOp "="
      t         <- typep
      return (\sig -> seWith sig tc tvs t)
  return (foldl (flip ($)) se (concat specs))

sigitemp :: Tag i => P (SigItem i)
sigitemp = "signature item" @@ choice [
    do
      reserved "val"
      n <- varidp
      colon
      t <- typep
      return (sgVal n t),
   do
     tid ← try $
       reserved "type" *> typidp <* reservedOp "=" <* reserved "type"
     rhs ← qtypidp
     return (sgAli tid rhs),
    do
      reserved "type"
      sgTyp <$> tyDecsp,
    do
      reserved "module"
      choice [
          do
            reserved "type"
            n <- sigidp
            reservedOp "="
            s <- sigexpp
            return (sgSig n s),
          do
            n <- modidp
            colon
            s <- sigexpp
            return (sgMod n s)
        ],
    do
      reserved "include"
      sgInc <$> sigexpp,
    do
      reserved "exception"
      n  <- conidp
      t  <- antioptaroundp (reserved "of" `between` punit) typep
      return (sgExn n t),
    antiblep
  ]

tyDecsp :: Tag i => P [TyDec i]
tyDecsp  = antilist1p (reserved "and") tyDecp

tyDecp :: Tag i => P (TyDec i)
tyDecp = "type declaration" @@ addLoc $ choice
  [ antiblep
  , do
      optional (reservedOp "|")
      tp    <- typatp
      (name, ps) <- checkHead tp
      case checkTVs ps of
        -- Could be a data type, a synonym, or an abstract type
        Just (True, tvs, arity) ->
          reservedOp "=" *>
             (tdDat name tvs <$> altsp
              <|> tryTySyn name ps)
          <|> finishTyAbs name tvs arity
        -- Must be a synonym or an abstract type
        Just (_, tvs, arity) ->
          reservedOp "=" *> tryTySyn name ps
          <|> finishTyAbs name tvs arity
        -- Must be a type function
        Nothing ->
          reservedOp "=" *> tryTySyn name ps
        ]
  where
  -- Try to parse the right-hand side of a type synonym
  tryTySyn name ps = do
    t    <- typep
    alts <- many $ do
      reservedOp "|"
      tp <- typatp
      (name', ps') <- checkHead tp
      unless (name == name') $
        unexpected $
          "non-matching type operators ‘" ++ show name' ++
          "’ and ‘" ++ show name ++ "’ in type pattern"
      reservedOp "="
      ti <- typep
      return (ps', ti)
    return (tdSyn name ((ps,t):alts))
  --
  finishTyAbs name tvs arity = do
    guards ← option [] $ brackets $ reserved "rec" *> many1 tyvarp
    tdAbs name tvs arity guards <$> qualsp
  --
  -- A type declaration needs to give an unqualified name for the type
  -- being defined.  This checks that and splits into the name and the
  -- parameter patterns.
  checkHead tp = case dataOf tp of
    TpApp (J [] name) ps -> return (name, ps)
    TpApp _ _            -> unexpected "qualified identifier"
    TpVar _ _            -> unexpected "type variable"
    TpRow _ _            -> unexpected "row type"
    TpAnti _             -> unexpected "antiquote"
  --
  -- Look at the parameters and determine what kind of type declaration
  -- this might be. Returns @Just (allInv, tvs, vars)@ if all the
  -- parameters are type variables, where @allInv@ tells whether all the
  -- variances are 'Invariant', and @tvs@ and @vars@ are the lists of
  -- type variables and variances. Otherwise, we're defining a type
  -- function and it returns @Nothing@.
  checkTVs [] = return (True, [], [])
  checkTVs (N _ (TpVar tv var):rest) = do
    (b, tvs, vars) <- checkTVs rest
    return (b && var == Invariant, tv:tvs, var:vars)
  checkTVs _ = Nothing

-- | Generic parser for things in the shape of type constructor
--   applications.
tyAppp :: Tag i =>
          -- | Wrapper for parsing the parameter(s) of a normal suffix
          --   type application
          (P [a] -> P [a]) ->
          -- | Parser for a type parameter
          P a ->
          -- | Injection to lift a type operator
          (TypId i -> b) ->
          -- | Parser for postfix constructor
          P b ->
          P ([a], b)
tyAppp wrap param oper suffix = choice [
  -- prefix operator
  do
    l  <- typopp (Right precBang)
    p1 <- param
    return ([p1], oper l),
  -- infix operator
  try $ do
    p1 <- param
    n <- choice [ semis, operator ]
    when (n == "-" || precOp n == Right precBang) pzero
    p2 <- param
    return ([p1, p2], oper (ident n)),
  -- normal postfix application
  do
    ps   <- wrap (delimList punit parens comma param)
    name <- suffix
    return (ps, name)
  ]

-- | Left-hand side of a type declaration, which looks like a
--   type constructor applied to parameters
tyProtp :: Tag i => P ([(Variance, TyVar i)], TypId i)
tyProtp  = tyAppp id paramVp id typidp

-- | A type pattern
typatp  :: Tag i => P (TyPat i)
typatp   = typatpP precStart

typatpP :: Tag i => Int -> P (TyPat i)
typatpP p = "type pattern" @@ case () of
  _ | p == precTySemi
          -> chainr1last (typatpP (p + 1))
                         (tpBinOp . J [] . ident <$> semis)
                         (typatpP precStart)
    | Just e <- fixities p -> case e of
        Left _ ->
          chainl1last (typatpP (p + 1))
                      (tpBinOp . J [] <$> typopp (Left p))
                      (typatpP precStart)
        Right _ ->
          chainr1last (typatpP (p + 1))
                      (tpBinOp . J [] <$> typopp (Right p))
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
  tparg  = parens (antiblep <|> commaSep1 (typatpP precMin))
       <|> (:[]) <$> tpatom
  --
  tpatom  = tpvar
        <|> tpApp <$> qtypidp <*> pure []
        <|> antiblep
        <|> tpApp (qident "U") [] <$ qualU
        <|> tpApp (qident "A") [] <$ qualA
        <|> tpvariant
        <|> tprecord
        <|> parens (typatpP precMin)
        <|> do
              ops <- many1 $ addLoc $
                typopp (Right precBang) >>! tpApp . J []
              arg <- tpatom
              return (foldr (\op t -> op [t]) arg ops)
  tpapp' [t] = option t $ do
    tc <- qtypidp
    tpapp' [tpApp tc [t]]
  tpapp' ts  = do
    tc <- qtypidp
    tpapp' [tpApp tc ts]
  --
  tpvar = do
    (v,tv) <- paramVp
    con    <- option tpVar (tpRow <$ ellipsis)
    return (con tv v)
  --
  tpvariant = brackets $
    tpApp (qident tnVariant) . (:[]) <$> (antiblep <|> tpvar)
  tprecord  = braces $
    tpApp (qident tnRecord) . (:[]) <$> (antiblep <|> tpvar)

-- | A let or let rec declaration
letp :: Tag i => P (Decl i)
letp  = do
  reserved "let"
  choice [
    do
      reserved "rec"
      dcLetRec <$> antilist1p (reserved "and") bindingp,
    do
      f     <- varidp
      args  <- buildargsp
      annot <- buildannotp
      reservedOp "="
      e     <- args . annot <$> exprp
      return (dcLet (paVar f) e),
    dcLet <$> pattp
          <*  reservedOp "="
          <*> exprp
    ]

-- An abstype group
absTysp :: Tag i => P [AbsTy i]
absTysp = antilist1p (reserved "and") $ absTyp

-- A single abstype
absTyp :: Tag i => P (AbsTy i)
absTyp  = addLoc $ antiblep <|> do
  ((arity, tvs), name) <- tyProtp >>! first unzip
  quals        <- qualsp
  reservedOp "="
  alts         <- altsp
  return (absTy arity quals (tdDat name tvs alts))

-- A type declaration parameter, consisting of a variance and a tyvar
paramVp :: Tag i => P (Variance, TyVar i)
paramVp = try $ (,) <$> variancep <*> tyvarp

-- A variance mark
variancep :: P Variance
variancep = do
    qvariance ← option Invariant (QInvariant <$ markQVariant)
    sign      ← option Invariant $ choice
      [ Covariant     <$ markCovariant
      , Contravariant <$ markContravariant
      , Omnivariant   <$ markOmnivariant
      , Invariant     <$ markInvariant ]
    return (qvariance ⊓ sign)
  <?> "variance marker"

-- A qualifier annotation for a type declaration
qualsp   :: Tag i => P (QExp i)
qualsp    = option minBound $
  (reserved "qualifier" <|> reservedOp ":") *> qExpp

-- A qualifier expression
qExpp :: Tag i => P (QExp i)
qExpp  = "qualifier expression" @@ qexp where
  qexp  = addLoc $
            chainl1 qatom (addLoc $ qeJoin <$ (void comma <|> qjoinArr))
  qatom = addLoc $
          qeLit Qu <$  qualU
      <|> qeLit Qa <$  qualA
      <|> clean    <$> tyvarp
      <|> qeLid    <$> lidp
      <|> antiblep
      <|> parens qexp
  qeLid = qeVar . (TV <-> Qa <-> bogus)
  clean (TV _ Qu _) = minBound
  clean tv          = qeVar tv

altsp :: Tag i => P [(ConId i, Maybe (Type i))]
altsp  = sepBy1 altp (reservedOp "|")

altp  :: Tag i => P (ConId i, Maybe (Type i))
altp   = do
  k <- try $ conidp <* try (dot *> pzero <|> punit)
  t <- optionMaybe $ do
    reserved "of"
    typep
  return (k, t)

exprp :: Tag i => P (Expr i)
exprp  = exprpP precStart

exprpP :: Tag i => Int -> P (Expr i)
exprpP p = mark $ case () of
  _ | p == precStart → choice
    [ do reserved "let"
         choice
           [ exLetRec <$  reserved "rec"
                      <*> antilist1p (reserved "and") bindingp
                      <*  reserved "in"
                      <*> exprp
           , exLet <$> (paVar <$> varidp)
                   <*> (buildargsp <*>
                         (buildannotp <* reservedOp "=" <*> exprp))
                   <*  reserved "in"
                   <*> exprp
           , exLet <$> pattp
                   <*  reservedOp "="
                   <*> exprp
                   <*  reserved "in"
                   <*> exprp
           , reserved "let" *> unexpected "let"
           , exLetDecl <$> declp
                       <*  reserved "in"
                       <*> exprp ],
      do reserved "if"
         ec  <- exprp
         clt <- addLoc $ do
           reserved "then"
           caClause (paCon (qident "INTERNALS.PrimTypes.true") Nothing)
                <$> exprp
         clf <- addLoc $ do
           reserved "else"
           caClause (paCon (qident "INTERNALS.PrimTypes.false") Nothing)
                <$> exprp
         return (exCase ec [clt, clf]),
      do reserved "match"
         e1 <- exprp
         reserved "with"
         choice [
           exCase e1 <$> antiblep,
           do
             optional (reservedOp "|")
             clauses <- flip sepBy1 (reservedOp "|") casealtp
             return (exCase e1 clauses) ],
      do reserved "try"
         e1 <- exprp
         reserved "with"
         optional (reservedOp "|")
         clauses <- sepBy1 <-> reservedOp "|" $ addLoc $ do
           caClause . paCon (qident "Left") . Just
             <$> pattp
             <*  arrow
             <*> exprp
         let tryQ = qident $
                      "INTERNALS.Exn.tryfun"
         return $
           exCase (exApp (exVar tryQ)
                         (exAbs paWild e1)) $
             caClause (paCon (qident "Right")
                             (Just (paVar (ident "x"))))
                      (exVar (qident "x"))
             :
             clauses ++
             [caClause
                (paCon (qident "Left")
                       (Just (paVar (ident "e"))))
                (exApp (exVar (qident "INTERNALS.Exn.raise"))
                       (exVar (qident "e")))
              ],
      lambda *> buildargsp <* arrow <*> exprp,
      next ]
    | p == precExSemi → do
        e1 <- next
        choice
          [ do semi
               e2 <- exprp
               return (exSeq e1 e2),
            return e1 ]
    | p == precCast → do
        e1 <- next
        anns <- many $ do
          b  <- False <$ colon
            <|> True <$ reservedOp ":>"
          t2 <- typep
          return (t2, b)
        return (foldl (uncurry . exCast) e1 anns)
    | p == precTySemi →
        next
    | p == precApp    →
        choice [
          exCon <$> qconidp <*> antioptp next,
          exInj <$> varinjp <*> antioptp next,
          exEmb <$> varembp <*> next,
          chainl1 next (addLoc (return exApp))
        ]
    | p == precBang   → do
        ops <- many $ addLoc $ exBVar <$> varopp (Right precBang)
        arg <- next
        return (foldr exApp arg ops)
    | p == precCom    →
        foldl1 exPair <$> commaSep1 next
    | p > precMax     → choice
        [
          exVar <$> qvaridp,
          exCon <$> qconidp <*> pure Nothing,
          exLit <$> litp,
          antiblep,
          parens (exprpP precMin <|> pure (exBCon (ident "()") Nothing))
        ]
    | Just (Left _) <- fixities p ->
        chainl1last next (opappp (Left p)) exprp
    | Just (Right _) <- fixities p ->
        chainr1last next (opappp (Right p)) exprp
    | otherwise       → next
  where
  next = exprpP (p + 1)
  mark = ("expression" @@)

-- Parse a match clause
casealtp :: Tag i => P (CaseAlt i)
casealtp  = "match clause" @@ antiblep <|>
     caClause <$> pattp <* arrow <*> exprp
 <|> caPrj <$> varembp <*> antioptp pattp <* arrow <*> exprp

-- Parse a single let rec binding
bindingp :: Tag i => P (Binding i)
bindingp = "let rec binding" @@ antiblep <|>
  bnBind <$> varidp
         <*> (buildargsp
               <*> (buildannotp
                     <* reservedOp "="
                     <*> exprp))

-- Parse an infix operator at given precedence
opappp :: Tag i => Prec -> P (Expr i -> Expr i -> Expr i)
opappp p = do
  op  <- addLoc (exBVar <$> varopp p)
  return (\e1 e2 -> op `exApp` e1 `exApp` e2)

-- Parse some number of argument patterns and return the function
-- that adds them to a body expression to build a lambda.
buildargsp :: Tag i => P (Expr i -> Expr i)
buildargsp = (foldr exAbs <->) <$> many (pattpP (precApp + 1))

-- Parse an optional type annotation and return the function that
-- adds it as an ascription on an expression.
buildannotp :: Tag i => P (Expr i -> Expr i)
buildannotp = do
  mt <- antioptaroundp (colon *>) typep
  return $ case mt of
    Nothing → id
    Just t  → \e → exCast e t False

-- A pattern
pattp :: Tag i => P (Patt i)
pattp  = pattpP precStart

pattpP ∷ Tag i ⇒ Int → P (Patt i)
pattpP p = mark $ case () of
  _ | p == precCast →
        foldl paAnn <$> next <*> many (colon *> typep)
    | p == precEq   → do
        x <- next
        choice
          [ do
              reserved "as"
              y <- varidp
              return (paAs x y),
            return x
          ]
    | p == precApp    →
        choice [
          paCon <$> qconidp <*> antioptp next,
          paInj <$> varinjp <*> antioptp next,
          next
        ]
    | p == precBang   →
        option id (paBang <$ bang) <*> next
    | p == precCom    →
        foldl1 paPair <$> commaSep1 next
    | p > precMax     → choice
        [
          paWild <$  reserved "_",
          paVar  <$> varidp,
          paCon  <$> qconidp <*> pure Nothing,
          paInj  <$> varinjp <*> pure Nothing,
          paLit  <$> litp,
          antiblep,
          parens (pattpP precMin <|> pure (paCon (qident "()") Nothing))
        ]
    | otherwise     → next
  where
  next = pattpP (p + 1)
  mark  = ("pattern" @@)

litp :: P Lit
litp = (<?> "literal") $ choice [
         integerOrFloat >>! either LtInt LtFloat,
         charLiteral    >>! LtChar,
         stringLiteral  >>! LtStr,
         antiblep
       ]

finish :: P a -> P a
finish p = do
  optional whiteSpace
  r <- p
  eof
  return r

-- | Parse a program
parseProg     :: Tag i => P (Prog i)
-- | Parse a REPL line
parseRepl     :: Tag i => P [Decl i]
-- | Parse a sequence of declarations
parseDecls    :: Tag i => P [Decl i]
-- | Parse a declaration
parseDecl     :: Tag i => P (Decl i)
-- | Parse a module expression
parseModExp   :: Tag i => P (ModExp i)
-- | Parse a type declaration
parseTyDec    :: Tag i => P (TyDec i)
-- | Parse a abstype declaration
parseAbsTy    :: Tag i => P (AbsTy i)
-- | Parse a type
parseType     :: Tag i => P (Type i)
-- | Parse a type pattern
parseTyPat    :: Tag i => P (TyPat i)
-- | Parse a qualifier expression
parseQExp     :: Tag i => P (QExp i)
-- | Parse an expression
parseExpr     :: Tag i => P (Expr i)
-- | Parse a pattern
parsePatt     :: Tag i => P (Patt i)
-- | Parse a case alternative
parseCaseAlt  :: Tag i => P (CaseAlt i)
-- | Parse a let rec binding
parseBinding  :: Tag i => P (Binding i)
-- | Parse a signature
parseSigExp   :: Tag i => P (SigExp i)
-- | Parse a signature item
parseSigItem  :: Tag i => P (SigItem i)

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
ptd :: Tag i => String -> TyDec i
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

{-
deriving instance Show (Expr' i)
deriving instance Show (CaseAlt' i)
deriving instance Show (Decl' i)
deriving instance Show (Binding' i)
deriving instance Show (AbsTy' i)
deriving instance Show (ModExp' i)
deriving instance Show (SigExp' i)
deriving instance Show (TyDec' i)
deriving instance Show (TyPat' i)
deriving instance Show (SigItem' i)
deriving instance Show (Patt' i)
deriving instance Show (Type' i)
deriving instance Show (QExp' i)
deriving instance Show (Prog' i)
deriving instance Show Lit
instance Show a ⇒ Show (N i a) where showsPrec = showsPrec <$.> view
-}

makeQaD :: P a -> String -> a
makeQaD parser =
  either (error . show) id . runParser parser state0 "<string>"

