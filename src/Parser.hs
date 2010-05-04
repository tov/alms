{-# LANGUAGE
      ScopedTypeVariables #-}
-- | Parser
module Parser (
  -- * The parsing monad
  P, parse,
  -- ** Quasiquote parsing
  parseQuasi, TyTagMode(..),
  -- ** Parsers
  parseProg, parseRepl, parseDecls, parseDecl, parseModExp,
    parseTyDec, parseType, parseQExp, parseExpr, parsePatt,
  -- * Convenience parsers (quick and dirty)
  pp, pds, pd, pme, ptd, pt, pqe, pe, px
) where

import Util
import Paths
import Prec
import Syntax
import Sigma
import Loc
import Lexer

import Data.Generics (Data)
import qualified Data.Map as M
import qualified Language.Haskell.TH as TH
import Text.ParserCombinators.Parsec hiding (parse)
import System.IO.Unsafe (unsafePerformIO)

data St   = St {
              stSigma :: Bool,
              stAnti  :: Bool
            }

-- | A 'Parsec' character parser, with abstract state
type P a  = CharParser St a

state0 :: St
state0 = St {
           stSigma = False,
           stAnti  = False
         }

-- | Run a parser, given the source file name, on a given string
parse   :: P a -> SourceName -> String -> Either ParseError a
parse p  = runParser p state0

-- | Run a parser on the given string in quasiquote mode
parseQuasi :: Data a => String -> (Bool -> Maybe String -> P a) -> TH.Q a
parseQuasi str p = do
  setter <- TH.location >>! mkSetter
  let parser = do
        setter
        iflag <- option False (do char '+'; return True)
        lflag <- choice [
                   do char '@'
                      choice [ char '=' >> identp_no_ws >>! Just,
                               char '!' >> return Nothing ],
                   return (Just "_loc")
                 ]
        p iflag lflag
  case runParser parser state0 { stAnti = True } "-" str of
    Left e  -> fail (show e)
    Right a -> return (scrub a)
  where
  mkSetter = setPosition . toSourcePos . fromTHLoc

class TyTagMode i where
  tytagp     :: P i
  injTd      :: TyTag -> i
  liftUnit   :: f () -> f i
  dropUnit   :: f i -> f ()

instance TyTagMode () where
  tytagp     = punit
  injTd      = const ()
  liftUnit   = id
  dropUnit   = id

instance TyTagMode TyTag where
  tytagp     = antiblep
  injTd      = id
  liftUnit   = error "BUG! Cannot use exSigma in quasi mode"
  dropUnit   = error "BUG! Cannot use exSigma in quasi mode"

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

curLoc :: P Loc
curLoc  = getPosition >>! fromSourcePos

addLoc :: Relocatable a => P a -> P a
addLoc p = do
  loc <- curLoc
  a   <- p
  return (a <<@ loc)

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

-- Antiquote
antip :: AntiDict -> P Anti
antip dict = (<?> "antiquote") . lexeme . try $ do
  char '$'
  (s1, s2) <- (,) <$> option "" (try (option "" identp_no_ws <* char ':'))
                  <*> identp_no_ws
  assertAnti
  case M.lookup s1 dict of
    Just _  -> return (Anti s1 s2)
    Nothing -> unexpected $ "antiquote tag: `" ++ s1 ++ "'"

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

antioptaroundp :: Antible a => (P (Maybe a) -> P (Maybe a)) -> P a -> P (Maybe a)
antioptaroundp wrap p = wrap present <|> pure Nothing
  where present = antiblep
              <|> Just <$> antiblep
              <|> Just <$> p

antilist1p       :: Antible a => P () -> P a -> P [a]
antilist1p sep p  = antiblep
                <|> sepBy1 (antiblep <|> p) sep

-- Just uppercase identifiers
uidp :: P Uid
uidp  = Uid <$> uid
    <|> antiblep

-- Just lowercase identifiers
lidp :: P Lid
lidp  = Lid <$> lid
    <|> antiblep

-- Lowercase identifiers or naturals
--  - tycon declarations
lidnatp :: P Lid
lidnatp = Lid <$> (lid <|> show <$> natural)
      <|> antiblep

-- Just operators
operatorp :: P Lid
operatorp  = try (parens operator) >>! Lid

-- Add a path before something
pathp :: P ([Uid] -> b) -> P b
pathp p = try $ do
  path <- many $ try $ uidp <* dot
  make <- p
  return (make path)

-- Qualified uppercase identifiers:
--  - module names occurences
--  - datacons in patterns (though path is ignored)
quidp :: P QUid
quidp  = pathp (uidp >>! flip J)
     <|> antiblep

-- Qualified lowercase identifiers:
-- qlidp :: P QLid
-- qlidp  = pathp (lidp >>! flip J)

-- Qualified lowercase identifiers or naturals:
--  - tycon occurences
qlidnatp :: P QLid
qlidnatp  = pathp (lidnatp >>! flip J)
        <|> antiblep

-- Lowercase identifiers and operators
--  - variable bindings
varp :: P Lid
varp  = lidp <|> operatorp

-- Qualified lowercase identifers and operators
--  - variable occurences
-- qvarp :: P QLid
-- qvarp  = pathp (varp >>! flip J)

-- Identifier expressions
identp :: P Ident
identp = antiblep
      <|> pathp (flip J <$> (Var <$> varp <|> Con <$> uidp))

-- Type variables
tyvarp :: P TyVar
tyvarp  = do
  char '\''
  choice [ antiblep
         , flip TV <$> (Qa <$ char '<' <|> pure Qu)
                   <*> lidp ]

oplevelp :: Prec -> P Lid
oplevelp  = liftM Lid . opP

quantp :: P Quant
quantp  = Forall <$ reserved "all"
      <|> Exists <$ reserved "ex"
      <|> antiblep

typep  :: TyTagMode i => P (Type i)
typep   = typepP precStart

typepP :: TyTagMode i => Int -> P (Type i)
typepP p
  | p == precStart
         = do
             tc <- TyQu <$> quantp
               <|> TyMu <$  reserved "mu"
             tvs <- many tyvarp
             dot
             t   <- typepP p
             return (foldr tc t tvs)
           <|> typepP (p + 1)
  | p == precArr
         = chainr1last (typepP (p + 1))
             (choice
              [ tyArrI <$ arrow,
                tyLolI <$ lolli,
                funbraces (TyArr <$> qExpp) ])
             (typepP precStart)
  | p == precPlus
         = chainl1last (typepP (p + 1))
             (tybinopp [plus]) (typepP precStart) 
  | p == precStar
         = chainl1last (typepP (p + 1))
             (tybinopp [star, slash]) (typepP precStart)
  | p == precSemi
         = chainr1last (typepP (p + 1))
             (tybinopp [semi]) (typepP precStart)
  | p == precApp -- this case ensures termination
         = tyarg >>= tyapp'
  | p <= precMax
         = typepP (p + 1)
  | otherwise
         = typepP precStart
  where
  tyarg :: TyTagMode i => P [Type i]
  tyarg  = choice
           [ parens $ antiblep <|> commaSep1 (typepP precStart),
             (:[]) <$> tyatom ]

  tyatom :: TyTagMode i => P (Type i)
  tyatom  = TyVar <$> tyvarp
        <|> TyCon <$> qlidnatp <*> pure [] <*> tytagp
        <|> antiblep
        <|> tyNulOpT (injTd tdUn) "U" <$ qualU
        <|> tyNulOpT (injTd tdAf) "A" <$ qualA

  tyapp' :: TyTagMode i => [Type i] -> P (Type i)
  tyapp' [t] = option t $ do
    tc <- qlidnatp
    i  <- tytagp
    tyapp' [TyCon tc [t] i]
  tyapp' ts  = do
                 tc <- qlidnatp
                 i  <- tytagp
                 tyapp' [TyCon tc ts i]

tybinopp :: TyTagMode i => [P String] -> P (Type i -> Type i -> Type i)
tybinopp ops = do
  op <- choice ops
  i  <- tytagp
  return (tyBinOpT i op)

progp :: TyTagMode i => P (Prog i)
progp  = choice [
           do ds <- declsp
              when (null ds) pzero
              e  <- antioptaroundp (reserved "in" `between` punit) exprp
              return (Prog ds e),
           antioptp exprp >>! Prog []
         ]

replp :: TyTagMode i => P [Decl i]
replp  = choice [
           try $ do
             ds <- declsp
             when (null ds) pzero
             eof
             return ds,
           exprp >>! (prog2decls . Prog [] . Just)
         ]

declsp :: TyTagMode i => P [Decl i]
declsp  = antiblep <|> loop
  where loop =
          choice [
            do
              d  <- declp
              ds <- loop
              return (d : ds),
            do
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

declp :: TyTagMode i => P (Decl i)
declp  = addLoc $ choice [
           do
             reserved "type"
             antilist1p (reserved "and") tyDecp >>! dcTyp,
           letp,
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
           do
             reserved "abstype"
             at <- abstysp
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

modexpp :: TyTagMode i => P (ModExp i)
modexpp  = choice [
             MeStr  <$> between (reserved "struct") (reserved "end") declsp,
             MeName <$> quidp,
             antiblep
           ]

tyDecp :: TyTagMode i => P (TyDec i)
tyDecp = do
  (arity, tvs, name) <- tyProtp
  choice [
    do
      unless (all (== Invariant) arity) pzero
      reservedOp "="
      choice [
        typep >>! TdSyn name tvs,
        altsp >>! TdDat name tvs ],
    do
      quals <- qualsp
      return (TdAbs name tvs arity quals),
    antiblep ]

tyProtp :: P ([Variance], [TyVar], Lid)
tyProtp  = choice [
  try $ do
    (v1, tv1) <- paramVp
    con <- choice [ semi, star, slash, plus ] >>! Lid
    (v2, tv2) <- paramVp
    return ([v1, v2], [tv1, tv2], con),
  do
    (arity, tvs) <- paramsVp
    name         <- lidnatp
    return (arity, tvs, name)
  ]

letp :: TyTagMode i => P (Decl i)
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
        return (Binding f (fixt t) (fixe e))
      let names    = map bnvar bindings
          namesExp = foldl1 exPair (map exBVar names)
          namesPat = foldl1 PaPair (map PaVar names)
          tempVar  = Lid "#letrec"
          decls0   = [ dcLet (PaVar tempVar) Nothing $
                         exLetRec bindings namesExp ]
          decls1   = [ dcLet (PaVar (bnvar binding)) Nothing $
                         exLet namesPat (exBVar tempVar) $
                            exBVar (bnvar binding)
                     | binding <- bindings ]
      return $ dcLoc decls0 decls1,
    do
      f <- varp
      (sigma, fixt, fixe) <- afargsp
      t <- antioptaroundp (colon `between` punit) typep
      reservedOp "="
      e <- withSigma sigma exprp
      return (dcLet (PaVar f) (fmap fixt t) (fixe e)),
    dcLet <$> pattp
          <*> antioptaroundp (colon `between` punit) typep
          <*  reservedOp "="
          <*> exprp
    ]

abstysp :: TyTagMode i => P [AbsTy i]
abstysp = antilist1p (reserved "and") $ do
  (arity, tvs, name) <- tyProtp
  quals        <- qualsp
  reservedOp "="
  alts         <- altsp
  return (AbsTy arity quals (TdDat name tvs alts))

paramsVp :: P ([Variance], [TyVar])
paramsVp  = delimList punit parens comma paramVp >>! unzip

paramVp :: P (Variance, TyVar)
paramVp = do
  v  <- variancep
  tv <- tyvarp
  return (v, tv)

variancep :: P Variance
variancep =
  choice
    [ char '+' >> return Covariant,
      char '-' >> return Contravariant,
      char '0' >> return Omnivariant,
      char '1' >> return Invariant,
      return Invariant ]

qualsp   :: P (QExp TyVar)
qualsp    = option minBound $ reserved "qualifier" *> qExpp

qExpp :: P (QExp TyVar)
qExpp  = qexp where
  qexp  = qeDisj <$> sepBy1 qterm (reservedOp "\\/")
  qterm = qeConj <$> sepBy1 qfact (reservedOp "/\\")
  qfact = parens qexp <|> qatom
  qatom = QeLit Qu <$  qualU
      <|> QeLit Qa <$  qualA
      <|> QeVar    <$> tyvarp
      <|> qeLid    <$> lidp
      <|> antiblep
  qeLid = QeVar . flip TV Qa

altsp :: TyTagMode i => P [(Uid, Maybe (Type i))]
altsp  = sepBy1 altp (reservedOp "|")

altp  :: TyTagMode i => P (Uid, Maybe (Type i))
altp   = do
  k <- uidp
  t <- optionMaybe $ do
    reserved "of"
    typep
  return (k, t)

exprp :: TyTagMode i => P (Expr i)
exprp = expr0 where
  onlyOne [x] = [x True]
  onlyOne xs  = map ($ False) xs
  expr0 = addLoc $ choice
    [ do reserved "let"
         choice
           [ do reserved "rec"
                bs <- antilist1p (reserved "and") $ do
                  x    <- varp
                  (sigma, ft, fe) <- afargsp
                  colon
                  t    <- typep
                  reservedOp "="
                  e    <- withSigma sigma expr0
                  return (Binding x (ft t) (fe e))
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
         ec <- expr0
         reserved "then"
         et <- expr0
         reserved "else"
         ef <- expr0
         return (exCase ec
                   [CaseAlt (PaCon (quid "true")  Nothing False) et,
                    CaseAlt (PaCon (quid "false") Nothing False) ef]),
      do reserved "match"
         e1 <- expr0
         reserved "with"
         choice [
           exCase e1 <$> antiblep,
           do
             optional (reservedOp "|")
             clauses <- flip sepBy1 (reservedOp "|") $
               const <$> antiblep <|> do
                 (xi, sigma, lift) <- pattbangp
                 reservedOp "->"
                 ei <- mapSigma (sigma ||) expr0
                 return (\b -> lift b CaseAlt xi ei)
             return (exCase e1 (onlyOne clauses)) ],
      do reserved "try"
         e1 <- expr0
         reserved "with"
         optional (reservedOp "|")
         clauses <- flip sepBy1 (reservedOp "|") $ do
           (xi, sigma, lift) <- pattbangp
           reservedOp "->"
           ei <- mapSigma (sigma ||) expr0
           return $
             lift False
                  (\xi' ei' ->
                     -- TODO: Make this robust to redefinition of
                     -- Left and Right
                     CaseAlt {
                       capatt = PaCon (quid "Left") (Just xi') False,
                       caexpr = ei'
                     })
                  xi ei
         let tryQ = qlid $
                      "INTERNALS.Exn.tryfun"
         return $
           exCase (exApp (exVar tryQ)
                         (exAbs PaWild (tyNulOpT (injTd tdUnit) "unit")
                            e1)) $
             CaseAlt {
               capatt = PaCon (quid "Right")
                              (Just (PaVar (Lid "x"))) False,
               caexpr = exVar (qlid "x")
             } :
             clauses ++
             [CaseAlt {
                capatt = PaCon (quid "Left")
                               (Just (PaVar (Lid "e"))) False,
                caexpr = exApp (exVar (qlid "INTERNALS.Exn.raise"))
                               (exVar (qlid "e"))
              }],
      do reserved "fun"
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
  expr7 = expr8
  expr8 = chainr1last expr9 (opappp (Right 8)) expr0
  expr9 = choice
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
  expr10 = do
    ops <- many $ addLoc $ oplevelp (Right 10) >>! exBVar
    arg <- expr11
    return (foldr exApp arg ops)
  expr11 = do
             e  <- exprA
             ts <- many . brackets $ commaSep1 typep
             return (foldl exTApp e (concat ts))
  exprA = addLoc $ choice
    [ identp          >>! exId,
      litp            >>! exLit,
      antiblep,
      parens (exprN1 <|> return (exBCon (Uid "()")))
    ]
  exprN1 = addLoc $ do
    e1 <- expr0
    choice
      [ do t1 <- antioptaroundp (colon `between` punit) typep
           reservedOp ":>"
           t2 <- typep
           return (exCast e1 t1 t2),
        do comma
           es <- commaSep1 expr0
           return (foldl exPair e1 es),
        return e1 ]

-- Parse an infix operator at given precedence
opappp :: TyTagMode i => Prec -> P (Expr i -> Expr i -> Expr i)
opappp p = do
  loc <- curLoc
  op  <- oplevelp p
  return (\e1 e2 -> (exBVar op <<@ loc `exApp` e1) `exApp` e2)

-- Zero or more of (pat:typ, ...), (), or tyvar, recognizing '|'
-- to introduce affine arrows
afargsp :: TyTagMode i => P (Bool, Type i -> Type i, Expr i -> Expr i)
afargsp = loop tyArrI where
  loop arrcon0 = do
    arrcon <- option arrcon0 $ do
      reservedOp "|"
      return tyLolI
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
argsp1 :: TyTagMode i => P (Bool, Expr i -> Expr i)
argsp1  = do
           (b, fe) <- argp
           if b
             then return (b, fe)
             else second (fe .) `fmap` option (False, id) argsp1

-- Zero or more of (pat:typ, ...), (), tyvar
argsp :: TyTagMode i => P (Bool, Expr i -> Expr i)
argsp  = option (False, id) $ do
           (b, fe) <- argp
           if b
             then return (b, fe)
             else second (fe .) `fmap` argsp

-- Parse a (pat:typ, ...), (), or tyvar
argp :: TyTagMode i => P (Bool, Expr i -> Expr i)
argp  = choice [
          do
            (_, fe)    <- tyargp
            return (False, fe),
          do
            (b, _, fe) <- vargp const
            return (b, fe)
        ]

-- Parse a (pat:typ, ...) or () argument
vargp :: TyTagMode i =>
         (Type i -> Type i -> Type i) ->
         P (Bool, Type i -> Type i, Expr i -> Expr i)
vargp arrcon = do
  loc    <- curLoc
  inBang <- bangp
  (p, t) <- paty
  return (inBang, arrcon t, condSigma inBang True (flip exAbs t) p <<@ loc)

-- Parse a (pat:typ, ...) or () argument
paty :: TyTagMode i => P (Patt, Type i)
paty  = do
  (p, mt) <- pamty
  case (p, mt) of
    (_, Just t) -> return (p, t)
    (PaCon (J [] (Uid "()")) Nothing False, Nothing)
                -> return (p, tyNulOpT (injTd tdUnit) "unit")
    _           -> pzero <?> ":"

-- Parse a (), (pat:typ, ...) or (pat) argument
pamty :: TyTagMode i => P (Patt, Maybe (Type i))
pamty  = parens $ choice
           [
             do
               (p, mt) <- pamty
               maybe (maybecolon p) (morepts p) mt,
             do
               p <- pattp
               maybecolon p,
             return (PaCon (quid "()") Nothing False, Nothing)
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
      return (foldl PaPair p0 ps, Just (foldl tyTupleI t0 ts))
    colonType p = do
      colon
      t <- typep
      return (p, t)
    tyTupleI = tyBinOpT (injTd tdTuple) "*"

-- Parse a sequence of one or more tyvar arguments
tyargp :: TyTagMode i => P (Type i -> Type i, Expr i -> Expr i)
tyargp  = do
  tvs <- liftM return loctv <|> brackets (commaSep1 loctv)
  return (\t -> foldr (\(_,   tv) -> tyAll tv) t tvs,
          \e -> foldr (\(loc, tv) -> exTAbs tv <<@ loc) e tvs)
    where
  loctv = liftM2 (,) curLoc tyvarp

pattbangp :: TyTagMode i =>
             P (Patt, Bool,
                Bool -> (Patt -> Expr i -> b) -> Patt -> Expr i -> b)
pattbangp = do
  inSigma <- getSigma
  inBang  <- bangp
  x       <- pattp
  let trans = inBang && not inSigma
      wrap  = inBang && inSigma
  return (condMakeBang wrap x, inBang, condSigma trans)

condSigma :: TyTagMode i =>
             Bool -> Bool ->
             (Patt -> Expr i -> a) ->
             Patt -> Expr i -> a
condSigma True  =
  \b f p e -> exSigma b (\p' e' -> f p' (liftUnit e')) p (dropUnit e)
condSigma False = const id

condMakeBang :: Bool -> Patt -> Patt
condMakeBang True  = makeBangPatt
condMakeBang False = id

bangp :: P Bool
bangp  = (bang >> return True) <|> return False

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
      PaCon <$> quidp
            <*> antioptp (try pattA)
            <*> isexnp,
      pattA ]
  pattA = choice
    [ PaWild <$  reserved "_",
      PaVar  <$> varp,
      PaLit  <$> litp,
      PaCon  <$> quidp
             <*> pure Nothing
             <*> isexnp,
      antiblep,
      parens pattN1
    ]
  pattN1 = do
    xs <- commaSep patt0
    case xs of
      []    -> return (PaCon (quid "()") Nothing False)
      x:xs' -> return (foldl PaPair x xs')

-- Dirty hack for specifying, in surface syntax, whether a datacon
-- pattern matches an exception.  TODO: get rid of
isexnp  :: P Bool
isexnp   = True <$ lexeme (symbol "!!!")
       <|> pure False

litp :: P Lit
litp = choice [
         integerOrFloat >>! either LtInt LtFloat,
         charLiteral    >>! (LtInt . fromIntegral . fromEnum),
         stringLiteral  >>! LtStr,
         antiblep
       ]

finish :: CharParser st a -> CharParser st a
finish p = do
  optional (whiteSpace)
  r <- p
  eof
  return r

-- | Parse a program
parseProg     :: TyTagMode i => P (Prog i)
-- | Parse a REPL line
parseRepl     :: TyTagMode i => P [Decl i]
-- | Parse a sequence of declarations
parseDecls    :: TyTagMode i => P [Decl i]
-- | Parse a declaration
parseDecl     :: TyTagMode i => P (Decl i)
-- | Parse a module expression
parseModExp   :: TyTagMode i => P (ModExp i)
-- | Parse a type declaration
parseTyDec    :: TyTagMode i => P (TyDec i)
-- | Parse a type
parseType     :: TyTagMode i => P (Type i)
-- | Parse a qualifier expression
parseQExp     :: P (QExp TyVar)
-- | Parse an expression
parseExpr     :: TyTagMode i => P (Expr i)
-- | Parse a pattern
parsePatt     :: P Patt
parseProg      = finish progp
parseRepl      = finish replp
parseDecls     = finish declsp
parseDecl      = finish declp
parseModExp    = finish modexpp
parseTyDec     = finish tyDecp
parseType      = finish typep
parseQExp      = finish qExpp
parseExpr      = finish exprp
parsePatt      = finish pattp

-- Convenience functions for quick-and-dirty parsing:

-- | Parse a program
pp  :: String -> Prog ()
pp   = makeQaD parseProg

-- | Parse a sequence of declarations
pds :: String -> [Decl ()]
pds  = makeQaD parseDecls

-- | Parse a declaration
pd  :: String -> Decl ()
pd   = makeQaD parseDecl

pme :: String -> ModExp ()
pme  = makeQaD parseModExp

-- | Parse a type declaration
ptd :: String -> TyDec ()
ptd  = makeQaD parseTyDec

-- | Parse a type
pt  :: String -> Type ()
pt   = makeQaD parseType

-- | Parse a qualifier expression
pqe :: String -> QExp TyVar
pqe  = makeQaD parseQExp

-- | Parse an expression
pe  :: String -> Expr ()
pe   = makeQaD parseExpr

-- | Parse a pattern
px  :: String -> Patt
px   = makeQaD parsePatt

makeQaD :: P a -> String -> a
makeQaD parser =
  either (error . show) id . runParser parser state0 "<string>"
