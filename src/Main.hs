-- | The main driver program, which performs all manner of unpleasant
--   tasks to tie everything together
{-# LANGUAGE CPP #-}
module Main (
  main
) where

import Util
import Syntax.Ppr (Doc, Ppr(..), (<+>), (<>), text, char, hang,
            ($$), nest, printDoc, hPrintDoc)
import qualified Syntax.Ppr
import Syntax.Parser (parseFile, REPLCommand(..), parseCommand)
import Syntax.Prec (precOp)
import Paths (findAlmsLib, findAlmsLibRel, versionString, shortenPath)
import Printing (addTyNameContext)
import Rename (RenameState, runRenamingM, renameDecls, renameProg,
               getRenamingInfo, RenamingInfo(..))
import Statics (tcProg, tcDecls, S, runTC, runTCNew, Module(..),
                getExnParam, tyConToDec, getVarInfo, getTypeInfo,
                getConInfo)
import Coercion (translate, translateDecls, TEnv, tenv0)
import Value (VExn(..), vppr)
import Dynamics (eval, addDecls, E, NewValues)
import Basis (primBasis, srcBasis)
import BasisUtils (basis2venv, basis2tenv, basis2renv)
import AST (Prog, Decl, TyDec, BIdent(..), prog2decls,
               Ident, Raw, Renamed)
import Env (empty, (=..=))
import Data.Loc (isBogus, initial, bogus)
import qualified ErrorMessage as EM
import qualified Message.AST  as Msg

import Prelude ()
import Data.Char (isSpace)
import System.Exit (exitFailure)
import System.Environment (getArgs, getProgName, withProgName, withArgs)
import System.IO.Error (ioeGetErrorString, isUserError)
import IO (hPutStrLn, hFlush, stdout, stderr)
import qualified Control.Exception as Exn

#ifdef USE_READLINE
import qualified USE_READLINE as RL
#endif

data Option = Don'tExecute
            | Don'tCoerce
            | NoBasis
            | Verbose
            | Quiet
            | LoadFile String
            | NoLineEdit
  deriving Eq

-- | The main procedure
main :: IO ()
main  = do
  args <- getArgs
  processArgs [] args $ \opts mmsrc filename -> do
  (primBasis', r0) <- basis2renv primBasis
  g0 <- basis2tenv primBasis'
  e0 <- basis2venv primBasis'
  case mmsrc of
    Nothing | Quiet `notElem` opts -> hPutStrLn stderr versionString
    _ -> return ()
  let st0 = RS r0 g0 tenv0 e0
  st1 <- if NoBasis `elem` opts
           then return st0
           else findAlmsLib srcBasis >>= tryLoadFile st0 srcBasis
  st2 <- foldM (\st n -> findAlmsLibRel n "." >>= tryLoadFile st n)
               st1 (reverse [ name | LoadFile name <- opts ])
  maybe interactive (batch filename) mmsrc (`elem` opts) st2
    `handleExns` (st2, exitFailure)

tryLoadFile :: ReplState -> String -> Maybe String -> IO ReplState
tryLoadFile st name mfile = case mfile of
  Nothing -> do
    carp $ name ++ ": could not load"
    return st
  Just file -> loadFile st file

loadFile :: ReplState -> String -> IO ReplState
loadFile st name = do
    src   <- readFile name
    name' <- shortenPath name
    loadString st name' src

loadString :: ReplState -> String -> String -> IO ReplState
loadString st name src = do
  case parseFile name src of
    Left e     -> Exn.throwIO e
    Right ast0 -> do
      (st1, ast1)    <- renaming (st, prog2decls (ast0 :: Prog Raw))
      (st2, _, ast2) <- statics False (st1, ast1)
      (st3, ast3)    <- translation (st2, ast2)
      (st4, _)       <- dynamics (st3, ast3)
      return st4

batch :: String -> IO String -> (Option -> Bool) -> ReplState -> IO ()
batch filename msrc opt st0 = do
      src <- msrc
      case parseFile filename src of
        Left e    -> Exn.throwIO e
        Right ast -> rename ast where
          rename  :: Prog Raw     -> IO ()
          check   :: Prog Renamed -> IO ()
          coerce  :: Prog Renamed -> IO ()
          execute :: Prog Renamed -> IO ()

          rename ast0 = do
            (ast1, _) <- runRenamingM True (initial filename)
                                      (rsRenaming st0) (renameProg ast0)
            check ast1

          check ast0 = do
            ((t, ast1), _) <- runTC (rsStatics st0) (tcProg ast0)
            when (opt Verbose) $
              mumble "TYPE" t
            coerce ast1

          coerce ast1 =
            if opt Don'tCoerce
              then execute ast1
              else do
                let ast2 = translate (rsTranslation st0) ast1
                when (opt Verbose) $
                  mumble "TRANSLATION" ast2
                execute ast2

          execute ast2 =
            unless (opt Don'tExecute) $ do
              v <- eval (rsDynamics st0) ast2
              when (opt Verbose) $
                mumble "RESULT" v

data ReplState = RS {
  rsRenaming    :: RenameState,
  rsStatics     :: S,
  rsTranslation :: TEnv,
  rsDynamics    :: E
}

renaming    :: (ReplState, [Decl Raw]) -> IO (ReplState, [Decl Renamed])
statics     :: Bool -> (ReplState, [Decl Renamed]) ->
               IO (ReplState, Module, [Decl Renamed])
translation :: (ReplState, [Decl Renamed]) -> IO (ReplState, [Decl Renamed])
dynamics    :: (ReplState, [Decl Renamed]) -> IO (ReplState, NewValues)

renaming (st, ast) = do
  (ast', r') <- runRenamingM True (initial "-")
                             (rsRenaming st) (renameDecls ast)
  return (st { rsRenaming = r' }, ast')

statics _ (rs, ast) = do
  (ast', new, s') <- runTCNew (rsStatics rs) (tcDecls ast)
  return (rs { rsStatics = s' }, new, ast')

translation (rs, ast) = do
  let (menv', ast') = translateDecls (rsTranslation rs) ast
  return (rs { rsTranslation = menv' }, ast')

dynamics (rs, ast) = do
  (e', new) <- addDecls (rsDynamics rs) ast
  return (rs { rsDynamics = e' }, new)

carp :: String -> IO ()
carp msg = do
  prog <- getProgName
  hPutStrLn stderr (prog ++ ": " ++ msg)

handleExns :: IO a -> (ReplState, IO a) -> IO a
handleExns body (st, handler) =
  body
    `Exn.catches`
    [ Exn.Handler $ \e@(VExn { }) -> do
        prog <- getProgName
        continue $ EM.AlmsError
                     (EM.OtherError ("Uncaught exception"))
                     bogus
                     (Msg.Table [
                        ("in program:", Msg.Exact prog),
                        ("exception:", Msg.Printable (-1) (vppr e))
                     ]),
      Exn.Handler continue,
      Exn.Handler $ \err ->
        continue $ EM.AlmsError EM.DynamicsPhase bogus $
          Msg.Flow [Msg.Words (errorString err)],
      Exn.Handler $ \(Exn.SomeException err) ->
        continue $ EM.AlmsError EM.DynamicsPhase bogus $
          Msg.Flow [Msg.Words (show err)] ]
  where
    continue err = do
      hPrintDoc stderr (withRS st (ppr (err :: EM.AlmsError)))
      handler

interactive :: (Option -> Bool) -> ReplState -> IO ()
interactive opt rs0 = do
  initialize
  repl 1 rs0
  where
    repl row st = do
      mres <- reader row st
      case mres of
        Nothing  -> return ()
        Just (row', ast) -> do
          st' <- doLine st ast
                   `handleExns` (st, return st)
          repl row' st'
    doLine st ast = let
      rename  :: (ReplState, [Decl Raw]) -> IO ReplState
      check   :: (ReplState, [Decl Renamed]) -> IO ReplState
      coerce  :: Module -> (ReplState, [Decl Renamed]) -> IO ReplState
      execute :: Module -> (ReplState, [Decl Renamed]) -> IO ReplState
      display :: Module -> NewValues -> ReplState -> IO ReplState

      rename (st0, ast0) = do
        renaming (st0, ast0) >>= check

      check stast0   = do
                         (st1, newDefs, ast1) <- statics True stast0
                         coerce newDefs (st1, ast1)

      coerce newDefs stast1
                     = if opt Don'tCoerce
                         then execute newDefs stast1
                         else do
                           stast2 <- translation stast1
                           when (opt Verbose) $
                             mumbles "TRANSLATION" (snd stast2)
                           execute newDefs stast2

      execute newDefs stast2
                          = if opt Don'tExecute
                              then display newDefs empty (fst stast2)
                              else do
                                (st3, newVals) <- dynamics stast2
                                display newDefs newVals st3

      display newDefs newVals st3
                          = do printResult st3 newDefs newVals
                               return st3

      in rename (st, ast)
    say    = if opt Quiet then const (return ()) else printDoc
    getln' = if opt NoLineEdit then getline else readline
    getln  = if opt Quiet then const (getln' "") else getln'
    reader :: Int -> ReplState -> IO (Maybe (Int, [Decl Raw]))
    reader row st = loop 1 []
      where
        fixup = unlines . mapTail ("   " ++) . reverse
        loop count acc = do
          mline <- getln (if null acc then "#- " else "#= ")
          case (mline, acc) of
            (Nothing, [])        -> return Nothing
            (Nothing, (_,err):_) -> do
              addHistory (fixup (map fst acc))
              hPutStrLn stderr ""
              hPutStrLn stderr (show err)
              reader (row + count) st
            (Just line, _)
              | all isSpace line -> loop count acc
              | otherwise        ->
              let cmd = fixup (line : map fst acc) in
              case parseCommand row line cmd of
                GetInfoCmd ids -> do
                  mapM_ (printInfo st) ids
                  addHistory line
                  loop (count + 1) acc
                GetPrecCmd lids -> do
                  mapM_ printPrec lids
                  addHistory line
                  loop (count + 1) acc
                DeclsCmd ast -> do
                  addHistory cmd
                  return (Just (row + count, ast))
                ParseError derr -> 
                  loop (count + 1) ((line, derr) : acc)
    printResult :: ReplState -> Module -> NewValues -> IO ()
    printResult st md00 values = say (withRS st (loop True md00)) where
      loop tl md0 = case md0 of
        MdNil               -> mempty
        MdApp md1 md2       -> loop tl md1 $$ loop tl md2
        MdValue (Var l) t   -> pprValue tl l t (values =..= l)
        MdValue (Con u) t   -> case getExnParam t of
          Nothing        -> mempty
          Just Nothing   -> text "exception"<+>ppr u
          Just (Just t') -> text "exception"<+>ppr u<+>text "of"<+>ppr t'
        MdTycon _ tc        ->
          text "type" <+>
          Ppr.askTyNames (\tn -> ppr (tyConToDec tn tc :: TyDec Renamed))
        MdModule u md1      -> Ppr.enterTyNames u $
          text "module" <+> ppr u <+> char ':' <+> text "sig"
          $$ nest 2 (loop False md1)
          $$ text "end"
        MdSig u md1         ->
          text "module type" <+> ppr u <+> char '=' <+> text "sig"
          $$ nest 2 (loop False md1)
          $$ text "end"
      pprValue tl x t mv =
        addHang '=' (if tl then fmap ppr mv else Nothing) $
          addHang ':' (Just (ppr t)) $
            (if tl then ppr x else text "val" <+> ppr x)
      addHang c m d = case m of
        Nothing -> d
        Just t  -> hang (d <+> char c) 2 t

printInfo :: ReplState -> Ident Raw -> IO ()
printInfo st ident = case getRenamingInfo ident (rsRenaming st) of
    []  -> putStrLn $ "Not bound: ‘" ++ show ident ++ "’"
    ris -> mapM_ each ris
  where
    each (SigAt      loc x') =
      mention "module type" (ppr x') mempty loc
    each (ModuleAt   loc x') =
      mention "module" (ppr x') mempty loc
    each (VariableAt loc x') =
      case getVarInfo x' s of
        Nothing  -> mention "val" (ppr x') mempty loc
        Just t   -> mention "val" (ppr x') (char ':' <+> ppr t) loc
    each (TyconAt    loc x') =
      case getTypeInfo x' s of
        Nothing  -> mention "type" (ppr x') mempty loc
        Just tc  -> mention "type" mempty (ppr tc) loc
    each (DataconAt  loc x') =
      case getConInfo x' s of
        Nothing -> mention "val" (ppr x') mempty loc
        Just (Left mt) ->
          mention "type" (text "exn")
                  (Ppr.sep [ text "= ...",
                             char '|' <+> ppr x' <+>
                             case mt of
                               Nothing -> mempty
                               Just t  -> text "of" <+> ppr t ])
                  loc
        Just (Right tc) ->
          mention "type" mempty (ppr tc) loc
    --
    s = rsStatics st
    --
    mention what who rhs loc = do
      printDoc $
        withRS st $
          text what <+> ppr who
            >?> rhs Ppr.>?>
              if isBogus loc
                then text "  -- built-in"
                else text "  -- defined at" <+> text (show loc)
      where a >?> b = Ppr.ifEmpty who (a <+> b) (a Ppr.>?> b)

-- Add the ReplState to the pretty-printing context.
withRS :: ReplState -> Doc -> Doc
withRS rs = addTyNameContext (rsRenaming rs) (rsStatics rs)

printPrec :: String -> IO ()
printPrec oper = printDoc $
  hang (text oper)
       2
       (text ":" <+> text (show (precOp oper)))

mumble ::  Ppr a => String -> a -> IO ()
mumble s a = printDoc $ hang (text s <> char ':') 2 (ppr a)

mumbles :: Ppr a => String -> [a] -> IO ()
mumbles s as = printDoc $ hang (text s <> char ':') 2 (Ppr.vcat (map ppr as))

errorString :: IOError -> String
errorString e | isUserError e = ioeGetErrorString e
              | otherwise     = show e

processArgs :: [Option] -> [String] ->
               ([Option] -> Maybe (IO String) -> String -> IO a) ->
               IO a
processArgs opts0 args0 k = loop opts0 args0 where
  loop opts []          = go "-" [] opts Nothing
  loop opts ("-":args)
                        = go "-" args opts (Just getContents)
  loop opts ("--":name:args) 
                        = go name args opts (Just (readFile name))
  loop opts ("-l":name:r)
                        = loop (LoadFile name:opts) r
  loop opts (('-':'l':name):r)
                        = loop (LoadFile name:opts) r
  loop opts ("-b":r)    = loop (NoBasis:opts) r
  loop opts ("-x":r)    = loop (Don'tExecute:opts) r
  loop opts ("-c":r)    = loop (Don'tCoerce:opts) r
  loop opts ("-v":r)    = loop (Verbose:opts) r
  loop opts ("-q":r)    = loop (Quiet:opts) r
  loop opts ("-e":r)    = loop (NoLineEdit:opts) r
  loop opts (('-':c:d:e):r)
                        = loop opts (['-',c]:('-':d:e):r)
  loop _    (('-':_):_) = usage
  loop opts (name:args) = go name args opts (Just (readFile name))

  go name args opts mmsrc =
    withProgName name $
      withArgs args $
        k opts mmsrc name

usage :: IO a
usage  = do
  hPutStrLn stderr "Usage: alms [OPTIONS...] [--] [FILENAME] [ARGS...]"
  hPutStrLn stderr ""
  hPutStrLn stderr "Options:"
  hPutStrLn stderr "  -l FILE  Load file"
  hPutStrLn stderr "  -q       Don't print prompt, greeting, responses"
  hPutStrLn stderr "  -e       Don't use line editing"
  hPutStrLn stderr ""
  hPutStrLn stderr "Debugging options:"
  hPutStrLn stderr "  -b       Don't load libbasis.alms"
  hPutStrLn stderr "  -c       Don't add contracts"
  hPutStrLn stderr "  -x       Don't execute"
  hPutStrLn stderr "  -v       Verbose (show translation, results, types)"
  exitFailure

initialize :: IO ()
addHistory :: String -> IO ()
readline   :: String -> IO (Maybe String)

#ifdef USE_READLINE
initialize   = RL.initialize
addHistory   = RL.addHistory
readline     = RL.readline
#else
initialize   = return ()
addHistory _ = return ()
readline     = getline
#endif

getline    :: String -> IO (Maybe String)
getline s   = do
  putStr s
  hFlush stdout
  catch (fmap Just getLine) (\_ -> return Nothing)
