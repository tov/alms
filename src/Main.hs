-- | The main driver program, which performs all manner of unpleasant
--   tasks to tie everything together
module Main (
  main,
  -- * For interactive exploration from GHCi
  makeRS0, check,
) where

import Util
import Util.MonadRef
import Util.UndoIO
import Syntax.ImplicitThreading
import Syntax.Ppr (Doc, Ppr(..), (<+>), (<>), text, char, hang,
                   printDoc, hPrintDoc)
import qualified Syntax.Ppr as Ppr
import Syntax.Parser (parseFile, REPLCommand(..), parseCommand)
import Syntax.Prec (precOp)
import Paths (findAlmsLib, findAlmsLibRel, versionString, shortenPath)
import Meta.Quasi
import Statics
import Value (VExn(..), vppr)
import Dynamics (eval, addDecls, E, NewValues)
import Basis (primBasis, srcBasis)
import BasisUtils (basis2venv, basis2tenv, basis2renv)
import qualified AST
import AST (Prog, Decl, SigItem, prog2decls,
               Ident, Raw, Renamed)
import Env (empty, (=..=))
import Error
import qualified Message.AST  as Msg
import Type.Ppr (TyConInfo(..))

import Prelude ()
import Data.Char (isSpace)
import Data.List (nub)
import Data.IORef (IORef)
import System.Exit (exitFailure, exitSuccess, ExitCode)
import System.Environment (getArgs, getProgName, withProgName, withArgs)
import System.IO.Error (ioeGetErrorString, isUserError)
import System.IO (hPutStrLn, hFlush, stdout, stderr)
import qualified Control.Exception as Exn

#ifdef USE_READLINE
import qualified USE_READLINE as RL
#endif

data Option = Don'tExecute
            | NoBasis
            | Verbose
            | Quiet
            | LoadFile String
            | NoLineEdit
  deriving Eq

data ReplState = RS {
  rsStatics     :: StaticsState IORef,
  rsDynamics    :: E
}

instance Show ReplState where showsPrec = showsPrec <$.> rsStatics

-- | The main procedure
main :: IO ()
main  = do
  args <- getArgs
  processArgs [] args $ \opts mmsrc filename -> do
  st0 <- makeRS0
  case mmsrc of
    Nothing | Quiet `notElem` opts -> hPutStrLn stderr versionString
    _ -> return ()
  st1 <- (if NoBasis `elem` opts
            then return st0
            else findAlmsLib srcBasis >>= tryLoadFile st0 srcBasis)
    `handleExns` (st0, exitFailure)
  st2 <- foldM (\st n -> findAlmsLibRel n "." >>= tryLoadFile st n)
               st1 (reverse [ name | LoadFile name <- opts ])
    `handleExns` (st1, exitFailure)
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

makeRS0 :: IO ReplState
makeRS0  = do
  (primBasis', r0) <- basis2renv primBasis
  g0 <- basis2tenv (staticsState0 r0) primBasis'
  e0 <- basis2venv primBasis'
  return (RS g0 e0)

-- For trying things from GHCi
check :: ReplState -> String -> IO ReplState
check rs = loadString rs "<check>"

loadString :: ReplState -> String -> String -> IO ReplState
loadString st name src = do
  case parseFile name src of
    Left e     -> Exn.throwIO e
    Right ast  -> do
      ast1           <- runAlmsErrorIO (mapM threadDecl (prog2decls ast))
      (st2, _, ast2) <- runAlmsErrorIO (statics (st, ast1))
      (st3, _)       <- dynamics (st2, ast2)
      return st3

batch :: String -> IO String -> (Option -> Bool) -> ReplState -> IO ()
batch filename msrc opt st = do
      src <- msrc
      case parseFile filename src of
        Left e    -> Exn.throwIO e
        Right ast -> thread ast where
          thread    :: Prog Raw -> IO ()
          typecheck :: Prog Raw -> IO ()
          execute   :: Prog Renamed -> IO ()

          thread ast0 = do
            ast1 <- runAlmsErrorIO (threadProg ast0)
            when (opt Verbose) $
              mumble "THREADING" ast1
            typecheck ast1

          typecheck ast1 = do
            (ast2, mt) <- runAlmsErrorIO (typeCheckProg (rsStatics st) ast1)
            when (opt Verbose) $
              mumble "TYPE" mt
            execute ast2

          execute ast2 =
            unless (opt Don'tExecute) $ do
              v <- eval (rsDynamics st) ast2
              when (opt Verbose) $
                mumble "RESULT" v

statics     :: (MonadRef IORef m, MonadAlmsError m) ⇒
               (ReplState, [Decl Raw]) ->
               m (ReplState, [SigItem Renamed], [Decl Renamed])
dynamics    :: (ReplState, [Decl Renamed]) -> IO (ReplState, NewValues)

statics (rs, ast) = do
  (ast', sig, s') <- typeCheckDecls (rsStatics rs) ast
  return (rs { rsStatics = s' }, sig, ast')

dynamics (rs, ast) = do
  (e', new) <- addDecls (rsDynamics rs) ast
  return (rs { rsDynamics = e' }, new)

carp :: String -> IO ()
carp message = do
  prog <- getProgName
  hPutStrLn stderr (prog ++ ": " ++ message)

handleExns :: IO a -> (ReplState, IO a) -> IO a
handleExns body (st, handler) =
  body
    `Exn.catches`
    [ Exn.Handler $ \(e ∷ ExitCode) -> Exn.throwIO e,
      Exn.Handler $ \e@(VExn { }) -> do
        prog <- getProgName
        continue1 $
          AlmsError
            (OtherError ("Uncaught exception"))
            bogus
            (Msg.Table [
               ("in program:", Msg.Exact prog),
               ("exception:", Msg.Printable (-1) (vppr e))
          ]),
      Exn.Handler continue1,
      Exn.Handler continue,
      Exn.Handler $ \err ->
        continue1 $ AlmsError DynamicsPhase bogus $
          Msg.Flow [Msg.Words (errorString err)],
      Exn.Handler $ \(Exn.SomeException err) ->
        continue1 $ AlmsError DynamicsPhase bogus $
          Msg.Flow [Msg.Words (show err)] ]
  where
    continue1 err = continue (AlmsErrorIO [err])
    continue errs = do
      for (nub (unAlmsErrorIO errs)) $ \err -> do
        hPrintDoc stderr (withRS st (ppr err))
        hPutStrLn stderr ""
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
          st' <- doLine st ast `handleExns` (st, return st)
          repl row' st'
    doLine st ast = do
      ast1                 <- runAlmsErrorIO (threadDecls ast)
      when (opt Verbose) (mumble "THREADING" ast1)
      (st2, newDefs, ast2) <- runUndoIO (runAlmsErrorIO (statics (st, ast1)))
      (st3, newVals)       <- if opt Don'tExecute
                              then return (st2, empty)
                              else dynamics (st2, ast2)
      printResult newDefs newVals
      return st3
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
                GetConstraintCmd -> do
                  say (getConstraint (rsStatics st))
                  addHistory line
                  loop (count + 1) acc
                QuitCmd -> exitSuccess
                DeclsCmd ast -> do
                  addHistory cmd
                  return (Just (row + count, ast))
                ParseError derr -> 
                  loop (count + 1) ((line, derr) : acc)
    printResult :: [SigItem Renamed] -> NewValues -> IO ()
    printResult types values = mapM_ (say . eachItem) types
      where
      eachItem sigitem = case sigitem of
        [sgQ| val $vid:n : $t |]
          → addHang '=' (ppr <$> values =..= n) $
              addHang ':' (Just (ppr t)) $
                ppr n
        _ → ppr sigitem
      addHang c m d = case m of
        Nothing -> d
        Just t  -> hang (d <+> char c) 2 t

printInfo :: ReplState -> Ident Raw -> IO ()
printInfo st ident = case getRenamingInfo ident s of
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
        Just tc  -> mention "type" mempty (ppr (TyConInfo tc)) loc
    each (DataconAt  loc x') =
      case getConInfo x' s of
        Nothing -> mention "val" (ppr x') mempty loc
        Just (Left tc) ->
          mention "type" mempty (ppr (TyConInfo tc)) loc
        Just (Right mt) ->
          mention "type" (text "exn")
                  (Ppr.sep [ text "= ...",
                             char '|' <+> ppr x' <+>
                             case mt of
                               Nothing -> mempty
                               Just t  -> text "of" <+> ppr t ])
                  loc
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
withRS = addTyNameContext . rsStatics

printPrec :: String -> IO ()
printPrec oper = printDoc $
  hang (text oper)
       2
       (text ":" <+> text (show (precOp oper)))

mumble ::  Ppr a => String -> a -> IO ()
mumble s a = printDoc $ hang (text s <> char ':') 2 (ppr a)

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
  hPutStrLn stderr "  -x       Don't execute"
  hPutStrLn stderr "  -v       Verbose (show results, types)"
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
