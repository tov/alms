-- | The main driver program, which performs all manner of unpleasant
--   tasks to tie everything together
module Main (
  main
) where

import Util
import Syntax.Ppr (Doc, Ppr(..), (<+>), (<>), text, char, hang,
                   printDoc, hPrintDoc)
import qualified Syntax.Ppr as Ppr
import Syntax.Parser (parseFile, REPLCommand(..), parseCommand)
import Syntax.Prec (precOp)
import Paths (findAlmsLib, findAlmsLibRel, versionString, shortenPath)
{-
import Printing (addTyNameContext)
-}
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
import qualified Error as E
import qualified Message.AST  as Msg
import Type.Ppr (TyConInfo(..))

import Prelude ()
import Data.Char (isSpace)
import Data.IORef (IORef)
import System.Exit (exitFailure)
import System.Environment (getArgs, getProgName, withProgName, withArgs)
import System.IO.Error (ioeGetErrorString, isUserError)
import IO (hPutStrLn, hFlush, stdout, stderr)
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

-- | The main procedure
main :: IO ()
main  = do
  args <- getArgs
  processArgs [] args $ \opts mmsrc filename -> do
  (primBasis', r0) <- basis2renv primBasis
  g0 <- basis2tenv (staticsState0 r0) primBasis'
  e0 <- basis2venv primBasis'
  case mmsrc of
    Nothing | Quiet `notElem` opts -> hPutStrLn stderr versionString
    _ -> return ()
  let st0 = RS g0 e0
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
    Right ast  -> do
      (st', _, ast') <- E.runAlmsErrorIO (statics (st, prog2decls ast))
      (st'', _)      <- dynamics (st', ast')
      return st''

batch :: String -> IO String -> (Option -> Bool) -> ReplState -> IO ()
batch filename msrc opt st0 = do
      src <- msrc
      case parseFile filename src of
        Left e    -> Exn.throwIO e
        Right ast -> check ast where
          check   :: Prog Raw -> IO ()
          execute :: Prog Renamed -> IO ()

          check ast0 = do
            (ast1, mt) <- typeCheckProg (rsStatics st0) ast0
            when (opt Verbose) $
              mumble "TYPE" mt
            execute ast1

          execute ast2 =
            unless (opt Don'tExecute) $ do
              v <- eval (rsDynamics st0) ast2
              when (opt Verbose) $
                mumble "RESULT" v

statics     :: (ReplState, [Decl Raw]) ->
               E.AlmsErrorT IO (ReplState, [SigItem Renamed], [Decl Renamed])
dynamics    :: (ReplState, [Decl Renamed]) -> IO (ReplState, NewValues)

statics (rs, ast) = do
  (ast', sig, s') <- typeCheckDecls (rsStatics rs) ast
  return (rs { rsStatics = s' }, sig, ast')

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
        continue1 $
          E.AlmsError
            (E.OtherError ("Uncaught exception"))
            bogus
            (Msg.Table [
               ("in program:", Msg.Exact prog),
               ("exception:", Msg.Printable (-1) (vppr e))
          ]),
      Exn.Handler continue1,
      Exn.Handler continue,
      Exn.Handler $ \err ->
        continue1 $ E.AlmsError E.DynamicsPhase bogus $
          Msg.Flow [Msg.Words (errorString err)],
      Exn.Handler $ \(Exn.SomeException err) ->
        continue1 $ E.AlmsError E.DynamicsPhase bogus $
          Msg.Flow [Msg.Words (show err)] ]
  where
    continue1 err = continue (E.AlmsErrorIO [err])
    continue errs = do
      for (E.unAlmsErrorIO errs) $ \err -> do
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
          st' <- E.runAlmsErrorIO (doLine st ast)
                   `handleExns` (st, return st)
          repl row' st'
    doLine st0 ast0 = let
      check   :: ReplState -> [Decl Raw] ->
                 E.AlmsErrorT IO ReplState
      execute :: [SigItem Renamed] -> ReplState -> [Decl Renamed] ->
                 IO ReplState
      display :: [SigItem Renamed] -> NewValues -> ReplState ->
                 IO ReplState

      check st ast        = do
                         (st', newDefs, ast') <- statics (st, ast)
                         liftIO (execute newDefs st' ast')

      execute newDefs st ast
                          = if opt Don'tExecute
                              then display newDefs empty st
                              else do
                                (st', newVals) <- dynamics (st, ast)
                                display newDefs newVals st'

      display newDefs newVals st
                          = do printResult newDefs newVals
                               return st

      in check st0 ast0
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
withRS _  = id
{- XXX
withRS rs = addTyNameContext (rsRenaming rs) (rsStatics rs)
-}

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
