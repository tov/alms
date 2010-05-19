-- | The main driver program, which performs all manner of unpleasant
--   tasks to tie everything together
{-# LANGUAGE CPP #-}
module Main (
  main
) where

import Util
import Ppr (Ppr(..), (<+>), (<>), text, char, hang, ($$), nest)
import qualified Ppr
import Parser (parse, parseRepl, parseProg)
import Paths (findAlmsLib, findAlmsLibRel, versionString)
import Rename (RenameState, runRenamingM, renameDecls, renameProg)
import Statics (tcProg, tcDecls, S, runTC, runTCNew, Module(..), tyConToDec)
import Coercion (translate, translateDecls, TEnv, tenv0)
import Value (VExn(..), vppr)
import Dynamics (eval, addDecls, E, NewValues)
import Basis (primBasis, srcBasis)
import BasisUtils (basis2venv, basis2tenv, basis2renv)
import Syntax (Prog, Decl, TyDec, BIdent(..), prog2decls,
               Raw, Renamed)
import Env (empty, (=..=))

import System.Exit (exitFailure)
import System.Environment (getArgs, getProgName, withProgName, withArgs)
import System.IO.Error (ioeGetErrorString, isUserError)
import IO (hPutStrLn, stderr)
import qualified Control.Exception as Exn

#ifdef USE_READLINE
import qualified USE_READLINE as RL
#else
import IO (hFlush, stdout)
#endif

data Option = Don'tExecute
            | Don'tCoerce
            | NoBasis
            | Verbose
            | Quiet
            | LoadFile String
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
  st2 <- foldM (\st n -> findAlmsLibRel n "-" >>= tryLoadFile st n)
               st1 (reverse [ name | LoadFile name <- opts ])
  maybe interactive (batch filename) mmsrc (`elem` opts) st2
    `handleExns` exitFailure

tryLoadFile :: ReplState -> String -> Maybe String -> IO ReplState
tryLoadFile st name mfile = case mfile of
  Nothing -> do
    carp $ name ++ ": could not load"
    return st
  Just file -> loadFile st file

loadFile :: ReplState -> String -> IO ReplState
loadFile st name = readFile name >>= loadString st name

loadString :: ReplState -> String -> String -> IO ReplState
loadString st name src = do
  case parse parseProg name src of
    Left e     -> fail $ show e
    Right ast0 -> do
      (st1, ast1)    <- renaming (st, prog2decls (ast0 :: Prog Raw))
      (st2, _, ast2) <- statics False (st1, ast1)
      (st3, ast3)    <- translation (st2, ast2)
      (st4, _)       <- dynamics (st3, ast3)
      return st4

batch :: String -> IO String -> (Option -> Bool) -> ReplState -> IO ()
batch filename msrc opt st0 = do
      src <- msrc
      case parse parseProg filename src of
        Left e    -> fail $ show e
        Right ast -> rename ast where
          rename  :: Prog Raw     -> IO ()
          check   :: Prog Renamed -> IO ()
          coerce  :: Prog Renamed -> IO ()
          execute :: Prog Renamed -> IO ()

          rename ast0 = do
            (ast1, _) <- runRenamingM True (rsRenaming st0) (renameProg ast0)
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
  (ast', r') <- runRenamingM True (rsRenaming st) (renameDecls ast)
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

handleExns :: IO a -> IO a -> IO a
handleExns body handler =
  (body
    `Exn.catch`
      \e@(VExn { }) -> do
        prog <- getProgName
        hPutStrLn stderr .
          show $
            hang (text (prog ++ ": Uncaught exception:"))
                 2
                 (vppr e)
        handler)
    `Exn.catch`
      \err -> do
        hPutStrLn stderr (errorString err)
        handler

interactive :: (Option -> Bool) -> ReplState -> IO ()
interactive opt rs0 = do
  initialize
  repl rs0
  where
    repl st = do
      mast <- reader
      case mast of
        Nothing  -> return ()
        Just ast -> do
          st' <- doLine st ast
                   `handleExns` return st
          repl st'
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
                              then display newDefs (empty, []) (fst stast2)
                              else do
                                (st3, newVals) <- dynamics stast2
                                display newDefs newVals st3

      display newDefs newVals st3
                          = do printResult newDefs newVals
                               return st3

      in rename (st, ast)
    quiet  = opt Quiet
    say    = if quiet then const (return ()) else print
    get    = if quiet then const (readline "") else readline
    reader = loop []
      where
        loop acc = do
          mline <- get (if null acc then "#- " else "#= ")
          case (mline, acc) of
            (Nothing, [])        -> return Nothing
            (Nothing, (_,err):_) -> do
              addHistory (unlines (reverse (map fst acc)))
              hPutStrLn stderr ""
              hPutStrLn stderr (show err)
              reader
            (Just "", _)         -> loop acc
            (Just line, _)       ->
              let cmd = unlines (reverse (line : map fst acc)) in
                case parse parseRepl "-" cmd of
                  Right ast -> do
                    addHistory cmd
                    return (Just ast)
                  Left derr ->
                    loop ((line, derr) : acc)
    printResult :: Module -> NewValues -> IO ()
    printResult md00 (values, _exns) = say (loop True md00) where
      loop tl md0 = case md0 of
        MdNil               -> Ppr.empty
        MdApp md1 md2       -> loop tl md1 $$ loop tl md2
        MdValue (Var l) t   -> pprValue tl l t (values =..= l)
        MdValue (Con _u) _t -> Ppr.empty -- exception?
        MdTycon _ tc        ->
          text "type" <+> ppr (tyConToDec tc :: TyDec Renamed)
        MdModule u md1      ->
          text "module" <+> ppr u <+> char ':' <+> text "sig"
          $$ nest 2 (loop False md1)
          $$ text "end"
      pprValue tl x t mv =
        addHang '=' (if tl then fmap ppr mv else Nothing) $
          addHang ':' (Just (ppr t)) $
            (if tl then ppr x else text "val" <+> ppr x)
      addHang c m d = case m of
        Nothing -> d
        Just t  -> hang (d <+> char c) 2 t
    {-
      pprExn (ExnId { eiName = u, eiParam = Just t })
        = text "exception" <+> ppr u <+> text "of" <+> ppr t
      pprExn (ExnId { eiName = u})
        = text "exception" <+> ppr u
    -}

mumble ::  Ppr a => String -> a -> IO ()
mumble s a = print $ hang (text s <> char ':') 2 (ppr a)

mumbles :: Ppr a => String -> [a] -> IO ()
mumbles s as = print $ hang (text s <> char ':') 2 (Ppr.vcat (map ppr as))

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
  hPutStrLn stderr ""
  hPutStrLn stderr "Debugging options:"
  hPutStrLn stderr "  -b       Don't load libbasis.alms"
  hPutStrLn stderr "  -c       Don't add contracts"
  hPutStrLn stderr "  -x       Don't execute"
  hPutStrLn stderr "  -v       Verbose (show translation, results, types)"
  exitFailure

initialize :: IO ()
readline   :: String -> IO (Maybe String)
addHistory :: String -> IO ()

#ifdef USE_READLINE
initialize   = RL.initialize
addHistory   = RL.addHistory
readline     = RL.readline
#else
initialize   = return ()
addHistory _ = return ()
readline s   = do
  putStr s
  hFlush stdout
  catch (fmap Just getLine) (\_ -> return Nothing)
#endif
