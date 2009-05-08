{-# LANGUAGE CPP #-}
module Main (
  main
) where

import Util
import Ppr (Ppr(..), Doc, (<+>), (<>), text, char, hang)
import Parser (parse, parseProg, parseMods)
import Statics (tcProg, tcMods, GG)
import Translation (translate, transMods, MEnv)
import Dynamics (eval, evalMods, E)
import Basis (basis)
import BasisUtils (basis2venv, basis2tenv)
import Syntax (Mod(..), prog2mods, modName)
import Env (empty, (=.=), (=-=))

import Control.Monad (when, unless)
import System (getArgs, getProgName, exitFailure)
import System.IO.Error (ioeGetErrorString, isUserError)
import IO (readFile, hPutStr, hPutStrLn, stderr)

#ifdef USE_READLINE
import qualified USE_READLINE as RL
#else
import IO (hFlush, stdout, getLine)
#endif

data Option = Don'tExecute
            | Don'tType
            | Don'tCoerce
            | ReType
            | Verbose
  deriving Eq

main :: IO ()
main  = do
  args <- getArgs
  let (opts, mmsrc, filename) = processArgs [] args
      g0 = basis2tenv basis
      e0 = basis2venv basis
  maybe interactive (batch filename) mmsrc (`elem` opts) g0 e0
    `catch`
      \err -> do
        prog <- getProgName
        hPutStrLn stderr $
          prog ++ ": " ++ errorString err
        exitFailure

batch :: String -> IO String -> (Option -> Bool) -> GG -> E -> IO ()
batch filename msrc opt g0 e0 = do
      src <- msrc
      case parse parseProg filename src of
        Left e    -> fail $ "syntax error: " ++ show e
        Right ast -> do
          ast0 <- if opt Don'tType
                    then return ast
                    else do
                      (t, ast0) <- tcProg g0 ast
                      when (opt Verbose) $
                        mumble "TYPE" t
                      return ast0
          ast1 <- if opt Don'tCoerce
                    then return ast0
                    else do
                      let ast1 = translate ast0
                      when (opt Verbose) $
                        mumble "TRANSLATION" ast1
                      return ast1
          when (opt ReType) $ do
            (t, _) <- tcProg g0 ast1
            when (opt Verbose) $
              mumble "RE-TYPE" t
          unless (opt Don'tExecute) $ do
            v <- eval e0 ast1
            when (opt Verbose) $
              mumble "RESULT" v

data ReplState = RS {
  rsStatics     :: GG,
  rsTranslation :: MEnv,
  rsDynamics    :: E
}

statics, translation, dynamics
  :: ReplState -> [Mod] -> IO (ReplState, [Mod])

statics rs ast = do
  (g', ast') <- tcMods (rsStatics rs) ast
  return (rs { rsStatics = g' }, ast')

translation rs ast = do
  let (menv', ast') = transMods (rsTranslation rs) ast
  return (rs { rsTranslation = menv' }, ast')

dynamics rs ast = do
  e' <- evalMods ast (rsDynamics rs)
  return (rs { rsDynamics = e' }, ast)

interactive :: (Option -> Bool) -> GG -> E -> IO ()
interactive opt g0 e0 = do
  initialize
  repl (RS g0 empty e0)
  where
    repl st = do
      mast <- reader
      case mast of
        Nothing  -> return ()
        Just ast -> do
          st' <- doLine st ast `catch`
            \err -> do
              hPutStrLn stderr (errorString err)
              return st
          repl st'
    doLine st ast = do
      (st0, ast0) <- if opt Don'tType
                       then return (st, ast)
                       else statics st ast
      (st1, ast1) <- if opt Don'tCoerce
                       then return (st0, ast0)
                       else do
                         (st1, ast1) <- translation st0 ast0
                         when (opt Verbose) $
                           mumble "TRANSLATION" ast1
                         return (st1, ast1)
      when (opt ReType) $ do
        statics st1 ast1
        return ()
      (st2, _   ) <- if opt Don'tExecute
                       then return (st1, ast1)
                       else dynamics st1 ast1
      printResult st2 ast0
      return st2
    reader = loop []
      where
        loop acc = do
          mline <- readline (if null acc then "#- " else "#= ")
          case (mline, acc) of
            (Nothing, [])        -> return Nothing
            (Nothing, (_,err):_) -> do
              addHistory (unlines (reverse (map fst acc)))
              hPutStr stderr "\rsyntax error: "
              hPutStrLn stderr (show err)
              reader
            (Just "", _)         -> loop acc
            (Just line, _)       ->
              let cmd = unlines (reverse (line : map fst acc)) in
                case parse parseProg "-" cmd of
                  Right ast -> do
                    addHistory cmd
                    return (Just (prog2mods ast))
                  Left _ ->
                    case parse parseMods "-" cmd of
                      Right ast -> do
                        addHistory cmd
                        return (Just ast)
                      Left derr ->
                        loop ((line, derr) : acc)
    printResult st ms0 = do
      (_, ds) <- foldrM dispatch (rsDynamics st, []) ms0
      mapM_ print ds
        where
      dispatch :: (E, [Doc]) -> Mod -> IO (E, [Doc])
      dispatch (e, ds) m = do
        mv   <- case e =.= modName m of
                  Nothing -> return Nothing
                  Just v  -> Just `fmap` v
        let d = case m of
                  MdC x t _   -> val "C" x t mv
                  MdA x t _   -> val "A" x t mv
                  MdInt x t _ -> val "A" x (Just t) mv
        return (e =-= modName m, d : ds)
      val :: (Ppr x, Ppr t, Ppr v) =>
             String -> x -> Maybe t -> Maybe v -> Doc
      val lang x mt mv =
        let add c m = case m of
                        Nothing -> id
                        Just t  -> \d -> hang (d <+> char c)
                                              2
                                              (ppr t) in
        add '=' mv $
          add ':' mt $
            text "val[" <> text lang <> text "]" <+> ppr x

mumble ::  Ppr a => String -> a -> IO ()
mumble s a = print $ hang (text s <> char ':') 2 (ppr a)

errorString :: IOError -> String
errorString e | isUserError e = ioeGetErrorString e
              | otherwise     = show e

processArgs :: [Option] -> [String] -> ([Option], Maybe (IO String), String)
processArgs opts []          = (opts, Nothing, "-")
processArgs opts ["-"]       = (opts, Just getContents, "-")
processArgs opts (('-':c:d:e):r)
                             = processArgs opts (['-',c]:('-':d:e):r)
processArgs opts ("-t":r)    = processArgs (Don'tType:opts) r
processArgs opts ("-x":r)    = processArgs (Don'tExecute:opts) r
processArgs opts ("-c":r)    = processArgs (Don'tCoerce:opts) r
processArgs opts ("-r":r)    = processArgs (ReType:opts) r
processArgs opts ("-v":r)    = processArgs (Verbose:opts) r
processArgs opts (('-':_):_) = (opts, Just usage, "")
processArgs opts [name]      = (opts, Just (readFile name), name)
processArgs opts _           = (opts, Just usage, "")

usage :: IO a
usage  = do
  hPutStrLn stderr "Usage: affine [OPTIONS...] [FILENAME]"
  hPutStrLn stderr ""
  hPutStrLn stderr "Options:"
  hPutStrLn stderr "  -t   Don't type check"
  hPutStrLn stderr "  -x   Don't execute"
  hPutStrLn stderr "  -c   Don't add contracts"
  hPutStrLn stderr "  -r   Re-typecheck after translation (may fail)"
  hPutStrLn stderr "  -v   Verbose (show translation, results, types)"
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
