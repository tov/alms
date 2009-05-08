{-# LANGUAGE CPP #-}
module Main (
  main
) where

import Ppr (Ppr(..), (<+>), (<>), text, char, hang)
import Parser (parse, parseProg)
import Statics (tcProg, GG)
import Translation (translate)
import Dynamics (eval, E)
import Basis (basis)
import BasisUtils (basis2venv, basis2tenv)

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
          unless (opt Don'tType) $ do
            t <- tcProg g0 ast
            when (opt Verbose) $
              mumble "TYPE" t
          ast' <- if opt Don'tCoerce
                    then return ast
                    else do
                      let ast' = translate ast
                      when (opt Verbose) $
                        mumble "TRANSLATION" ast'
                      return ast'
          when (opt ReType) $ do
            t <- tcProg g0 ast'
            when (opt Verbose) $
              mumble "RE-TYPE" t
          unless (opt Don'tExecute) $ do
            v <- eval e0 ast'
            when (opt Verbose) $
              mumble "RESULT" v

interactive :: (Option -> Bool) -> GG -> E -> IO ()
interactive opt g0 e0 = do
  initialize
  repl
  where
    repl = do
      mast <- reader
      case mast of
        Nothing  -> return ()
        Just ast -> do
          doLine ast `catch`
            \err -> do
              hPutStrLn stderr (errorString err)
          repl
    doLine ast = do
      t <- if opt Don'tType
             then return Nothing
             else Just `fmap` tcProg g0 ast
      ast' <- if opt Don'tCoerce
                then return ast
                else do
                  let ast' = translate ast
                  when (opt Verbose) $
                    mumble "TRANSLATION" ast'
                  return ast'
      when (opt ReType) $ do
        t' <- tcProg g0 ast'
        when (opt Verbose) $
          mumble "RE-TYPE" t'
      v <- if opt Don'tExecute
             then return (ppr ast)
             else ppr `fmap` eval e0 ast'
      printResult v t
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
                    return (Just ast)
                  Left derr ->
                    loop ((line, derr) : acc)
    printResult v Nothing  = print v
    printResult v (Just t) = print $ hang (v <+> char ':') 2 (ppr t)

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
