{-# LANGUAGE CPP #-}
module Main (
  main
) where

import Util
import Ppr (Ppr(..), Doc, (<+>), (<>), text, char, hang, vcat)
import Parser (parse, parseProg, parseDecls)
import Statics (tcProg, tcDecls, S)
import Translation (translate, transDecls, MEnvT)
import Dynamics (eval, evalDecls, E)
import Basis (primBasis, srcBasis)
import BasisUtils (basis2venv, basis2tenv)
import Syntax (Prog, ProgT, Decl(..), DeclT, Mod(..),
               prog2decls, modName)
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
  g0  <- basis2tenv primBasis
  e0  <- basis2venv primBasis
  st0 <- loadSource (RS g0 empty e0) "basis" srcBasis
  maybe interactive (batch filename) mmsrc (`elem` opts) st0
    `catch`
      \err -> do
        prog <- getProgName
        hPutStrLn stderr $
          prog ++ ": " ++ errorString err
        exitFailure

loadSource :: ReplState -> String -> String -> IO ReplState
loadSource st name src = do
  case parse parseDecls name src of
    Left e     -> fail (show e)
    Right ast0 ->
      statics (st, ast0) >>= translation >>= dynamics >>= return . fst

batch :: String -> IO String -> (Option -> Bool) -> ReplState -> IO ()
batch filename msrc opt st0 = do
      src <- msrc
      case parse parseProg filename src of
        Left e    -> fail $ "syntax error: " ++ show e
        Right ast -> check ast where
          check   :: Prog () -> IO ()
          coerce  :: ProgT   -> IO ()
          recheck :: Prog i  -> IO ()
          execute :: Prog i  -> IO ()

          check ast0 =
            if opt Don'tType
              then execute ast0
              else do
                (t, ast1) <- tcProg (rsStatics st0) ast0
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
                recheck ast2

          recheck ast2 = do
            when (opt ReType) $ do
              (t, _) <- tcProg (rsStatics st0) ast2
              when (opt Verbose) $
                mumble "RE-TYPE" t
            execute ast2

          execute ast2 =
            unless (opt Don'tExecute) $ do
              v <- eval (rsDynamics st0) ast2
              when (opt Verbose) $
                mumble "RESULT" v

data ReplState = RS {
  rsStatics     :: S,
  rsTranslation :: MEnvT,
  rsDynamics    :: E
}

statics     :: (ReplState, [Decl i])  -> IO (ReplState, [DeclT])
translation :: (ReplState, [DeclT])   -> IO (ReplState, [DeclT])
dynamics    :: (ReplState, [Decl i])  -> IO (ReplState, [Decl i])

statics (rs, ast) = do
  (g', ast') <- tcDecls (rsStatics rs) ast
  return (rs { rsStatics = g' }, ast')

translation (rs, ast) = do
  let (menv', ast') = transDecls (rsTranslation rs) ast
  return (rs { rsTranslation = menv' }, ast')

dynamics (rs, ast) = do
  e' <- evalDecls ast (rsDynamics rs)
  return (rs { rsDynamics = e' }, ast)

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
          st' <- doLine st ast `catch`
            \err -> do
              hPutStrLn stderr (errorString err)
              return st
          repl st'
    doLine st ast = let
      check   :: (ReplState, [Decl ()]) -> IO ReplState
      coerce  :: (ReplState, [DeclT])   -> IO ReplState
      recheck :: [Decl i0] -> (ReplState, [Decl i])  -> IO ReplState
      execute :: [Decl i0] -> (ReplState, [Decl i])  -> IO ReplState
      display :: [Decl i0] -> (ReplState, [Decl i])  -> IO ReplState

      check stast0   = if opt Don'tType
                         then execute (snd stast0) stast0
                         else statics stast0 >>= coerce

      coerce stast1  = if opt Don'tCoerce
                         then recheck (snd stast1) stast1
                         else do
                           stast2 <- translation stast1
                           when (opt Verbose) $
                             mumbles "TRANSLATION" (snd stast2)
                           recheck (snd stast1) stast2

      recheck ast1 stast2 = if opt ReType
                              then do
                                statics stast2
                                execute ast1 stast2
                              else
                                execute ast1 stast2

      execute ast1 stast2 = if opt Don'tExecute
                              then display ast1 stast2
                              else dynamics stast2 >>= display ast1

      display ast1 stast3 = do
                              printResult (fst stast3, ast1)
                              return (fst stast3)

      in check (st, ast)
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
                    return (Just (prog2decls ast))
                  Left derr ->
                    case parse parseDecls "-" cmd of
                      Right ast -> do
                        addHistory cmd
                        return (Just ast)
                      Left _ ->
                        loop ((line, derr) : acc)
    printResult :: (ReplState, [Decl i]) -> IO ()
    printResult (st, ds0) = do
      (_, docs) <- foldrM dispatch (st, []) ds0
      mapM_ print docs
        where
      dispatch :: (ReplState, [Doc]) -> Decl i -> IO (ReplState, [Doc])
      dispatch (rs, docs) (DcMod m) = do
        let e = rsDynamics rs
        mv   <- case e =.= modName m of
                  Nothing -> return Nothing
                  Just v  -> Just `fmap` v
        let doc = case m of
                    MdC x t _   -> val "C" x t mv
                    MdA x t _   -> val "A" x t mv
                    MdInt x t _ -> val "A" x (Just t) mv
        return (rs { rsDynamics = e =-= modName m }, doc : docs)
      dispatch (rs, docs) (DcTyp td) = return (rs, ppr td : docs)
      dispatch (rs, docs) (DcAbs at ds) =
        foldrM dispatch (rs, (text "abstype" <> ppr at) : docs) ds
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

mumbles :: Ppr a => String -> [a] -> IO ()
mumbles s as = print $ hang (text s <> char ':') 2 (vcat (map ppr as))

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
  hPutStrLn stderr "  -t   Don't type check (implies -c)"
  hPutStrLn stderr "  -c   Don't add contracts"
  hPutStrLn stderr "  -x   Don't execute"
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
