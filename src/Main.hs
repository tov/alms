-- | The main driver program, which performs all manner of unpleasant
--   tasks to tie everything together
{-# LANGUAGE CPP #-}
module Main (
  main
) where

import Util
import Ppr (Ppr(..), (<+>), (<>), text, char, hang)
import qualified Ppr
import Parser (parse, parseProg, parseDecls)
import Statics (tcProg, tcDecls, S,
                NewDefs(..), emptyNewDefs, tyInfoToDec)
import Translation (translate, translateDecls, TEnv, tenv0)
import Value (VExn(..), vppr)
import Dynamics (eval, addDecls, E, NewValues)
import Basis (primBasis, srcBasis)
import BasisUtils (basis2venv, basis2tenv)
import Syntax (Prog, ProgT, Decl, DeclT,
               BIdent(..), prog2decls)
import Env (empty, unionProduct, toList)

import Control.Monad (when, unless)
import System.Exit (exitFailure)
import System.Environment (getArgs, getProgName, withProgName, withArgs)
import System.IO.Error (ioeGetErrorString, isUserError)
import IO (readFile, hPutStr, hPutStrLn, stderr)
import qualified Control.Exception as Exn

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

-- | The main procedure
main :: IO ()
main  = do
  args <- getArgs
  processArgs [] args $ \opts mmsrc filename -> do
  g0  <- basis2tenv primBasis
  e0  <- basis2venv primBasis
  st0 <- loadSource (RS g0 tenv0 e0) "basis" srcBasis
  maybe interactive (batch filename) mmsrc (`elem` opts) st0
    `handleExns` exitFailure

loadSource :: ReplState -> String -> String -> IO ReplState
loadSource st name src = do
  case parse parseDecls name src of
    Left e     -> fail (show e)
    Right ast0 -> do
      (st1, _, ast1) <- statics False (st, ast0)
      (st2, ast2)    <- translation (st1, ast1)
      (st3, _)       <- dynamics (st2, ast2)
      return st3

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
  rsTranslation :: TEnv,
  rsDynamics    :: E
}

statics     :: Bool -> (ReplState, [Decl i]) ->
               IO (ReplState, NewDefs, [DeclT])
translation :: (ReplState, [DeclT])   -> IO (ReplState, [DeclT])
dynamics    :: (ReplState, [Decl i])  -> IO (ReplState, NewValues)

statics slow (rs, ast) = do
  (g', new, ast') <- tcDecls slow (rsStatics rs) ast
  return (rs { rsStatics = g' }, new, ast')

translation (rs, ast) = do
  let (menv', ast') = translateDecls (rsTranslation rs) ast
  return (rs { rsTranslation = menv' }, ast')

dynamics (rs, ast) = do
  (e', new) <- addDecls (rsDynamics rs) ast
  return (rs { rsDynamics = e' }, new)

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
        prog <- getProgName
        hPutStrLn stderr (prog ++ ": " ++ errorString err)
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
          st' <- doLine st ast `handleExns` return st
          repl st'
    doLine st ast = let
      check   :: (ReplState, [Decl ()]) -> IO ReplState
      coerce  :: NewDefs -> (ReplState, [DeclT]) -> IO ReplState
      recheck :: NewDefs -> (ReplState, [Decl i]) -> IO ReplState
      execute :: NewDefs -> (ReplState, [Decl i]) -> IO ReplState
      display :: NewDefs -> NewValues -> ReplState -> IO ReplState

      check stast0   = if opt Don'tType
                         then execute emptyNewDefs stast0
                         else do
                           (st1, newDefs, ast1) <- statics True stast0
                           coerce newDefs (st1, ast1)

      coerce newDefs stast1
                     = if opt Don'tCoerce
                         then recheck newDefs stast1
                         else do
                           stast2 <- translation stast1
                           when (opt Verbose) $
                             mumbles "TRANSLATION" (snd stast2)
                           recheck newDefs stast2

      recheck newDefs stast2
                          = if opt ReType
                              then do
                                statics False stast2
                                execute newDefs stast2
                              else
                                execute newDefs stast2

      execute newDefs stast2
                          = if opt Don'tExecute
                              then display newDefs empty (fst stast2)
                              else do
                                (st3, newVals) <- dynamics stast2
                                display newDefs newVals st3

      display newDefs newVals st3
                          = do printResult newDefs newVals
                               return st3

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
                    loop ((line, derr) : acc)
    printResult :: NewDefs -> NewValues -> IO ()
    printResult defs values = do
      let vals = unionProduct
                   (newValues defs)
                   values
      print $ Ppr.vcat $
        map pprMod (newModules defs) ++
        map pprType (toList (newTypes defs)) ++
        map pprValue (toList vals)

      where
      pprMod uid    = text "module" <+> ppr uid

      pprType (lid, ti) = ppr (tyInfoToDec lid ti)

      pprValue (Con _, _)        = Ppr.empty
      pprValue (Var k, (mt, mv)) =
        addHang '=' (fmap ppr mv) $
          addHang ':' (fmap ppr mt) $
            ppr k

      addHang c m d = case m of
        Nothing -> d
        Just t  -> hang (d <+> char c) 2 t

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
  loop opts (('-':c:d:e):r)
                        = loop opts (['-',c]:('-':d:e):r)
  loop opts ("-t":r)    = loop (Don'tType:opts) r
  loop opts ("-x":r)    = loop (Don'tExecute:opts) r
  loop opts ("-c":r)    = loop (Don'tCoerce:opts) r
  loop opts ("-r":r)    = loop (ReType:opts) r
  loop opts ("-v":r)    = loop (Verbose:opts) r
  loop _    (('-':_):_) = usage
  loop opts (name:args) = go name args opts (Just (readFile name))

  go name args opts mmsrc =
    withProgName name $
      withArgs args $
        k opts mmsrc name

usage :: IO a
usage  = do
  hPutStrLn stderr "Usage: alms [OPTIONS...] [--] [FILENAME] [OPTIONS...]"
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
