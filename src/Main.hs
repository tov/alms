{-# LANGUAGE CPP #-}
module Main (
  main
) where

import Util
import Ppr (Ppr(..), Doc, (<+>), (<>), text, char, hang, vcat)
import Parser (parse, parseProg, parseDecls)
import Statics (tcProg, tcDecls, S, NewDefs)
import Translation (translate, translateDecls, TEnv)
import Dynamics (eval, addDecls, E, NewValues)
import Basis (primBasis, srcBasis)
import BasisUtils (basis2venv, basis2tenv)
import Syntax (Prog, Lid, ProgT, Decl(..), DeclT, Let(..),
               prog2decls, letName)
import Env (empty, GenLookup(..), GenEmpty(..))

import Control.Monad (when, unless)
import System.Exit (exitFailure)
import System.Environment (getArgs, getProgName, withProgName, withArgs)
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
  processArgs [] args $ \opts mmsrc filename -> do
  g0  <- basis2tenv primBasis
  e0  <- basis2venv primBasis
  st0 <- loadSource (RS g0 genEmpty e0) "basis" srcBasis
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
    Right ast0 -> do
      (st1, _, ast1) <- statics (st, ast0)
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

statics     :: (ReplState, [Decl i])  -> IO (ReplState, NewDefs, [DeclT])
translation :: (ReplState, [DeclT])   -> IO (ReplState, [DeclT])
dynamics    :: (ReplState, [Decl i])  -> IO (ReplState, NewValues)

statics (rs, ast) = do
  (g', newTypes, ast') <- tcDecls (rsStatics rs) ast
  return (rs { rsStatics = g' }, newTypes, ast')

translation (rs, ast) = do
  let (menv', ast') = translateDecls (rsTranslation rs) ast
  return (rs { rsTranslation = menv' }, ast')

dynamics (rs, ast) = do
  (e', newValues) <- addDecls (rsDynamics rs) ast
  return (rs { rsDynamics = e' }, newValues)

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
      coerce  :: Maybe NewDefs ->
                 (ReplState, [DeclT]) -> IO ReplState
      recheck :: Maybe NewDefs ->
                 (ReplState, [Decl i]) -> IO ReplState
      execute :: Maybe NewDefs ->
                 (ReplState, [Decl i]) -> IO ReplState
      display :: Maybe NewDefs -> Maybe NewValues ->
                 ReplState -> IO ReplState

      check stast0   = if opt Don'tType
                         then execute Nothing stast0
                         else do
                           (st1, newDefs, ast1) <- statics stast0
                           coerce (Just newDefs) (st1, ast1)

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
                                statics stast2
                                execute newDefs stast2
                              else
                                execute newDefs stast2

      execute newDefs stast2
                          = if opt Don'tExecute
                              then display newDefs Nothing (fst stast2)
                              else do
                                (st3, newValues) <- dynamics stast2
                                display newDefs (Just newValues) st3

      display newDefs newValues st3
                          = do printResult newDefs newValues
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
    printResult :: Maybe NewDefs -> Maybe NewValues -> IO ()
    printResult mdefs mvals = do
      print mdefs
      print mvals
    {-
      (_, docs, _) <- foldrM dispatch (st, [], []) ds0
      mapM_ print docs
        where
      dispatch :: (ReplState, [Doc], [Lid]) ->
                  Decl i -> IO (ReplState, [Doc], [Lid])
      dispatch (rs, docs, seen) (DcLet _ m)     = do
        let e = rsDynamics rs
            n = letName m
        mv   <- case (e =..= n, n `elem` seen) of
                  (Just v, False) -> Just `fmap` v
                  _               -> return Nothing
        let doc = case m of
                    LtC _ x t _   -> val "C" x t mv
                    LtA _ x t _   -> val "A" x t mv
                    LtInt _ x t _ -> val "A" x (Just t) mv
        return (rs, doc : docs, n : seen)
      dispatch (rs, docs, seen) (DcTyp _ td)    =
        return (rs, ppr td : docs, seen)
      dispatch (rs, docs, seen) (DcAbs _ at ds) =
        foldrM dispatch (rs, (text "abstype" <> ppr at) : docs, seen) ds
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
            -}

mumble ::  Ppr a => String -> a -> IO ()
mumble s a = print $ hang (text s <> char ':') 2 (ppr a)

mumbles :: Ppr a => String -> [a] -> IO ()
mumbles s as = print $ hang (text s <> char ':') 2 (vcat (map ppr as))

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
  hPutStrLn stderr "Usage: affine [OPTIONS...] [--] [FILENAME] [OPTIONS...]"
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
