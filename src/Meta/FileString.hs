module Meta.FileString (
  fileString, fileStringCheck
) where

import Language.Haskell.TH

fileString :: String -> ExpQ
fileString  = fileStringCheck (const (return Nothing))

fileStringCheck :: (String -> IO (Maybe (Bool, String))) -> String -> ExpQ
fileStringCheck check file = do
  (str, chk) <- runIO $ do
    str <- readFile file
    chk <- check str
    return (str, chk)
  case chk of
    Nothing     -> return ()
    Just (b, s) -> report b s
  litE (stringL str)
