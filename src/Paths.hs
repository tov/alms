{-# LANGUAGE
      CPP,
      TemplateHaskell #-}
module Paths where

import Util

import Language.Haskell.TH
import System.FilePath
import System.Directory (doesFileExist, getCurrentDirectory)
import System.Environment (getEnv)

#ifdef ALMS_CABAL_BUILD
import Paths_alms
#else
import Data.Version (Version(..))
import System.Environment (getEnv)
#endif

builddir  :: FilePath
builddir   = $(runIO getCurrentDirectory >>= litE . stringL)

getBuildDir :: IO FilePath
getBuildDir  = catch (getEnv "alms_builddir") (\_ -> return builddir)

#ifndef ALMS_CABAL_BUILD
version :: Version
version = Version {versionBranch = [0,0,0], versionTags = ["dev"]}

bindir, datadir :: FilePath

bindir     = builddir
datadir    = dropFileName builddir </> "lib"

getBinDir, getDataDir :: IO FilePath
getBinDir  = catch (getEnv "alms_bindir") (\_ -> return bindir)
getDataDir = catch (getEnv "alms_datadir") (\_ -> return datadir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir </> name)
#endif

findFileInPath :: FilePath -> [FilePath] -> IO (Maybe FilePath)
findFileInPath _    []     = return Nothing
findFileInPath name (d:ds) = do
  b <- doesFileExist (d </> name)
  if b
    then return (Just (normalise (d </> name)))
    else findFileInPath name ds

almsLibPath :: IO [FilePath]
almsLibPath = do
  user   <- liftM splitSearchPath (getEnv "ALMS_LIB_PATH")
             `catch` \_ -> return []
  system <- getDataDir
  build  <- liftM (</> "lib") getBuildDir
  return $ "." : user ++ [ system, build ]

findAlmsLib :: FilePath -> IO (Maybe FilePath)
findAlmsLib name = almsLibPath >>= findFileInPath name

