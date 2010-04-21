{-# LANGUAGE
      CPP,
      TemplateHaskell #-}
module Paths (
  findFirstInPath, findInPath,
  almsLibPath, findAlmsLib, findAlmsLibRel,
  version, versionString
) where

import Util

import Language.Haskell.TH
import System.FilePath
import System.Directory (doesFileExist, getCurrentDirectory)
import System.Environment (getEnv)
import Data.Version

#ifdef ALMS_CABAL_BUILD
import Paths_alms
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

findFirstInPath :: [FilePath] -> [FilePath] -> IO (Maybe FilePath)
findFirstInPath []     _  = return Nothing
findFirstInPath (f:fs) ds = do
  mpath <- findInPath f ds
  case mpath of
    Nothing -> findFirstInPath fs ds
    Just _  -> return mpath

findInPath :: FilePath -> [FilePath] -> IO (Maybe FilePath)
findInPath _    []     = return Nothing
findInPath name (d:ds) = do
  b <- doesFileExist (d </> name)
  if b
    then return (Just (normalise (d </> name)))
    else findInPath name ds

almsLibPath :: IO [FilePath]
almsLibPath = do
  user   <- liftM splitSearchPath (getEnv "ALMS_LIB_PATH")
             `catch` \_ -> return []
  system <- getDataDir
  build  <- liftM (</> "lib") getBuildDir
  return $ user ++ [ system, build ]

findAlmsLib :: FilePath -> IO (Maybe FilePath)
findAlmsLib name = do
  path <- almsLibPath
  findFirstInPath [ name, name <.> "alms" ] path

findAlmsLibRel :: FilePath -> FilePath -> IO (Maybe FilePath)
findAlmsLibRel name rel = do
  path <- almsLibPath
  let rel' = case rel of
               "-"  -> "."
               _    -> dropFileName rel
  findFirstInPath [ name, name <.> "alms" ] (rel' : path)

versionString :: String
versionString  = "Alms, version " ++ showVersion version

