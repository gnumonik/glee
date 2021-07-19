{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_glee (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,0,0,1] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/home/gsh/code/haskell/glee/.stack-work/install/x86_64-linux-tinfo6/5f34a23336cc5d2aaa471c989e6952d8a9f2fbadbd6d08f7e6573c048fc790c6/8.10.4/bin"
libdir     = "/home/gsh/code/haskell/glee/.stack-work/install/x86_64-linux-tinfo6/5f34a23336cc5d2aaa471c989e6952d8a9f2fbadbd6d08f7e6573c048fc790c6/8.10.4/lib/x86_64-linux-ghc-8.10.4/glee-0.0.0.1-GTqxEqjMJsIJTdqt2Pjqiv"
dynlibdir  = "/home/gsh/code/haskell/glee/.stack-work/install/x86_64-linux-tinfo6/5f34a23336cc5d2aaa471c989e6952d8a9f2fbadbd6d08f7e6573c048fc790c6/8.10.4/lib/x86_64-linux-ghc-8.10.4"
datadir    = "/home/gsh/code/haskell/glee/.stack-work/install/x86_64-linux-tinfo6/5f34a23336cc5d2aaa471c989e6952d8a9f2fbadbd6d08f7e6573c048fc790c6/8.10.4/share/x86_64-linux-ghc-8.10.4/glee-0.0.0.1"
libexecdir = "/home/gsh/code/haskell/glee/.stack-work/install/x86_64-linux-tinfo6/5f34a23336cc5d2aaa471c989e6952d8a9f2fbadbd6d08f7e6573c048fc790c6/8.10.4/libexec/x86_64-linux-ghc-8.10.4/glee-0.0.0.1"
sysconfdir = "/home/gsh/code/haskell/glee/.stack-work/install/x86_64-linux-tinfo6/5f34a23336cc5d2aaa471c989e6952d8a9f2fbadbd6d08f7e6573c048fc790c6/8.10.4/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "glee_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "glee_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "glee_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "glee_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "glee_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "glee_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
