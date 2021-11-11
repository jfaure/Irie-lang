-- Handles modules
-- 1. find the corresponding files
module ModulePaths where

import qualified System.Directory as Dir
import System.FilePath.Posix as FilePath

findModule :: [FilePath] -> FilePath -> IO FilePath
 = \searchPath fName ->
  let
   checkExists [] f = error $ "couldn't find " ++ show f
     ++ " in search path\n" ++ show searchPath
   checkExists (sp:x) fName = 
     let fPath = sp </> fName
     in Dir.doesFileExist fPath >>= \e -> if e
       then pure fPath
       else checkExists x fName
  in (checkExists searchPath . (FilePath.<.> "ii")) fName
