-- Handles modules
-- 1. find the corresponding files
-- 2. synthesize needed declarations (types + fn sigs)
module Modules where

import qualified ParseSyntax as P
import CoreSyn

import qualified System.Directory as Dir
import System.FilePath.Posix
import Data.Functor
import qualified Data.Vector as V
import qualified Data.Text as T
import Debug.Trace

getModulePaths :: [FilePath] -> V.Vector P.Decl -- P.ImportDecl
  -> IO (V.Vector FilePath) -- full paths
 = \searchPath imports ->
  let
   fNames = modPath <$> imports
   checkExists [] f = error $ "couldn't find " ++ show f
     ++ " in search path\n" ++ show searchPath
   checkExists (sp:x) fName = 
     let fPath = sp </> fName
     in Dir.doesFileExist fPath >>= \case
       True  -> pure fPath
       False -> checkExists x fName
  in mapM (checkExists searchPath . (<.> "arya")) fNames

modPath (P.Import f) = T.unpack $ case modName f of
  P.Ident  t -> t
  P.Symbol t -> t

modName = \case
  P.Open n -> n
  P.Require n -> n
  P.ImportAs _ n -> n
  P.ImportCustom n _ _ -> n

--data ImportDecl
-- = Open    Name -- open import
-- | Require Name -- qualified import
-- | ImportAs ImportDecl Name
-- | ImportCustom {
--   importMod :: Name
-- , hiding    :: [Name]
-- , renaming  :: [(Name, Name)]
-- }
