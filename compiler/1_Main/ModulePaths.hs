-- Find the files corresponding to import statements
module ModulePaths where
import System.FilePath.Posix as FilePath ( (<.>), (</>) )
import qualified System.Directory as Dir ( doesFileExist )

findModule ∷ [FilePath] -> FilePath -> IO (Either FilePath FilePath) --(Maybe FilePath)
 = \searchPath fName -> let
   checkExists [] _ = pure (Left fName)
   checkExists (sp:x) fName = let fPath = sp </> fName in Dir.doesFileExist fPath >>= \case
     True  -> pure (Right fPath)
     False -> checkExists x fName
  in Dir.doesFileExist fName >>= \case
    True  -> pure (Right ("." </> fName))
    False -> checkExists searchPath (fName FilePath.<.> "ii")
