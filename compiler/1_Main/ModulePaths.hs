-- Find the files corresponding to import statements
module ModulePaths where
import System.FilePath.Posix as FilePath ( (<.>), (</>) )
import qualified System.Directory as Dir ( doesFileExist )

-- Either NoPathfound(identity) FilePath
findModule :: [FilePath] -> FilePath -> IO (Either FilePath FilePath) --(Maybe FilePath)
 = \searchPath fName -> let
   checkExists [] _ = pure (Left fName)
   checkExists (sp:x) fName = let fPath = sp </> fName in Dir.doesFileExist fPath >>= \case
     True  -> pure (Right fPath)
     False -> checkExists x fName
  in Dir.doesFileExist fName >>= \case
    True  -> pure (Right ("." </> fName))
    False -> checkExists searchPath (fName FilePath.<.> "ii")

-- canonicalise filepaths and replace '/' with '%'
getCachePath :: FilePath -> FilePath -> FilePath
getCachePath objDir fName = let
  -- ./module == module , the cache converts paths to the first version
  normalise fName = case fName of
    '.' : '/' : _ -> fName
    '/' : _ -> fName
    _ -> '.' : '/' : fName
  in objDir <> map (\case { '/' -> '%' ; x -> x} ) (normalise fName)
