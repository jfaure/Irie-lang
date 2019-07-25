import ParseSyntax
import Parser

import Text.Megaparsec
import qualified Data.Text as T
import qualified Data.Text.IO as T.IO
import System.Environment

main = mapM go =<< getArgs
  where go f_name = T.IO.readFile f_name >>=
          \m -> case parseModule f_name m of
            Left e -> putStrLn $ errorBundlePretty e
            Right r -> print r
