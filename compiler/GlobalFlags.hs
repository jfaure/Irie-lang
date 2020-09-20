-- Command line arguments are basically global constants
--  but they must be initialized first thing at runtime
module GlobalFlags (module CmdLine , initGlobalFlags , getGlobalFlags)
where
import CmdLine
import Data.IORef
import System.IO.Unsafe

globalFlags :: IORef CmdLine
  = unsafePerformIO $ newIORef defaultCmdLine

initGlobalFlags :: CmdLine -> IO CmdLine
  = \flags -> flags <$ writeIORef globalFlags flags

getGlobalFlags :: CmdLine
  = unsafePerformIO $ readIORef globalFlags
