import Control.Monad
import System.Directory
import System.Process

sizes      =  [7, 8]
widths     =  [1, 2, 3, 4]
dir        =  "expansions"

main  =  do ex <- doesDirectoryExist dir
            when ex (removeDirectoryRecursive dir)
            createDirectory dir
            mapM_ forSize sizes

forSize :: Int -> IO ()
forSize s      =  mapM_ forWidth widths
  where
  forWidth w   =  do res <- readProcess
                              "./HUExtract"
                              ["-S"++show s, "-W"++show w]
                              ""
                     appendFile (dir++"/s"++show s++"w"++show w) res
