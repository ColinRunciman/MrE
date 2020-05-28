import Control.Monad
import System.Directory
import System.Process

sizes      =  [10, 20, 40, 80, 160, 320, 640, 1280, 2560]
widths     =  [1, 2, 3, 4, 8, 16]
dir        =  "populations"

main  =  do ex <- doesDirectoryExist dir
            when ex (removeDirectoryRecursive dir)
            createDirectory dir
            mapM_ forSize sizes

forSize :: Int -> IO ()
forSize s      =  mapM_ forWidth widths
  where
  forWidth w   =  do res <- readProcess
                              "./Reg"
                              ["-S"++show s, "-W"++show w, "-Q1000"]
                              ""
                     appendFile (dir++"/s"++show s++"w"++show w) res
