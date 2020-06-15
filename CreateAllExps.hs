import Control.Monad
import System.Directory
import System.Info
import System.Process

sizes      =  [7 .. 9]
widths     =  [1 .. 4]
dir        =  "expansions"

huextract  =  if System.Info.os == "windows"
              then "HUExtract.exe"
              else "./HUExtract"

main  =  do ex <- doesDirectoryExist dir
            when ex (removeDirectoryRecursive dir)
            createDirectory dir
            mapM_ forSize sizes

forSize :: Int -> IO ()
forSize s      =  mapM_ forWidth widths
  where
  forWidth w   =  do res <- readProcess
                              huextract
                              ["-S"++show s, "-W"++show w]
                              ""
                     appendFile (dir++"/s"++show s++"w"++show w) res
