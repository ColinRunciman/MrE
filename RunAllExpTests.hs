import Control.Monad
import System.Directory
import System.Info
import System.Process

sizes      =  [7, 8]
widths     =  [1, 2, 3, 4]
t          =  100
trafos     =  [ ("-g", "Gruber-Gulan")
              , ("-n", "normal")
              , ("-f", "fused")
              , ("-l", "promoted")
              , ("-p", "pressed")
              , ("-s", "stellar")
              , ("-c", "semsearch")
              , ("-y", "synsearch")
              ]
dir        =  "expresults"

exptest    =  if System.Info.os == "windows"
              then "ExpTest.exe"
              else "./ExpTest"


main  =  do ex <- doesDirectoryExist dir
            when ex (removeDirectoryRecursive dir)
            createDirectory dir
            mapM_ forTrafo trafos

forTrafo :: (String, String) -> IO ()
forTrafo (o, g)  =  mapM_ forSize sizes
  where
  forSize s      =  mapM_ forWidth widths
    where
    forWidth w   =  do line <- readProcess
                                 exptest
                                 [o, "-S"++show s, "-W"++show w, "-T"++show t]
                                 ""
                       appendFile (dir++"/"++g) line
