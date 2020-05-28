import Control.Monad
import System.Directory
import System.Process

sizes      =  [10, 20, 40, 80, 160, 320, 640, 1280, 2560]
widths     =  [1, 2, 3, 4, 8, 16]
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

main  =  do ex <- doesDirectoryExist "popresults"
            when ex (removeDirectoryRecursive "popresults")
            createDirectory "popresults"
            mapM_ forTrafo trafos

forTrafo :: (String, String) -> IO ()
forTrafo (o, g)  =  mapM_ forSize sizes
  where
  forSize s      =  mapM_ forWidth widths
    where
    forWidth w   =  do line <- readProcess
                                 "./PopTest"
                                 [o, "-S"++show s, "-W"++show w, "-T"++show t]
                                 ""
                       appendFile ("popresults/"++g) line
