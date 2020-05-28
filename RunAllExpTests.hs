import Control.Monad
import System.Directory
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

main  =  do ex <- doesDirectoryExist "expresults"
            when ex (removeDirectoryRecursive "expresults")
            createDirectory "expresults"
            mapM_ forTrafo trafos

forTrafo :: (String, String) -> IO ()
forTrafo (o, g)  =  mapM_ forSize sizes
  where
  forSize s      =  mapM_ forWidth widths
    where
    forWidth w   =  do line <- readProcess
                                 "./ExpTest"
                                 [o, "-S"++show s, "-W"++show w, "-T"++show t]
                                 ""
                       appendFile ("expresults/"++g) line
