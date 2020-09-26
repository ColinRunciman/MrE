-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

import Control.Monad
import System.Directory
import System.Info
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
dir        =  "popresults"

poptest    =  if System.Info.os == "windows"
              then "PopTest.exe"
              else "./PopTest"

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
                                 poptest
                                 [o, "-S"++show s, "-W"++show w, "-T"++show t]
                                 ""
                       appendFile (dir++"/"++g) line
