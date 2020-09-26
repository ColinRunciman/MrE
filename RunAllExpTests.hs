-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

import Control.Monad
import System.Directory
import System.Info
import System.Process

sizes      =  [7 .. 9]
widths     =  [1 .. 4]
t          =  100
trafos     =  [ ("-n", "normal")
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
