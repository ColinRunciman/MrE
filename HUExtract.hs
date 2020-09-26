-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

import Info
import Expression
import AutIntersect
import Data.List.Split
import System.Environment
import Data.List (maximum)
import Catalogue (treeSizes,treeFileName,sigmaFor)
import Parameters

minSize :: Int
minSize    =  7

main :: IO ()
main  =   do args <- getArgs
             let p = argsToParams args
             let (s,w) = sizeWidth (inputsource p)
             input <- readFile (treeFileName (sigmaFor w)(treeSizes!!w))
             let allREs  =  filter ((==s) . size) $ resFrom input
             let testREs =  map (hu_extract . convertNice) allREs
             mapM print testREs
             return ()

sizeWidth :: Maybe PopulationFile -> (Int,Int)
sizeWidth Nothing   = (minSize, 2)
sizeWidth (Just pf) = (ofsize pf,width pf)

resFrom :: String -> [RE]
resFrom xs  =  case dropWhile (/='[') xs of
               []       -> []
               ('[':ys) -> let (i,zs) = span (/=']') ys in
                           read i : resFrom (tail zs)
