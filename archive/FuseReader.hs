module FuseReader where

import Expression
import Fuse
import List
import StarPromotion
import StarRecognition
import Comparison
import Context

xfuse = recognise -- was : recognise
ifuse = recognise -- was : promote

fuseReader :: IO [RE]
fuseReader = fmap makeREs $ getContents

makeREs :: String -> [RE]
makeREs input = nubSort $ map (ifuse . read) (lines input)

--makeREs2 :: String -> IO [RE]
--makeREs2 s = fmap nubSort (mapM transform $ makeREs s)

transform :: RE -> IO RE
transform x
    | compEQ x y
    = return y
    | otherwise
    = do
          putStr "bad pair: "
          print (x,y)
          return x   
      where y=xfuse x

fuseFile :: String -> IO [RE]
fuseFile filename = fmap makeREs $ readFile filename

fuseFileInfo :: String -> IO [RE]
fuseFileInfo filename = fmap nubSort $
    do
       contents <- readFile filename
       let (res,inle,oule,inq,ouq) = makeREInfo contents
       putStrLn ("number of inputs:\t" ++ show inle)
       putStrLn ("average input size:\t" ++ show inq)
       putStrLn ("number of outputs:\t" ++ show oule)
       putStrLn ("average output size:\t" ++ show ouq)
       -- mapM transform res
       return res
       

makeREInfo :: String -> ([RE],Int,Int,Double,Double)
makeREInfo input = (outs,inle,oule,quotient insi inle,quotient ousi oule)
                   where
                   inps = map read $ lines input
                   outs = nubSort $ map ifuse inps
                   inle = length inps
                   oule = length outs
                   insi = totalSize inps
                   ousi = totalSize outs

totalSize :: [RE] -> Int
totalSize xs = sum $ map size xs

quotient :: Int -> Int -> Double
quotient _ 0 = error "average of nothing"
quotient m n = fromIntegral ((m*100) `div` n) / 100.0
 
                  




