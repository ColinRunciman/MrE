import Info
import Expression
import AutIntersect
import Parameters
import Data.List.Split
import Text.Printf
import System.Environment

minSize :: Int
minSize    =  7
chunkSize  =  20

main :: IO ()
main  =  do input <- readFile "semcatalogue/TREE-ab-11.txt"
            let allREs  =  filter ((==minSize) . size) $ resFrom input
            let testREs =  map (hu_extract . convertNice) $
                           drop (length allREs `mod` chunkSize) allREs
            mapM_ (reportRatioFor testREs) [Normal .. Minimal]

reportRatioFor :: [RE] -> Grade -> IO ()
reportRatioFor xs t  =  do putStr (show t ++ ": ")
                           putStrLn $ printf "%.3f" $
                             geomean $ map geomean $ chunksOf chunkSize $
                             map (sizeRatio . transFun t) xs

sizeRatio :: RE -> Double
sizeRatio x  =  fromIntegral (size x) / fromIntegral minSize

resFrom :: String -> [RE]
resFrom xs  =  case dropWhile (/='[') xs of
               []       -> []
               ('[':ys) -> let (i,zs) = span (/=']') ys in
                           read i : resFrom (tail zs)

geomean :: (Floating a) => [a] -> a
geomean xs = (foldr1 (*) xs)**(1 / fromIntegral (length xs))