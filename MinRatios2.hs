import Info
import Expression
import AutIntersect
import Parameters
import Data.List.Split
import Text.Printf
import System.Environment
import Data.List (maximum)
import Parameters
import BigNum

main :: IO ()
main  = do  args <- getArgs
            let p = argsToParams args
            input <- contents (inputsource p)
            let n = origSize (inputsource p)
            let ts = map read $ lines input
            mapM_ (reportRatioFor n ts) [Normal .. Minimal]

origSize Nothing   = 7
origSize (Just pf) = ofsize pf

reportRatioFor :: Int -> [RE] -> Grade -> IO ()
reportRatioFor n xs t  =  do putStr (show t ++ ": ")
                             putStrLn $ printf "%.3f" $ biggeomean $
                               map (sizeRatio n t . transFun (defaults{trafo=t})) xs

sizeRatio :: Int -> Grade -> RE -> Double
sizeRatio n g x  =  fromIntegral (sizeForT g x) / fromIntegral n

resFrom :: String -> [RE]
resFrom xs  =  case dropWhile (/='[') xs of
               []       -> []
               ('[':ys) -> let (i,zs) = span (/=']') ys in
                           read i : resFrom (tail zs)
