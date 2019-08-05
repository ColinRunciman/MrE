module Main where
import Generator
import Data.Time.Clock
import Expression
import Numeric
import PreOrderTrees
import Comparison

alphaSize :: Int
alphaSize = 4

sizeBound:: Int
sizeBound = 10

main = do
    t1 <- getCurrentTime
    let delta1=utctDayTime t1
    let fa=fuseA (take alphaSize ['a'..])
    let fan=concat $ take (sizeBound+1) fa
    let n=length fan
    t2 <- timeToCompute (n>0)
    let delta2=utctDayTime t2
    putStrLn $ "size of fused coalgebra: " ++ show n ++ "; time: " ++ showFFloat Nothing (convert delta2 delta1) ""
    t3 <- getCurrentTime
    let delta3=utctDayTime t3
    let xs=groupOrder compRE fan
    let ys=map pickMinList xs
    let m = length ys
    let q = sum (map size ys)
    t4 <- timeToCompute (q>0)
    let delta4=utctDayTime t4
    putStrLn $ "size of minimal coalgebra: " ++ show m ++ "; sum of sizes: " ++ show q ++ "; time: " ++ showFFloat Nothing (convert delta4 delta3) ""
    
timeToCompute :: Bool -> IO UTCTime
timeToCompute b | b         = getCurrentTime
                | otherwise = undefined

convert x y = fromRational (toRational (x-y))
    
    
