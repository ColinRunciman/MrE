module Main where

import System.Environment
import Parameters
import Parser
import GruberP
import Data.List.Split
import Text.Printf

-- Effect runs a transformation on random input data
-- and outputs how effective the trafo is on inputs of varying
-- alphabet/expression sizes

-- the trafo is selected  as it would in MrE

geomean :: (Floating a) => [a] -> a
geomean xs = (foldr1 (*) xs)**(1 / fromIntegral (length xs))

main = do
  args <- getArgs
  let p = argsToParams args
  input <- contents (inputsource p)
  let lns = lines input
  let n   = length lns
  let ins  = map (gSize . readFullExp) lns
  let outs = map (sizeTrafo (trafo p)) lns
  let average = (fromIntegral (sum outs) / fromIntegral n) :: Double
  let ratios = zipWith (\i o -> (fromIntegral o / fromIntegral i) :: Double) ins outs
  putStrLn $ reportInput (inputsource p)  ++
             show average
  putStrLn $ printf "%.1f" (100.0 * geomean (map geomean $ chunksOf 20 ratios))



