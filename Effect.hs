module Main where

import System.Environment
import Parameters

-- Effect runs a transformation on random input data
-- and outputs how effective the trafo is on inputs of varying
-- alphabet/expression sizes

-- the trafo is selected  as it would in MrE

main = do
  args <- getArgs
  let p = argsToParams args
  input <- contents (inputsource p)
  let lns = lines input
  let n   = length lns
  let outs = sum $ map (sizeTrafo (trafo p)) lns
  let average = (fromIntegral outs / fromIntegral n) :: Double
  putStrLn $ reportInput (inputsource p)  ++ show average



