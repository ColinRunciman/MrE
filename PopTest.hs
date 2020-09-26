-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module Main where

import System.Environment
import Data.Time.Clock
import System.IO.Unsafe (unsafePerformIO)
import Numeric
import Expression
import Parameters
import Parser
import GruberP
import Data.List.Split
import Text.Printf
import Control.Monad

-- This program runs a transformation on one of the samples of randomly
-- generated REs stored in the 'populations' directory.  A single line is
-- written to standard output reporting:
-- (1) alphabet size for the sample
-- (2) RE size for the sample
-- (3) geometric mean result size as a percentage of input size
-- (4) mean simplification time

-- Input, Time, Output
data ITO = ITO {inp :: RE, tim :: Float, out :: RE}

meanTime :: [ITO] -> Float
meanTime itos = sum (map tim itos) / fromIntegral (length itos)

showTime :: Float -> String
showTime f = showFFloat Nothing f ""

geomean :: (Floating a) => [a] -> a
geomean xs = (foldr1 (*) xs)**(1 / fromIntegral (length xs))

showDouble :: Double -> String
showDouble d = printf "%.2f" d

process :: Parameters -> String -> ITO
process p s  =  ITO e t e'
  where
  g  =  trafo p
  e  =  readFullExp s
  e' =  transFun p $ readBeforeT g s
  t  =  timeToCompute e e' (e' == e')
        -- the comparison of e' with itself forces its full
        -- evaluation EXCLUDING Info attributes unneeded
        -- by the transformation

timeToCompute :: RE -> RE -> Bool -> Float
timeToCompute e0 e1 x  =  unsafePerformIO $ do
  t0  <-  getCurrentTime
  compute
  t1  <-  getCurrentTime
  return $ fromRational $ toRational $ utctDayTime t1 - utctDayTime t0
  where
  compute | x          =  return ()
          | otherwise  =  error $ show e0 ++ " expanded to " ++ show e1 ++ "!"

main = do
  args        <-  getArgs
  let p        =  argsToParams args
  input       <-  contents (inputsource p)
  let lns      =  lines input
  let itos     =  map (process p) lns
  let n        =  length lns
  let insizes  =  map (gSize . inp) itos
  let outsizes =  map (gSize . out) itos
  let ratios   =  zipWith (\i o -> (fromIntegral o / fromIntegral i) :: Double)
                    insizes outsizes
  timedCommand p $
    putStrLn $ reportInput (inputsource p)
    ++
    showTime (meanTime itos)    
    ++ "\t" ++
    showDouble (100.0 * geomean (map geomean $ chunksOf 20 ratios))
  let average  =  (fromIntegral (sum outsizes) / fromIntegral n) :: Double
  when (verbose p) $ putStrLn $ showDouble average
