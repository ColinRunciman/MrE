-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

import Data.List.Split
import Text.Printf
import System.Environment
import Data.List (maximum)
import AutIntersect
import BigNum
import Expression
import GruberP
import Info
import Parameters
import Parser

-- This program runs a transformation on one of the samples of expressions
-- in the 'expansions' directory.  A single line to standard output reports:
-- (1) alphabet size for the sample
-- (2) size of ORIGINAL minimal expressions from which the sample was derived
-- (3) geometric mean of result size as a percentage of input size
-- (4) geometric mean of result size as a multiple of minimal equivalent size

main :: IO ()
main  = do  args      <-  getArgs
            let p      =  argsToParams args
            let (n,w)  =  case inputsource p of
                          Nothing -> (7,2)
                          Just pf -> (ofsize pf, width pf)
            input     <-  readFile ("expansions/S"++show n++"W"++show w)
            let ios    =  map (process p) (lines input)
            putStr $ reportInput (inputsource p)
            putStrLn $ ratiosFor n ios

process :: Parameters -> String -> (RE,RE)
process p s  =  (e,e')
  where
  t  =  trafo p
  e  =  readFullExp s
  e' =  transFun p $ readBeforeT t s

ratiosFor :: Int -> [(RE,RE)] -> String
ratiosFor n ios  =
    (printf "%.2f" $ (100.0 *) $ biggeomean $ map ratioOfSizes ios)
    ++"\t"++
    (printf "%.2f" $ biggeomean $ map (ratioOver n . snd) ios)

ratioOfSizes :: (RE,RE) -> Double
ratioOfSizes (x,y)  =  fromIntegral (gSize y) / fromIntegral (gSize x)

ratioOver :: Int -> RE -> Double
ratioOver n y  =  fromIntegral (gSize y) / fromIntegral n
