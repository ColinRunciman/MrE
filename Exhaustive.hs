module Main where
-- produce the exhaustive list of all expressions
-- of the specified size and width that are normal forms of the specified trafo
-- if the verbose flg is set they are HopCroft-Ullman-ed first
-- printed to stdout

import System.Environment
import Parameters
import Generator

import AutIntersect

main = do
  args <- getArgs
  let p = argsToParams args
  let kp = transKP (trafo p)
  let Just pf = inputsource p
  let w = width pf
  let s = ofsize pf
  let xs = createGradedCarrier (take w ['a'..]) kp !! s
  if   verbose p then mapM_ (print . hu_extract . convertNice) xs
  else mapM_ print xs
