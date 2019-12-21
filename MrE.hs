module Main where

import System.Environment
import Parameters

-- MrE simplies REs given as a command-line arguments, or if there is
-- no RE argument, the REs on successive stdinput lines.
-- default trafo is Promote, default input is stdin

main = do
  args <- getArgs
  let p = argsToParams args
  input <- contents (inputsource p)
  process p (lines input)

process :: Parameters -> [String] -> IO()
process p ss | verbose p
             = sequence_ [ putStrLn (show n++". "++ f s)
                         | (n,s)<-zip [1..] ss ]
             | otherwise
             = mapM_ (putStrLn . f) ss
               where
               f = stringTransFun (trafo p)

