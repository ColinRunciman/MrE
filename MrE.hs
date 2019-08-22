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
  mapM_ (putStrLn . stringTrafo (trafo p)) (lines input)



