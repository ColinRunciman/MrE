module Main where

import Data.Maybe
import Info
import Expression
import StarPromotion
import System.Environment
import Parameters

-- Input, Promoted, Output
data IPO = IPO {inp :: RE, pro :: RE, out :: RE}

instance Show IPO where
  show (IPO e1 e2 e3) =
    "IN:  " ++ show e1 ++ "\n" ++
    "PRO: " ++ show e2 ++ "\n" ++
    "OUT: " ++ show e3 ++ "\n"
    -- ++ grading e' ++ "\n"   (Gruber Gulan don't do grading)

main = do
  args <- getArgs
  let p = argsToParams args
  input <- contents (inputsource p)
  let ipos = catMaybes $ map (process (trafo p)) (lines input)
  mapM_ print ipos
  putStrLn ("no of expressions beyond promote: " ++ (show $ length ipos))

process :: Grade -> String -> Maybe IPO
process g s  |  e1==e'
             =  Nothing
             |  otherwise
             =  Just (IPO { inp=e, pro=e1, out=e' })
  where
  e  =  readBeforeT g s
  e1 =  promote e
  e' =  transFun g e



