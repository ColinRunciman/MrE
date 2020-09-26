-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

import Data.List (isPrefixOf)
import Test.QuickCheck
import System.Environment
import RegexpCount
import System.IO

usage = "Reg [-W<no.>] [-S<no.>] [-Q<no.>] [-A]\n"

data Params  =  Params {width, size, quantity :: Int, assocQ:: Bool, report:: Bool} deriving Show

defaults  =  Params {width = 2, size = 10, quantity = 10, assocQ=False, report=False}

main = do args <- getArgs ; generateBy (resetBy args defaults)

resetBy :: [String] -> Params -> Params
resetBy []     p  =  p
resetBy (s:ss) p  =  resetBy ss $
                      case letter of
                      'W' -> p {width    = number}
                      'S' -> p {size     = number}
                      'Q' -> p {quantity = number}
                      'A' -> p {assocQ   = True}
                      'r' -> p {report   = True}
                      _   -> error usage
            where
                             '-':letter:digits  =  s
                             number             =  read digits

generateBy :: Params -> IO ()
generateBy p  =  a1 >> generateQ (quantity p) g
                 where
                 a1 =  if report p then hPutStrLn stderr (langReport (size p)(width p)) else return ()
                 g  =  case size p of
                       0 -> error "expressions of size 0 not supported by this program"
                       1 -> elements $ map Sym al
                       _ -> if assocQ p then ga else gn
                 d  =  computeDistribution (width p) (size p)
                 al =  take (width p) ['a' .. 'z']
                 ga =  generateAssocExp al (size p)
                 gn =  generateExp al d
                 s  =  langReport (size p)(width p)


generateQ :: Int -> Gen Exp -> IO ()
generateQ 0 g  =  return ()
generateQ n g  |  n > 0
               =  do
                     e <- generate g
                     print e
                     generateQ (n-1) g
