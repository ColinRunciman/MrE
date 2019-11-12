import Data.List (isPrefixOf)
import Test.QuickCheck
import System.Environment
import RegexpCount

usage = "Reg [-w<no.>] [-s<no.>] [-q<no.>] [-a]\n"

data Params  =  Params {width, size, quantity :: Int, assocQ:: Bool} deriving Show

defaults  =  Params {width = 2, size = 10, quantity = 10, assocQ=False}

main = do args <- getArgs ; generateBy (resetBy args defaults)

resetBy :: [String] -> Params -> Params
resetBy []     p  =  p
resetBy (s:ss) p  =  resetBy ss $
                     case letter of
                     'w' -> p {width    = number}
                     's' -> p {size     = number}
                     'q' -> p {quantity = number}
                     'a' -> p {assocQ   = True}
                     _   -> error usage
                     where
                       '-':letter:digits  =  s
                       number             =  read digits

generateBy :: Params -> IO ()
generateBy p  =  generateQ (quantity p) g
                 where
                 g  =  case size p of
                       0 -> error "expressions of size 0 not supported by this program"
                       1 -> elements $ map Sym al
                       _ -> if assocQ p then ga else gn
                 d  =  computeDistribution (width p) (size p)
                 al =  take (width p) ['a' .. 'z']
                 ga =  generateAssocExp al (size p)
                 gn =  generateExp al d


generateQ :: Int -> Gen Exp -> IO ()
generateQ 0 g  =  return ()
generateQ n g  |  n > 0
               =  do
                     e <- generate g
                     print e
                     generateQ (n-1) g


