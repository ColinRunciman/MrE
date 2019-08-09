module Main where

import Data.List (sort)
import Data.Maybe
import Expression
import Pressing
import Fuse
import StarPromotion
import Shrinking
import TopShrink
import SyntaxCatalogue -- was ProfileCatalogue
import qualified Catalogue as C
import System.Environment
import Data.Time.Clock
import System.IO.Unsafe (unsafePerformIO)
import Numeric
import Info
import OK
import Context

shrinkBound :: Int
shrinkBound = 80 -- up to 100 is OK

localshrinkEX :: Extension
localshrinkEX = mkExtension (altSizeBound shrinkBound shrinkAltList)
                            (catSizeBound shrinkBound shrinkCatList) minByCatalogueKP Shrunk

localshrink :: RE -> RE
localshrink x = valOf $ katahom (trg localshrinkEX) NoCxt x

pressBound :: Int
pressBound = 20 -- up to 40 is OK

localpressEX = mkExtension (altSizeBound pressBound pressAltListOne)
                           (catSizeBound pressBound pressCatListOne) (target localshrinkEX) Pressed

localpress :: RE -> RE
localpress x = valOf $ katahom (trg localpressEX) NoCxt x

-- Input, Promoted, Output
data IPO = IPO {inp :: RE, pro :: RE, out :: RE}

instance Show IPO where
  show (IPO e1 e2 e3) =
    "IN:  " ++ show e1 ++ "\n" ++
    "PRO: " ++ show e2 ++ "\n" ++
    "OUT: " ++ show e3 ++ "\n"
    -- ++ grading e' ++ "\n"   (Gruber Gulan don't do grading)

main = do
  input <- getContents
  let ipos = catMaybes $ map process (lines input)
  mapM_ print ipos
  putStrLn ("no of expressions beyond promote: " ++ (show $ length ipos))

process :: String -> Maybe IPO
process s  |  e1==e'
           =  Nothing
           |  otherwise
           =  Just (IPO { inp=e, pro=e1, out=e' })
  where
  e  =  read s
  e1 =  promote e
  e2 =  valOf $ minByCatalogue e1
  e3 =  localshrink e2
  e4 =  localpress e3 
  e5 =  valOf $ C.minByCatalogue e1
  e6 =  press e1
  e7 =  topshrink e2 
  e' =  e3 -- change this to e3/e4/whatever for a weaker/stronger trafo



