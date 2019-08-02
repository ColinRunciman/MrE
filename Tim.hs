module Main where

import Alphabet
import Data.List (sort)
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
import Context
-- import Gruber

shrinkBound :: Int
shrinkBound = 80 -- up to 100 is OK

localshrinkEX :: Extension
localshrinkEX = mkExtension (altSizeBound shrinkBound shrinkAltList)
                            (catSizeBound shrinkBound shrinkCatList) minByCatalogueKP Shrunk

localshrink :: RE -> RE
localshrink x = valOf $ katahom (trg localshrinkEX) NoCxt x

pressBound :: Int
pressBound = 20 -- up to 40 is OK

localpressEX = mkExtension (altSizeBound pressBound pressPressAltListOne)
                           (catSizeBound pressBound pressCatListOne) (target localshrinkEX) Pressed

localpress :: RE -> RE
localpress x = valOf $ katahom (trg localpressEX) NoCxt x

-- Input, Time, Output
data ITO = ITO {inp :: RE, tim :: Float, out :: RE}

instance Show ITO where
  show (ITO e t e') =
    "IN:  " ++ show e ++ "\n" ++
    showFFloat Nothing t "" ++ " seconds\n" ++
    "OUT: " ++ show e' ++ "\n"
    -- ++ grading e' ++ "\n"   (Gruber Gulan don't do grading)

instance Eq ITO where
  (ITO _ t0 _) == (ITO _ t1 _)  =  t0 == t1

instance Ord ITO where
  (ITO _ t0 _) <= (ITO _ t1 _)  =  t0 <= t1

asPercentageOf :: Int -> Int -> Float
x `asPercentageOf` y  =  float (100 * x) / float y

float :: Int -> Float
float = fromInteger . toInteger

isTotal :: RE -> Bool
isTotal (Rep x) = swa x==(charSet (alpha x))
isTotal _       = False

countTotal :: [ITO] -> Int
countTotal is = length $ (filter (isTotal . out)) is

main = do
  input <- getContents
  let itos = sort $ map process (lines input)
  mapM_ print itos
  putStrLn $ "total output size as percentage of total input size: " ++
             show ((sum $ map (size . out) itos) `asPercentageOf` (sum $ map (size . inp) itos)) ++
--             show ((sum $ map (oldSize . out) itos) `asPercentageOf` (sum $ map (oldSize . inp) itos)) ++
             " %\n" ++
             "total time: " ++ (showFFloat Nothing (sum $ map tim itos) "") ++
             "\npercentage of total languages: " ++ (show (countTotal itos `asPercentageOf` length itos))

ymain = do
  input <- getContents
  let itos = map process (lines input)
  mapM_ print itos

process :: String -> ITO
process s  =  ITO e t e' -- ITO (re eg) te e''  --ITO e t e'
  where
  e  =  read s
--  eg =  read s
--  et =  blop eg
--  eu =  blopEWP eg
  e0 =  fuse e
  e1 =  promote e
  e2 =  syncat e1
  e3 =  localshrink e2
  e4 =  localpress e3 
  e5 =  C.catalogue e1
  e6 =  press e1
  e7 =  topshrink e2 
  e' =  e5 -- change this to e1/e4/whatever for a weaker/stronger trafo
--  e'' = eu -- or et
  t  =  timeToCompute e e' (size e' <= size e)
--  te =  timeToCompute (re eg) e'' (ggsize eg >= oldSize e'') -- different as GG use a different parser

timeToCompute :: RE -> RE -> Bool -> Float
timeToCompute e0 e1 x  =  unsafePerformIO $ do
  t0  <-  getCurrentTime
  compute
  t1  <-  getCurrentTime
  return $ fromRational $ toRational $ utctDayTime t1 - utctDayTime t0
  where
  compute | x  =  return ()
          | otherwise = error $ show e0 ++ " expanded to " ++ show e1 ++ "!"

