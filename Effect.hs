module Main where

import Info
import Context
import Data.List (isPrefixOf)
import Expression
import Pressing
import StarPromotion
import Stellation
import Catalogue
import SyntaxCatalogue (syncat)
import System.Environment
import GruberP
import Fuse

-- Effect runs a transformation on random input data
-- and outputs how effective the trafo is on inputs of varying
-- alphabet/expression sizes

-- the trafo is selected  as it would in MrE

-- -q quick mode: promote only
-- -p press: will be slow for large expressions
-- -m minimizing mode: stellation + minimization using semantic catalogues
-- -z pressing after using the catalogue

usage = "MrE [-q | -m | -p | -c | -s | -z | -k | -y ] re1 re2 ...\n"

stelEX2 :: Extension
stelEX2 = mkExtension altTrans catTrans (target minByCatalogueExtension) Stellar
catalogueStellate = mkTransform (khom (target stelEX2))


-- Note this uses 'Stellar' as a tag, because Pressed is below Catalogued in the order
pressEX2 :: Extension
pressEX2 = mkExtension pressPressAltListOne pressCatListOne (target minByCatalogueExtension) Stellar
cataloguePress = mkTransform (khom (target pressEX2))

sizes :: [Int]
sizes = -- [10,20,30,40,50,100,250,500,1000,10000]
        [10,20,40,80,160,320,640,1280,2560]

alphaSizes :: [Int]
alphaSizes = [1,2,3,4,8,16]

processFile :: Int -> Int -> (String -> Int) -> IO()
processFile eSize aSize trafo =
   do 
       inp <- readFile $ "populations/s" ++ eString ++ "w" ++ aString
       let lns  = lines inp
       let n    = length lns -- normally: 1000
       let outs = sum $ map trafo lns
       let average = (fromIntegral outs / fromIntegral n) :: Double
       putStrLn $ eString ++ "\t" ++ aString ++ "\t" ++ show average
   where
   eString = show eSize
   aString = show aSize

main = do
  args <- getArgs
  let trafo = interpret args
  sequence_ [ processFile esi asi trafo | esi <- sizes, asi <- alphaSizes]

interpret :: [String] -> String->Int
interpret args = simple
  where
  promread           = promote . read {- standard strategy: reduce size via promotion first -}
  (optArgs, inpArgs) = span ("-" `isPrefixOf`) args
  simple = case optArgs of
           []     -> size . promread {- default: promotion; it's fast, but not superfast -}
           ["-s"] -> size . stellate . promread 
           ["-q"] -> size . fuse . read    {- fusion is faster than promotion -}
           ["-m"] -> size . catalogueStellate . promread
           ["-c"] -> size . catalogue . promread
           ["-p"] -> size . press . promread {- let press not even see the whole thing -}
           ["-z"] -> size . cataloguePress . promread
           ["-l"] -> gSize . linearTrans -- uses dedicated parser to maintain linearity
           ["-k"] -> size . kataGrade . read
           ["-y"] -> size . syncat . promread

