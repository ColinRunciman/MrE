module Main where

import Data.List (sort)
import Expression
import Parameters

import System.Environment
import Data.Time.Clock
import System.IO.Unsafe (unsafePerformIO)
import Numeric
import Info
import Alphabet

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
isTotal (Rep x)  =  swa x == alpha x
isTotal _        =  False

countTotal :: [ITO] -> Int
countTotal is = length $ (filter (isTotal . out)) is

effectITOs :: Trafo -> [ITO] -> Float
effectITOs t itos = (sum $ map (sizeForT t . out) itos) `asPercentageOf` (sum $ map (sizeForT t . inp) itos)

totalITOs :: [ITO] -> Float
totalITOs itos = countTotal itos `asPercentageOf` length itos

totalTime :: [ITO] -> Float
totalTime itos = sum $ map tim itos

averageTime :: [ITO] -> Float
averageTime itos = sum (map tim itos) / fromIntegral (length itos)

showTime :: Float -> String
showTime f = showFFloat Nothing f ""

main = do
  args <- getArgs
  let par = argsToParams args
  input <- contents (inputsource par)
  let itos = map (process (trafo par)) $ lines input
  if verbose par then verboseContinuation itos par
  else plainContinuation itos par

verboseContinuation :: [ITO] -> Parameters -> IO ()
verboseContinuation itos p = do
    mapM_ print $ sort itos
    putStrLn $ "total output size as percentage of total input size: " ++
             show (effectITOs (trafo p) itos) ++
             " %\n" ++
             "total time: " ++
             showTime (totalTime itos) ++
             "\npercentage of total languages: " ++ (show $ totalITOs itos)

-- just reporting average time per item and where the input came from
plainContinuation :: [ITO] -> Parameters -> IO ()
plainContinuation itos p = do
    putStrLn $ reportInput (inputsource p) ++ showTime (averageTime itos)

process :: Trafo -> String -> ITO
process tr s  =  ITO e t e'
  where
  e  =  readBeforeT tr s
  e' =  transFun tr e
  t  =  timeToCompute e e' (sizeForT tr e' <= sizeForT tr e)


timeToCompute :: RE -> RE -> Bool -> Float
timeToCompute e0 e1 x  =  unsafePerformIO $ do
  t0  <-  getCurrentTime
  compute
  t1  <-  getCurrentTime
  return $ fromRational $ toRational $ utctDayTime t1 - utctDayTime t0
  where
  compute | x  =  return ()
          | otherwise = error $ show e0 ++ " expanded to " ++ show e1 ++ "!"

