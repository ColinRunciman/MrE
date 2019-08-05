module Main where

import Data.List (sort)
import Expression

import Context
import Fuse
import StarPromotion

import List
import Gluchkov
import AutIntersect

asPercentageOf :: Int -> Int -> Float
x `asPercentageOf` y  =  float (100 * x) / float y

float :: Int -> Float
float = fromInteger . toInteger

mainOld = do
  input <- getContents
  let ls = lines input
  let nr = length ls
  let re = map read ls
  let fu = map fuse re
  let pr = map promote fu
  let as = map (\x -> 1 + width x) re
  let rs = map cuSize re
  let bs = map cuSize fu
  let cs = map cuSize pr
  let au = map gluchkov re
  let su = map noStates au
  let a2 = map langQuotient au
  let s2 = map noStates a2
  let a3 = map semanticStateMin a2
  let s3 = map noStates a3
  putStrLn $ "number of REs:\t\t\t\t\t" ++ show nr
  putStrLn $ "average Gluchkov size:\t\t\t\t" ++ show (averageD as)
  --putStrLn $ "average Gluchkov after left quotient:\t\t" ++ show (averageD (map fst es))
  --putStrLn $ "average Gluchkov after both quotients:\t\t" ++ show (averageD (map snd es))
  --putStrLn $ "average NFA size, raw unfolding:\t\t" ++ show (averageD rs)
  --putStrLn $ "average NFA size, fused:\t\t\t" ++ show (averageD bs)
  --putStrLn $ "ditto, promoted:\t\t\t\t" ++ show (averageD cs)
  putStrLn $ "quotiented by lang equivalence, right:\t\t" ++ show (averageD s2)
  putStrLn $ "fixpoint, by eitherway lang equivalent:\t\t" ++ show (averageD s3)

main :: IO ()
main = do
  input <- getContents
  let ls = lines input
  let nr = length ls
  let re = map read ls
  sequence_ $ map process (zip [1..] re)

process :: (Int,RE) -> IO()
process (n,re) = do
    putStrLn $ show n ++ ": " ++ show re
    let a = gluchkov re
    putStrLn "gluchkov:"
    processNFA a
    let b = compactUnfolding kataGradeKatahom re
    putStrLn "partial derivatives, using plain katahom"
    processNFA b
    let c = compactUnfolding promoteK re
    putStrLn "partial derivatives, using promote scheme"
    processNFA c
    putStrLn "===================================================="

processNFA :: (Ord a,Show a) => NFA a Char -> IO()
processNFA nfa = do
    putStrLn $ "initial size:\t"  ++ show (noStates nfa)
    putStrLn $ "after bisim:\t"   ++ show (noStates nfa2)
    putStrLn $ "after simtrim:\t" ++ show (noStates nfa3)
    putStrLn $ "extracted exp:\t" ++ show ne
    putStrLn $ "other scheme:\t"  ++ show ne2
    putStrLn $ "---------------------------------------------------------------"
    where
    nfa2 = semanticStateMin nfa
    nfa3 = simulationQuotient2 nfa2
    ne   = extractRE nfa3
    ne2  = extractRE1 nfa3


-- in percentage
average :: [Int]->Int
average xs = (sum xs * 100) `div` length xs

percConvert :: Int -> Double
percConvert x = fromIntegral x / 100

averageD = percConvert . average

noStates :: NFA a b -> Int
noStates nfa = length $ states  nfa







