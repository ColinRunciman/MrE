module Generator where

import Expression
import Info
import Context
import Function
import OK
import Comparison
import List
import Data.List
import Control.Monad
import PreOrderTrees

type Carrier = [[RE]]

totalCarrier :: String -> Carrier
totalCarrier alpha = memo
    where
    memo = [Emp, Lam] : (map Sym alpha ++ sizeat 1) : from 2
    from n = sizeat n : from (n+1)
    sizeat n = catat n ++ altat n ++ repat n ++ optat n
    catat n = [ mkCat [x,y] | k<-[0..(n-1)], x<-memo!!k, y<-memo!!(n-k-1) ]
    altat n = [ mkAlt [x,y] | k<-[0..(n-1)], x<-memo!!k, y<-memo!!(n-k-1) ]
    repat n = [ Rep re | re <- memo !! (n-1) ]
    optat n = [ Opt re | re <- memo !! (n-1) ]    

-- Gruber Gulan Carriers, not created using createCarrier,
-- because they have even less structure
-- Gruber Gulan SSNF, without assoc
gruGul :: String -> Carrier
gruGul alpha = memo
   where
   memo = [Emp, Lam] : map Sym alpha : from 2
   from n = sizeat n : from (n+1)
   sizeat 2 = map Rep (memo!!1) ++ map Opt (memo!!1)
   sizeat n = catat n ++ altat n ++ repat n ++ optat n
   catat n = [ mkCat [x,y] | k<-[1..(n-2)], x<-memo!! k, y<-memo!!(n-k-1) ]
   altat n = [ mkAlt [x,y] | k<-[1..(n-2)], x<-memo!! k, y<-memo!!(n-k-1) ]
   repat n = [ Rep re | re <- memo !! (n-1), not (ewp re) ]
   optat n = [ Opt re | re <- memo !! (n-1), not (ewp re) ]

-- Gruber Gulan SSNF, with assoc
gruGulAssoc :: String -> Carrier
gruGulAssoc alpha = memo
   where
   memo = [Emp, Lam] : map Sym alpha : from 2
   from n = sizeat n : from (n+1)
   sizeat 2 = map Rep (memo!!1) ++ map Opt (memo!!1)
   sizeat n = catat n ++ altat n ++ repat n ++ optat n
   catat n = [ mkCat xs | k<-[1..(n-2)], x<-memo!! k, y<-memo!!(n-k-1), Just xs <- [simCat x y] ]
   altat n = [ consalt x y | k<-[1..(n-2)], x<-memo!! k, not(isAlt x), y<-memo!!(n-k-1) ]
   repat n = [ Rep re | re <- memo !! (n-1), not (ewp re) ]
   optat n = [ Opt re | re <- memo !! (n-1), not (ewp re) ]
   consalt x (Alt i xs) = mkAlt (x:xs)
   consalt x y          = mkAlt [x,y]

-- Gruber Gulan SSNF, with assoc and normalized options
gruGulAssocO :: String -> Carrier
gruGulAssocO alpha = memo
   where
   memo = [Emp, Lam] : map Sym alpha : from 2
   from n = sizeat n : from (n+1)
   sizeat 2 = map Rep (memo!!1) ++ map Opt (memo!!1)
   sizeat n = catat n ++ altat n ++ repat n ++ optat n
   catat n = [ mkCat xs
             | k<-[1..(n-2)], x<-memo!! k, y<-memo!!(n-k-1), Just xs <- [simCat x y] ]
   altat n = [ consalt x y
             | k<-[1..(n-2)], x<-memo!! k, not(isAlt x||isOpt x), y<-memo!!(n-k-1) ]
   repat n = [ Rep re | re <- memo !! (n-1), not (ewp re) ]
   optat n = [ Opt re | re <- memo !! (n-1), not (ewp re) ]
   consalt x (Alt b xs) = mkAlt (x:xs)
   consalt x y          = mkAlt [x,y]

simCat :: RE -> RE -> Maybe [RE]
simCat (Cat i1 xs) re          = Nothing
simCat re          (Cat i2 ys) = Just (re:ys)
simCat re1         re2         = Just [re1,re2]

simAlt :: RE -> RE -> Maybe [RE]
simAlt (Alt i1 xs) re          = Nothing
simAlt re          (Alt i2 ys) = justIf (re<=head ys) (re:ys)
simAlt re1         re2         = justIf (re1<=re2) [re1,re2]

createGradedCarrier :: String -> KataPred -> Carrier
createGradedCarrier alpha kp = memo
    where
    g     =  grade (khom kp)
    p     =  kpred kp
    memo = ([Emp | empP p RootCxt]++ [Lam | lamP p RootCxt]): size1 : size2 : from 3
    size1 = [ Sym c | c<-alpha, symP p NoCxt c]
    size2 = [ Rep re | re <- size1, repP p NoCxt re ] ++
            [ Opt re | re <- size1, optP p NoCxt re ]
    from n = sizeat n : from (n+1)
    sizeat n = catat n ++ altat n ++ optat n ++ repat n
    catat n = [ valOf cac
              | xs <- pluralList n, let ca=mkCat xs,
                cac <- [addContext p g ca ], hasChanged cac]
    altat n = [ valOf alc
              | xs <- pluralSet n (not . isAlt), let al=mkAlt xs,
                alc <-[addContext p g al], hasChanged alc ]
    repat n = [ Rep re | re <- memo !! (n-1), not (isOpt re || isRep re), okGradeCxt g RepCxt re ]    
    optat n = [ Opt re | re <- memo !! (n-1), not (ewp re), okGradeCxt g OptCxt re ]
    list n =  [ [x] | x <- memo !! n, not(isCat x) ] ++ pluralList n
    pluralList n = [ x:xs | k<-[1..(n-2)], x<-memo!!k, not(isCat x), xs<-list(n-k-1) ]
    set n p =  [ [x] | x <- memo !! n, p x ] ++ pluralSet n p
    pluralSet n p = [ x:xs | k<-[1..(n-2)], x<-memo!!k, p x, xs<-set(n-k-1) (\y->y>x && p y) ]

crossF :: [[a]] -> [[b]] -> (a-> Bool) -> (a->b->Bool) -> (a->b->c) -> [c]
crossF (xs:xss)(ys:yss) p q f = [ f x y | x<-xs, p x, y<-ys, q x y ] ++ crossF xss yss p q f
crossF [] _ _ _ _ = []
crossF _ [] _ _ _ = []

-- we need a predicate anyway, we may as well find simple early reasons for rejection
catCheck x       (Cat _ xs) = catCheck x (head xs)
catCheck (Opt x) (Rep y)    = x/=y
catCheck (Rep x) (Rep y)    = x/=y
catCheck (Rep x) (Opt y)    = x/=y
catCheck (Rep x) (Alt _ xs) = all (catCheck (Rep x)) xs -- too strong for fusion, OK for Minimal
catCheck x y                = True

-- stronger test for single-letter alphabet
catCheck1 x (Cat _ xs)       = all (catCheck1 x) xs
catCheck1 (Rep x) y          | swa x/=0 && ewp y = False
catCheck1 (Rep x) (Rep y)    = x<y
catCheck1 (Rep x) (Opt y)    = x/=y
catCheck1 x y                = x<=y

altCheck x (Alt _ xs) = x<head xs
altCheck x y          = x<y

catCons :: RE -> RE -> RE
catCons x (Cat _ xs) = mkCat (x:xs)
catCons x y          = mkCat [x,y]

altCons :: RE -> RE -> RE
altCons x (Alt _ xs) = mkAlt (x:xs)
altCons x y          = mkAlt [x,y]

-- True result means here: condition passed
addContext :: RecPred -> Grade -> RE -> OK RE
addContext p g e@(Alt i xs) |  not (ew i) && repP p NoCxt e && all (okGradeCxt g RepCxt) xs
                                              && altP p RepCxt i xs
                            =  changed (upgradeRE RepCxt g e)
                            |  not (ew i) && optP p NoCxt e && all (okGradeCxt g OptCxt) xs
                                              && altP p OptCxt i xs
                            =  changed (upgradeRE OptCxt g e)
                            |  altP p nc i xs && all (okGradeCxt g nc) xs
                            =  changed (upgradeRE nc g e)
                               where nc = outerCxt (ew i) NoCxt
addContext p g e@(Cat i xs) |  not(ew i) && repP p NoCxt e && catP p RepCxt i xs
                            =  changed (upgradeRE RepCxt g e)
                            |  not (ew i) && optP p NoCxt e && catP p OptCxt i xs
                            =  changed (upgradeRE OptCxt g e)
                            |  catP p nc i xs
                            =  changed (upgradeRE nc g e)
                               where nc = outerCxt (ew i) NoCxt
addContext p g e            =  unchanged e                       

linearOrderTest :: Carrier -> (RE->RE->Ordering) -> Int -> IO()
linearOrderTest car ordering cutoff = process 0
    where
    process k | k==cutoff = return ()
              | null cex  = putStrLn ("passed test at size "++show k) >> process(k+1)
              | otherwise = putStrLn ("failed test at size "++show k) >> printPairs(take 5 cex)
                where
                so=sortBy ordering (car!!k)
                cex=ltcheck so
    printPairs [] = return ()
    printPairs ((x,y):xs) = putStrLn(show x ++ " ~ " ++ show y) >> printPairs xs
    ltcheck [] = []
    ltcheck (x:xs) = [(x,y)|y<-xs, ordering x y/=LT] ++ ltcheck xs

-- check that a hom forms an algebra
-- prints samplesize many counterExamples, found within size cutOff
checkSurjectivity :: HomTrans -> Carrier -> IO()
checkSurjectivity hom carrier = surTest 2 sampleSize
    where
    surTest n ss |  n>=cutOff || ss==0
                 =  return ()
                 |  otherwise
                 =  do
                       putStrLn ("checking size " ++ show n)
                       let ex=take ss (concatMap test (toCheck n))
                       mapM_ process ex
                       surTest (n+1) (ss-length ex)
    cutOff = 14
    sampleSize = 5
    process (x,y) = putStrLn (show x++ " vs " ++ show y)
    toCheck n = map degradeTop $ carrier!!n -- lose the top grade, as we probably operate on graded carrier
    test a@(Alt _ xs) = testPair a $ falt hom xs
    test a@(Cat _ xs) = testPair a $ fcat hom xs
    test a@(Rep x)    = testPair a $ frep hom x
    test a@(Opt x)    = testPair a $ fopt hom x
    testPair x y | x==y      = []
                 | otherwise = [(x,y)]

checkSurKP :: String -> KataPred -> IO()
checkSurKP s kp = checkSurjectivity (mkHomTrans $ khom kp) (createGradedCarrier s kp)

checkAlgebra :: String -> KataPred -> IO()
checkAlgebra alpha kp = closedA 0 sampleSize
    where
    hom        = mkHomTrans (khom kp)
    cutOff     = 16 -- maximum size of arguments, then stop
    sampleSize = 10 -- maximum no of counter examples, then stop
    carrier    = createGradedCarrier alpha kp
    closedA n rmE
        | n==cutOff || rmE <=0 = return ()
        | otherwise            =
           do { putStrLn $ "checking arguments of size " ++ (show n);
                k<-checkViolations rmE (kpred kp) $
                  (applyNary hom carrier n ++ applyUnary hom carrier n);
                closedA(n+1)(rmE-k)
              }

checkViolations :: Int -> RecPred -> [(RE,RE)] -> IO Int
checkViolations _ _ []      = return 0
checkViolations 0 _ _       = return 0
checkViolations n fp (x:xs) = do
       m <- checkViolation fp x
       k <- checkViolations (n-m) fp xs
       return (m+k)

checkViolation :: RecPred -> (RE,RE) -> IO Int
checkViolation fp (re1,re2) 
    | checkWith fp re2 = return 0
    | otherwise = putStrLn (show re1 ++ " --> " ++ show re2) >> return 1

-- create unary application result at size n
applyUnary :: HomTrans -> Carrier -> Int -> [(RE,RE)]
applyUnary    h      c          n      =
    [(Rep a,frep h $ degradeTop a)|a<-c!!n] ++[(Opt a,fopt h $ degradeTop a)|a<-c!!n]

applyNary :: HomTrans -> Carrier -> Int -> [(RE,RE)]
applyNary    h      c          n      =
    [ (mkAlt xs, falt h xs)| xs<-xss ] ++ 
    [ (mkCat xs, fcat h xs)| xs<-xss]
    where xss = genList c n

genList :: Carrier -> Int -> [[RE]]
genList c 0 = [[]]
genList c n = [ r:rs | m<-[0..n-1], r<-c!!m, rs<-genList c (n-1-m)]

