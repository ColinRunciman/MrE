module Generator where

import Expression
import Info
import Context
import Function
import Comparison
--import Normalization
import Fuse
import StarPromotion
import Pressing
{-
import Factorization
import Refactorization
import Shrinking
import Stellation
-}
import Shrinking
import List
import Data.List
import Control.Monad
import PreOrderTrees
--import AutIntersect
import StarRecognition
-- TO DO: move RecPreds into RegularTrans to replace predicates there.

type Alphabet = String
type Carrier = [[RE]]

totalCarrier :: Alphabet -> Carrier
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
gruGul :: Alphabet -> Carrier
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
gruGulAssoc :: Alphabet -> Carrier
gruGulAssoc alpha = memo
   where
   memo = [Emp, Lam] : map Sym alpha : from 2
   from n = sizeat n : from (n+1)
   sizeat 2 = map Rep (memo!!1) ++ map Opt (memo!!1)
   sizeat n = catat n ++ altat n ++ repat n ++ optat n
   catat n = [ mkCat xs | k<-[1..(n-2)], x<-memo!! k, y<-memo!!(n-k-1), (c,xs) <- simCat x y ]
   altat n = [ consalt x y | k<-[1..(n-2)], x<-memo!! k, not(isAlt x), y<-memo!!(n-k-1) ]
   repat n = [ Rep re | re <- memo !! (n-1), not (ewp re) ]
   optat n = [ Opt re | re <- memo !! (n-1), not (ewp re) ]
   consalt x (Alt i xs) = mkAlt (x:xs)
   consalt x y          = mkAlt [x,y]

-- Gruber Gulan SSNF, with assoc and normalized options
gruGulAssocO :: Alphabet -> Carrier
gruGulAssocO alpha = memo
   where
   memo = [Emp, Lam] : map Sym alpha : from 2
   from n = sizeat n : from (n+1)
   sizeat 2 = map Rep (memo!!1) ++ map Opt (memo!!1)
   sizeat n = catat n ++ altat n ++ repat n ++ optat n
   catat n = [ mkCat xs | k<-[1..(n-2)], x<-memo!! k, y<-memo!!(n-k-1), (c,xs) <- simCat x y ]
   altat n = [ consalt x y | k<-[1..(n-2)], x<-memo!! k, not(isAlt x||isOpt x), y<-memo!!(n-k-1) ]
   repat n = [ Rep re | re <- memo !! (n-1), not (ewp re) ]
   optat n = [ Opt re | re <- memo !! (n-1), not (ewp re) ]
   consalt x (Alt b xs) = mkAlt (x:xs)
   consalt x y          = mkAlt [x,y]

simCat :: RE -> RE -> [(Bool,[RE])]
simCat (Cat i1 xs) re          = []
simCat re          (Cat i2 ys) = [(ew i2&&ewp re, re:ys)]
simCat re1         re2         = [(ewp re1 && ewp re2, [re1,re2])]

simAlt :: RE -> RE -> [(Bool,[RE])]
simAlt (Alt i1 xs) re          = []
simAlt re          (Alt i2 ys) = [(ew i2||ewp re,re:ys) | re<=head ys]
simAlt re1         re2         = [(ewp re1||ewp re2,[re1,re2]) | re1<=re2 ]

{-
 - this does not work well anymore under the graded regime
createCarrier :: Alphabet -> RecPred -> Carrier
createCarrier alpha p = memo
    where
    memo = ([Emp | empP p RootCxt]++ [Lam | lamP p RootCxt]): size1 : size2 : from 3
    size1 = [ Sym c | c<-alpha, symP p NoCxt c]
    size2 = [ Rep re | re <- size1, repP p NoCxt re ] ++ [ Opt re | re <- size1, optP p NoCxt re ]
    from n = sizeat n : from (n+1)
    sizeat n = catat n ++ altat n ++ optat n ++ repat n
    catat n = [ ca | k<-[1..(n-2)], a<-memo !! k, not(isCat a),
                                          b<-memo !! (n-k-1), (c,xs)<-simCat a b,
                                          let Cat i _ =mkCat xs, catP p c i xs ]
    altat n = [ al | k<-[1..(n-2)], a<-memo !! k, not(isAlt a),
                                          b<-memo !! (n-k-1), (c,xs)<-simAlt a b,
                                          let Alt i _=mkAlt xs, altP p c i xs ]
    repat n = [ Rep re | re <- memo !! (n-1), repP p NoCxt re ]    
    optat n = [ Opt re | re <- memo !! (n-1), optP p NoCxt re ]
-}

createGradedCarrier :: Alphabet -> Grade-> RecPred -> Carrier
createGradedCarrier alpha g p = memo
    where
    memo = ([Emp | empP p RootCxt]++ [Lam | lamP p RootCxt]): size1 : size2 : from 3
    size1 = [ Sym c | c<-alpha, symP p NoCxt c]
    size2 = [ Rep re | re <- size1, repP p NoCxt re ] ++ [ Opt re | re <- size1, optP p NoCxt re ]
    from n = sizeat n : from (n+1)
    sizeat n = catat n ++ altat n ++ optat n ++ repat n
    catat n = [ cac | xs <- pluralList n, let ca=mkCat xs, (cac,True)<-[addContext p g ca ]]
    altat n = [ alc | -- k<-[1..(n-2)], a<-memo !! k, not(isAlt a),
                                     -- b<-memo !! (n-k-1), (c,xs)<-simAlt a b,
                      xs <- pluralSet n (not . isAlt),
                      let al=mkAlt xs, (alc,True)<-[addContext p g al] ]
    repat n = [ Rep re | re <- memo !! (n-1), not (isOpt re || isRep re), okGradeCxt g RepCxt re ]    
    optat n = [ Opt re | re <- memo !! (n-1), not (ewp re), okGradeCxt g OptCxt re ]
    list n =  [ [x] | x <- memo !! n, not(isCat x) ] ++ pluralList n
    pluralList n = [ x:xs | k<-[1..(n-2)], x<-memo!!k, not(isCat x), xs<-list(n-k-1) ]
    set n p =  [ [x] | x <- memo !! n, p x ] ++ pluralSet n p
    pluralSet n p = [ x:xs | k<-[1..(n-2)], x<-memo!!k, p x, xs<-set(n-k-1) (\y->y>x && p y) ]

-- note that 'isFused' is even overkill here, it suffices to check the root node
minimalCarrier :: Alphabet -> Carrier
minimalCarrier alpha = memo
    where
    n           = length alpha
    cc          = if n==1 then catCheck1 else catCheck
    memo        = [Emp,Lam]:size1:size2:from 3 tree0 [size2,size1]
    tree0       = buildTree compRE (size1++size2)
    size1       = map Sym alpha
    size2       = map Rep size1 ++ map Opt size1
    from n t sm = ns : from (n+1) t' (ns : sm)
                  where t' = next n t sm
                        ns = getPairs n (classReps t')
    next n t sm = addUniqTree compRE (map minimalAssert $ candat n sm) t -- assertion only correct for those that go into the tree
    candat n (h:t) = chainSort $ altat n t smb ++ catat n t smb ++ repat n nh ++ optat n nh
                     where 
                     smb = reverse t
                     nh  = filter (not . ewp) h
    catat n sf sb  = [ ca |  ca <- crossF sf sb (not.isCat) catCheck catCons, isFused ca ]                         
    altat n sf sb  = [ al |  al <- crossF sf sb (\x->not(isAlt x || isOpt x)) altCheck altCons, isFused al ]
    repat n h =  [ re | rb <- h, let re=Rep rb, isFused re]  
    optat n h =  [ re | rb <- h, let re=Opt rb, isFused re]  

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

    

-- TO DO: the extracted REs could be labeled Minimal
getPairs :: Int -> [RE] -> [RE]
getPairs n xs = filter ((==n).size) xs

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


--normA alpha = createCarrier alpha normP
--normA alpha = createGradedCarrier alpha Normal normP

fuseA alpha = createGradedCarrier alpha Fused fuseP
promoteA alpha = createGradedCarrier alpha Promoted promoteP

{-
--pressA alpha = createCarrier alpha pressP -}
pressA alpha = createGradedCarrier alpha Pressed pressP

{-
refactA alpha = createGradedCarrier alpha Refactorized refactP
-}
shrinkA alpha = createGradedCarrier alpha Shrunk shrinkP
{-
stelA alpha = createGradedCarrier alpha Stellar stelP
-}
{- currently hidden
shrunkP :: RecPred
shrunkP = factP { altP=altShrinkP, catP=catShrinkP, repP=repShrinkP, optP=optShrinkP }

altShrinkP pa b xs = altP factP pa b xs && null ss && null cs
    where
    ss = [xs' | xs' <- shrunkenAltList xs, normAlt xs `sublang` normAlt xs']
    cs = [xs' | xs' <- coShrunkenAltList xs, normAlt xs' `sublang` normAlt xs]
catShrinkP pa b xs = catP factP pa b xs && null ss && null cs
    where
    ss = [xs' | xs' <- shrunkenCatList xs, normCat xs `sublang` normCat xs']
    cs = [xs' | xs' <- coShrunkenCatList xs, normCat xs' `sublang` normCat xs]
repShrinkP x = repP factP x && null ss && null cs
    where
    ss = [x'  | x' <- shrunken x, normRep x `sublang` normRep x']
    cs = [x'  | x' <- coShrunken x, normRep x' `sublang` normRep x]
optShrinkP x = optP factP x && null ss && null cs
    where
    ss = [x'  | x' <- shrunken x, normOpt x `sublang` normOpt x']
    cs = [x'  | x' <- coShrunken x, normOpt x' `sublang` normOpt x]
-}

-- predicates for stellar expressions, using sublang
{-
stellarP :: RecPred
stellarP = shrunkP { altP=stellarAltP, catP=stellarCatP, optP= \x->optP shrunkP x&& not(isTransitive (Opt x)) }

stellarAltP pa b xs = altP shrunkP pa b xs &&
                   not (or [ isTransitive (normAlt ys)
                           | ys <- sublists xs,
                             plural ys, any ewp ys, any hasRep ys ])
stellarCatP pa b xs = catP shrunkP pa b xs &&
                   not (or [ isTransitive (normCat ys)
                           | ys <- segments xs,
                             plural ys, all ewp ys, any hasRep ys ])

stellarA alpha = createCarrier alpha stellarP
-}

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
    toCheck n = carrier!!n
    test a@(Alt _ xs) = testPair a $ falt hom xs
    test a@(Cat _ xs) = testPair a $ fcat hom xs
    test a@(Rep x)    = testPair a $ frep hom x
    test a@(Opt x)    = testPair a $ fopt hom x
    testPair x y | x==y      = []
                 | otherwise = [(x,y)]

{-
-- checking that hom/carrier form an algebra
checkAlgebra  :: Alphabet -> HomTrans -> RecPred -> IO()
checkAlgebra alpha hom fp = closedA 0 sampleSize
    where
    cutOff=16 -- maximum size of arguments, then stop
    sampleSize=10 -- maximum no of counter examples, then stop
    carrier = createCarrier alpha fp
    closedA n rmE
        | n==cutOff || rmE <=0 = return ()
        | otherwise            =
           do { putStrLn $ "checking arguments of size " ++ (show n);
                k<-checkViolations rmE fp $ (applyNary hom carrier n++
                                             applyUnary hom carrier n);
                closedA(n+1)(rmE-k)
              }
-}


checkAlgebra :: Alphabet -> Katahom -> RecPred -> IO()
checkAlgebra alpha kahom fp = closedA 0 sampleSize
    where
    hom = mkHomTrans kahom
    cutOff=16 -- maximum size of arguments, then stop
    sampleSize=10 -- maximum no of counter examples, then stop
    carrier = createGradedCarrier alpha (grade kahom) fp
    closedA n rmE
        | n==cutOff || rmE <=0 = return ()
        | otherwise            =
           do { putStrLn $ "checking arguments of size " ++ (show n);
                k<-checkViolations rmE fp $ (applyNary hom carrier n++
                                             applyUnary hom carrier n);
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
    [(Rep a,frep h a)|a<-c!!n] ++[(Opt a,fopt h a)|a<-c!!n]

applyNary :: HomTrans -> Carrier -> Int -> [(RE,RE)]
applyNary    h      c          n      =
    [ (mkAlt xs, falt h xs)| xs<-xss ] ++ 
    [ (mkCat xs, fcat h xs)| xs<-xss]
    where xss = genList c n

genList :: Carrier -> Int -> [[RE]]
genList c 0 = [[]]
genList c n = [ r:rs | m<-[0..n-1], r<-c!!m, rs<-genList c (n-1-m)]

onePer :: Int -> [a] -> [a]
onePer n []  =  []
onePer n xs  =  head xs : onePer n (drop n xs)

bad1, bad2, bad3, bad4, bad5 :: RE
bad1= read "(a?(bab*)?*ba?)***?"
bad2= read "(a?ba*?a?(a+b+(a?(ab?aaa?)*?(a+aa))?))*"
bad3= read "(((a+bb)((a+(a+b)*+a?)b?*+b*))*?(b(a+b)baa??abb?b?*)?**\
            \(b+b*a+a?+a?)?ba**aa*a)*"
bad4= read "((a+b+(b+aa*)*+((a+b)?b((a+b+b?)***??(aa)??+(b+b)*))?)\
            \((b+b+bbba)(b+a*+b?)(a+a*a?+b?b)(a**(aa*?a)?)?a(a+a)a(\
            \(b*?a+a*)*a*ba)*?*(aa?b)?a(b+((a+b)?a?)?)?+(a+b*)*aab)?\
            \a*?b)**"
bad5= read "((a+b+c+d+e+f+g+h)*b(a+e*)((f(b+c+e+h)*(a+b+c+g+h)*(d(h+cd+e*(d?g)*+h*e))?)*b?(c+e+gg)\
            \(cg+e?a?+(b(d+e*))*)((a+b+(e+h)e?)(h+be?)*+(c+ga*f*)?(((b+d+g)*+(c+h)*)\
            \(a+bh*)*(f+ga*)(f+g+aa))?)(ef+(d+bc)?((b+d)?f)*((h+b*)d)?+(d+g)*))*)*"
