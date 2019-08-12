module Shrinking (
  ShrunkRE,
  shrink, shrinkP, shrinkKP, shrinkCxt, shrinkRep, shrinkAltList, shrinkCatList,
  isShrunk) where

import List (itemRest, segPreSuf, splits, powerSplits)
import Expression
import OK
import Comparison
import Fuse
import StarPromotion
import Context
import Info

-- EXPERIMENT:
-- (1) after fusion
-- (2) simple cat ends not *mostCom

lMostCom' :: RE -> [(RE,[RE])]
lMostCom' (Cat _ xs)  =  [(head xs, tail xs)]
lMostCom' y           =  [(y,[])]
          
rMostCom' :: RE -> [([RE],RE)]
rMostCom' (Cat _ xs)  =  [(init xs, last xs)]
rMostCom' y           =  [([],y)]

lMostComList :: [RE] -> [(RE,[RE])]
lMostComList []  =  []
lMostComList xs  =  [(head xs, tail xs)]

rMostComList :: [RE] -> [([RE],RE)]
rMostComList []  =  []
rMostComList xs  =  [(init xs, last xs)]

-- FURTHER EXPERIMENT
-- (3) bounded-depth shrinkage

shrinkDepth, coShrinkDepth :: Int
shrinkDepth    =  100
coShrinkDepth  =  100

-- Shrinking is a generate-and-test method.  It lazily generates
-- variants of x with something missed out, but in a way that
-- ensures L(x') <= L(x) (or vice versa: co-shrinking).  It tests such x' to see if in fact
-- L(x) <= L(x') is also true.  If so, voila! -- a simpler x.

type ShrunkRE = RE

isShrunk :: RE -> Bool
isShrunk = checkWith shrinkP

shrinkEX :: Extension
shrinkEX = mkExtension shrinkAltList shrinkCatList promoteKP Shrunk

shrinkK :: Katahom
shrinkK = khom shrinkKP

shrinkKP :: KataPred
shrinkKP = target shrinkEX

shrinkP :: RecPred
shrinkP = kpred shrinkKP

Katahom { kalt = shrinkAltK, kcat = shrinkCatK } = shrinkK

shrinkH = mkHomTrans shrinkK
HomTrans { falt = shrinkAlt, fcat = shrinkCat, frep = shrinkRep, fopt = shrinkOpt } = shrinkH

shrink = mkTransform shrinkK

shrinkCxt :: Cxt -> RE -> OK RE
shrinkCxt = katahom shrinkK

globalShrink :: RE -> OK RE
globalShrink x = fixOK (globalShrinkCxt NoCxt) x

globalShrinkCxt :: Cxt -> RE -> OK RE
globalShrinkCxt c (Alt i xs) = ifchanged(shrinkAltList c' i xs) (changed . fuseAlt)(unchanged . Alt i)
                               where c' = if ew i then max OptCxt c else c
globalShrinkCxt c (Cat i xs) = ifchanged(shrinkCatList c i xs) (changed . fuseCat)(unchanged . Cat i)
                               where c' = if ew i then max OptCxt c else c
globalShrinkCxt c (Rep x)    = ifchanged(globalShrinkCxt RepCxt x) (changed . fuseRep) (unchanged . Rep)
globalShrinkCxt c (Opt x)    = ifchanged(globalShrinkCxt OptCxt x) (changed . fuseOpt) (unchanged . Opt)
globalShrinkCxt c x          = unchanged x

-- end of boilerplate section

shrunkenCatList :: Int -> [FuseRE] -> [[FuseRE]] -- the Cxt might be used
shrunkenCatList d xs  =  [ xs'
                         | (as,[x],bs) <- segPreSuf 1 xs,
                           xs' <- [as++bs | ewp x] ++
                                  [as++[unOpt x]++bs | isOpt x] ++
                                  [as++[unRep x]++bs | isRep x] ++
                                  [ as ++ [x'] ++ bs
                                  | x' <- shrunken (d-1) x] ] ++
                         [ xs'
                         | (pre,suf) <- splits xs,
                           (pre',x) <- rMostComList pre,
                           (y,suf') <- lMostComList suf,
                           xs' <- [ pre' ++ [xy'] ++ suf'
                                  | xy' <- shrunkenCat2Seg [x,y] ]]

shrunkenCat2Seg :: [FuseRE] -> [FuseRE]
shrunkenCat2Seg [Opt x, Opt y]  =  [promoteOpt $ promoteCat [x,y],
                                    promoteOpt $ promoteAlt [x,y]]
shrunkenCat2Seg [Rep x, Opt y]  =  [promoteAlt $ [Rep x, y]]
shrunkenCat2Seg [Opt x, Rep y]  =  [promoteAlt $ [x, Rep y]]
shrunkenCat2Seg _               =  []

coShrunkenCatList :: Int -> [FuseRE] -> [[FuseRE]]
coShrunkenCatList d xs  =  [ xs'
                           | (as,[x],bs) <- segPreSuf 1 xs,
                             xs' <- [ as ++ [x'] ++ bs
                                    | x' <- coShrunken (d-1) x] ] ++
                           [ xs'
                           | (pre,suf) <- splits xs,
                             (pre',x) <- rMostCom' $ mkCat pre,
                             (y,suf') <- lMostCom' $ mkCat suf,
                             xs' <- [ pre' ++ [xy'] ++ suf'
                                    | xy' <- coShrunkenCat2Seg [x,y] ]]

-- includes rules such as x(x*y)? -> x+x*y
coShrunkenCat2Seg :: [FuseRE] -> [FuseRE]
coShrunkenCat2Seg [Rep x, Rep y]  =  [promoteRep $ promoteAlt [x,y]]
coShrunkenCat2Seg [Rep x, Opt(Cat _ ys) ] 
                                  |  head ys == x
                                  =  [ promoteCat[Rep x, promoteOpt(mkCat(tail ys))] ] 
                                  |  isCat x && take n ys == xs
                                  =  [ promoteCat[Rep x, promoteOpt(mkCat(drop n ys))] ]
                                     where
                                     Cat _ xs = x
                                     n = length(unCat x)
coShrunkenCat2Seg [Opt(Cat _ ys), Rep x ] 
                                  |  last ys == x
                                  =  [ promoteCat[promoteOpt(mkCat(init ys)), Rep x] ] 
                                  |  isCat x && drop m ys == xs
                                  =  [ promoteCat[promoteOpt(mkCat(take m ys)), Rep x] ]
                                     where
                                     Cat _ xs = x
                                     n = length(unCat x)
                                     m = length ys - n
coShrunkenCat2Seg [Alt _ xs, Rep y] 
                                  |  not (null candidates)
                                  =  [ promoteCat[promoteAlt ca, Rep y] | ca<-candidates ]
                                     where
                                     candidates = [mkCat(init zs):xs' | (Cat _ zs,xs')<-itemRest xs, y==last zs]
coShrunkenCat2Seg [Rep y, Alt _ xs] 
                                  |  not (null candidates)
                                  =  [ promoteCat[Rep y, promoteAlt ca] | ca<-candidates ]
                                     where
                                     candidates = [mkCat(tail zs):xs' | (Cat _ zs,xs')<-itemRest xs, y==head zs]
coShrunkenCat2Seg [Opt x,     y]  |  not $ null candidates
                                  =  take 1 candidates
                                     where
                                     candidates = [ promoteAlt[y,Opt x] | (xs,Rep y')<-rMostCom' x, eqv y y']
coShrunkenCat2Seg [y,     Opt x]  |  not $ null candidates
                                  =  take 1 candidates
                                     where
                                     candidates = [ promoteAlt[y,Opt x] | (Rep y',xs)<-lMostCom' x, eqv y y']
coShrunkenCat2Seg [Rep x,     y]  |  x == y
                                  =  [Rep x]
coShrunkenCat2Seg [x    , Rep y]  |  y == x
                                  =  [Rep y]
coShrunkenCat2Seg _               =  []

shrunkenAltList :: Int -> [FuseRE] -> [[FuseRE]]
shrunkenAltList d xs = [ xs'
                       | (x,etc) <- itemRest xs,
                         xs' <-  ([Lam | ewp x] ++ etc) : ([unRep x | isRep x] ++ etc) :
                                 [x' :etc | x' <- shrunken (d-1) x] ]

coShrunkenAltList :: Int -> [FuseRE] -> [[FuseRE]]
coShrunkenAltList d xs = [ xs'
                         | (x,etc) <- itemRest xs,
                           xs' <- [x':etc | x' <- coShrunken (d-1) x] ]

shrunken :: Int -> FuseRE -> [FuseRE]
shrunken 0 _           =  []
shrunken d (Alt _ xs)  =  [promoteAlt xs' | xs' <- shrunkenAltList d xs]
shrunken d (Cat _ xs)  =  [promoteCat xs' | xs' <- shrunkenCatList d xs]  
shrunken d (Opt x)     =  x : [promoteOpt x' | x'  <- shrunken (d-1) x ]
shrunken d (Rep x)     =  x : [promoteRep x' | x'  <- shrunken (d-1) x ]
shrunken d _           =  []

coShrunken :: Int -> FuseRE -> [FuseRE]
coShrunken 0 _           =  []
coShrunken d (Alt _ xs)  =  [promoteAlt xs' | xs' <- coShrunkenAltList d xs]
coShrunken d (Cat _ xs)  =  [promoteCat xs' | xs' <- coShrunkenCatList d xs]  
coShrunken d (Opt x)     =  [promoteOpt x'  | x'  <- coShrunken (d-1) x]
coShrunken d (Rep x)     =  [promoteRep x'  | x'  <- coShrunkenRepBody (d-1) x ]
coShrunken d _           =  []

coShrunkenRepBody 0 _           =  []
coShrunkenRepBody d (Alt _ xs)  =  [ valOf $ promoteCxt RepCxt (mkAlt xs')
                                   | (x,etc) <-itemRest xs,
                                     xs' <- [x':etc | x' <- coShrunkenRepBody (d-1) x] ]                          
coShrunkenRepBody d x@(Cat _ _) =  [ promoteAlt[b2',mkCat suf]
                                   | (b2,suf)<-lMostCom' x, b2'<-unOptRep b2] ++
                                   [ promoteAlt[mkCat pre,b3']
                                   | (pre,b3)<-rMostCom' x, b3'<-unOptRep b3] ++
                                   coShrunken d x
coShrunkenRepBody d _           =  []

unOptRep :: RE -> [RE]
unOptRep (Rep x) = [x]
unOptRep (Opt x) = [x]
unOptRep _       = []
                                                                                                
shrinkAltList :: RewRule
shrinkAltList c i xs =
      list2OK xs $  [ ys' | ys' <- shrunkenAltList shrinkDepth xs,
                            x `sublang` la (fuseAlt ys') ]
                 ++ [ ys' | ys' <- coShrunkenAltList coShrinkDepth xs,
                            fuseAlt ys' `sublang` lang ]
      where x    = Alt i xs
            la   = contextFunction c
            lang = la x

shrinkCatList :: RewRule
shrinkCatList c i xs =
      list2OK xs $  [ ys' | ys' <- shrunkenCatList shrinkDepth xs,
                            x `sublang` la(fuseCat ys') ]
                 ++ [ ys' | ys' <- coShrunkenCatList coShrinkDepth xs,
                            fuseCat ys' `sublang` lang ]
      where x    = Cat i xs
            la   = contextFunction c
            lang = la x

