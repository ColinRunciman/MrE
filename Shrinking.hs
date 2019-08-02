module Shrinking where

import List (itemRest, segPreSuf, splits, powerSplits)
import Expression
import Comparison
import Fuse
-- import Pressing
-- import Refactorization
import StarPromotion
import Context
import Info

-- EXPERIMENT:
-- (1) after fusion not after refactorization
-- (2) simple cat ends not *mostCom

refactOpt  =  promoteOpt
refactRep  =  promoteRep
refactCat  =  promoteCat
refactAlt  =  promoteAlt

refactCxt  =  promoteCxt

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
-- shrinkEX = mkExtension shrinkAltList shrinkCatList refactKP Shrunk
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
                                  [as++[unOpt x]++bs | isOpt x] ++ -- these two cases were part of shrinkRep/shrinkOpt
                                  [as++[unRep x]++bs | isRep x] ++ -- but had to be moved because of new regime
                                  [ as ++ [x'] ++ bs
                                  | x' <- shrunken (d-1) x] ] ++
                         [ xs'
                         | (pre,suf) <- splits xs,
                           (pre',x) <- rMostComList pre,
                           (y,suf') <- lMostComList suf,
                           xs' <- [ pre' ++ [xy'] ++ suf'
                                  | xy' <- shrunkenCat2Seg [x,y] ]]

shrunkenCat2Seg :: [FuseRE] -> [FuseRE]
shrunkenCat2Seg [Opt x, Opt y]  =  [refactOpt $ refactCat [x,y],
                                    refactOpt $ refactAlt [x,y]]
shrunkenCat2Seg [Rep x, Opt y]  =  [refactAlt $ [Rep x, y]]
shrunkenCat2Seg [Opt x, Rep y]  =  [refactAlt $ [x, Rep y]]
shrunkenCat2Seg _               =  []

-- TO DO:
-- coshrink X(YX)* to (Y?X)*
-- more generally: if A sublang X* and B sublang X*, coshrink AB to X*

-- Cxt might be used eventually
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

{- TO DO: catlists inside opts, special co-shrinking
coShrunkenOptCatList :: [FuseRE] -> [[FuseRE]]
coShrunkenOptCatList xs = [ xs'
                          | (as,bs) <- allSplits xs, all ewp as,
                            (cs,ds) <- allSplits bs, all ewp ds,
                            not (null as && null ds),
-}

-- TO DO: could generalise the XX* case for plural segment X
-- TO DO: use prefixCom instead of take/drop
-- SMK 18/9/2015 rules x(x*y)? -> x+x*y
coShrunkenCat2Seg :: [FuseRE] -> [FuseRE]
coShrunkenCat2Seg [Rep x, Rep y]  =  [refactRep $ refactAlt [x,y]]
coShrunkenCat2Seg [Rep x, Opt(Cat _ ys) ] 
                                  |  head ys == x
                                  =  [ refactCat[Rep x, refactOpt(mkCat(tail ys))] ] 
                                  |  isCat x && take n ys == xs
                                  =  [ refactCat[Rep x, refactOpt(mkCat(drop n ys))] ]
                                     where
                                     Cat _ xs = x
                                     n = length(unCat x)
coShrunkenCat2Seg [Opt(Cat _ ys), Rep x ] 
                                  |  last ys == x
                                  =  [ refactCat[refactOpt(mkCat(init ys)), Rep x] ] 
                                  |  isCat x && drop m ys == xs
                                  =  [ refactCat[refactOpt(mkCat(take m ys)), Rep x] ]
                                     where
                                     Cat _ xs = x
                                     n = length(unCat x)
                                     m = length ys - n
coShrunkenCat2Seg [Alt _ xs, Rep y] 
                                  |  not (null candidates)
                                  =  [ refactCat[refactAlt ca, Rep y] | ca<-candidates ]
                                     where
                                     candidates = [mkCat(init zs):xs' | (Cat _ zs,xs')<-itemRest xs, y==last zs]
coShrunkenCat2Seg [Rep y, Alt _ xs] 
                                  |  not (null candidates)
                                  =  [ refactCat[Rep y, refactAlt ca] | ca<-candidates ]
                                     where
                                     candidates = [mkCat(tail zs):xs' | (Cat _ zs,xs')<-itemRest xs, y==head zs]
coShrunkenCat2Seg [Opt x,     y]  |  not $ null candidates
                                  =  take 1 candidates
                                     where
                                     candidates = [ refactAlt[y,Opt x] | (xs,Rep y')<-rMostCom' x, eqv y y']
coShrunkenCat2Seg [y,     Opt x]  |  not $ null candidates
                                  =  take 1 candidates
                                     where
                                     candidates = [ refactAlt[y,Opt x] | (Rep y',xs)<-lMostCom' x, eqv y y']
coShrunkenCat2Seg [Rep x,     y]  |  x == y
                                  =  [Rep x]
coShrunkenCat2Seg [x    , Rep y]  |  y == x
                                  =  [Rep y]
coShrunkenCat2Seg _               =  []

shrunkenAltList :: Int -> [FuseRE] -> [[FuseRE]]
shrunkenAltList d xs = [ xs'
                       | (x,etc) <- itemRest xs,
                         xs' <- -- could be cheaper if sublang pressing?
                              ([Lam | ewp x] ++ etc) : ([unRep x | isRep x] ++ etc) : -- unRep case has been added because of new regime
                              [x' :etc | x' <- shrunken (d-1) x] ]

coShrunkenAltList :: Int -> [FuseRE] -> [[FuseRE]]
coShrunkenAltList d xs = [ xs'
                         | (x,etc) <- itemRest xs,
                           xs' <- [x':etc | x' <- coShrunken (d-1) x] ]

shrunken :: Int -> FuseRE -> [FuseRE]
shrunken 0 _           =  []
shrunken d (Alt _ xs)  =  [refactAlt xs' | xs' <- shrunkenAltList d xs]
shrunken d (Cat _ xs)  =  [refactCat xs' | xs' <- shrunkenCatList d xs]  
shrunken d (Opt x)     =  x : [refactOpt x' | x'  <- shrunken (d-1) x ]
shrunken d (Rep x)     =  x : [refactRep x' | x'  <- shrunken (d-1) x ]
shrunken d _           =  []

coShrunken :: Int -> FuseRE -> [FuseRE]
coShrunken 0 _           =  []
coShrunken d (Alt _ xs)  =  [refactAlt xs' | xs' <- coShrunkenAltList d xs]
coShrunken d (Cat _ xs)  =  [refactCat xs' | xs' <- coShrunkenCatList d xs]  
coShrunken d (Opt x)     =  {- coShrunkenOpt x ++ -}  -- extra power but at significant extra cost?
                            [refactOpt x'  | x'  <- coShrunken (d-1) x]
coShrunken d (Rep x)     =  [refactRep x'  | x'  <- coShrunkenRepBody (d-1) x ]
coShrunken d _           =  []

coShrunkenRepBody 0 _           = []
coShrunkenRepBody d (Alt _ xs)  = [ valOf $ refactCxt RepCxt (mkAlt xs')
                                | (x,etc) <-itemRest xs,
                                  xs' <- [x':etc | x' <- coShrunkenRepBody (d-1) x] ]                          
coShrunkenRepBody d x@(Cat _ _) =
                         [ refactAlt[b2',mkCat suf] | (b2,suf)<-lMostCom' x, b2'<-unOptRep b2] ++
                         [ refactAlt[mkCat pre,b3'] | (pre,b3)<-rMostCom' x, b3'<-unOptRep b3] ++
                         coShrunken d x
coShrunkenRepBody d _           =  [] -- cannot coshrink symbols

{- OUT OF USE FOR NOW

coShrunkenOpt d (Alt _ xs) = [ refactAlt xs' | xs' <- coShrunkenOptAltList xs]
coShrunkenOpt d (Cat _ xs) = [ refactCat xs' | xs' <- coShrunkenOptCatList xs]
coShrunkenOpt d x          = []

coShrunkenOptAltList xs =  [ (nz:zs')
                           | (ys,zs) <- powerSplits xs, (z,zs')<-itemRest zs,
                             nz <-  [ mkCat[Opt zt,Opt(mkCat tl)] | (Opt zt,tl)<-lMostCom' z, zt===fuseAlt ys]
                                 ++ [ mkCat[Opt(mkCat lt),Opt zt] | (lt,Opt zt)<- rMostCom' z, zt===fuseAlt ys]
                           ]

coShrunkenOptCatList xs =  [ xs1++[x2] | not(null xs1), x2<-coShrunken(Opt $ mkCat xs2)] ++
                           [ y1:ys2    | null xs1, not(null ys2), y1<-coShrunken(Opt $mkCat ys1)]
                           where
                           (xs1,xs2) = span ewp xs
                           (ys1,ys2) = span (not . ewp) xs
-}

unOptRep :: RE -> [RE]
unOptRep (Rep x) = [x]
unOptRep (Opt x) = [x]
unOptRep _       = []

                                                                                                 

{- Potential coshrinking rule for Rep bodies:
-- replace one cat by an alt, and coshrink, underneath a Rep
-- new rule SMK  7/9/2015
coShrunkenRepBody c@(Cat _ xs) = coShrunken c ++
                                 [ refactAlt as | (ys,zs)<- splits xs,
                                                let y=mkCat ys, let z=mkCat zs,
                                                as<-[[y,z'] | z'<-coShrunkenRepAlternative z] ++
                                                    [[y',z] | y'<-coShrunkenRepAlternative y]]
coShrunkenRepBody x = coShrunken x

coShrunkenRepAlternative x | ewp x = [ refactAlt (whiteAltList x) ]
coShrunkenRepAlternative x = coShrunken x
-}

{-

shrink  =  homTrans shrinkH

shrinkH =  HomTrans {falt=shrinkAlt, fcat=shrinkCat, frep=shrinkRep, fopt=shrinkOpt}

-- NAME no longer accurate : REFACTORIZATION
shrinkFactorized :: RE -> ShrunkRE
shrinkFactorized Emp = Emp
shrinkFactorized Lam = Lam
shrinkFactorized (Sym c) = Sym c
shrinkFactorized a@(Alt _ _) = shrinkFactorizedAlt a
shrinkFactorized c@(Cat _ _) = shrinkFactorizedCat c
shrinkFactorized r@(Rep _)   = shrinkFactorizedRep r
shrinkFactorized o@(Opt _)   = shrinkFactorizedOpt o

shrinkAlt :: [ShrunkRE] -> ShrunkRE
shrinkAlt xs = shrinkFactorized(refactAlt xs)
-}

shrinkAltList :: RewRule
shrinkAltList c i xs =
      list2OK xs $  [ ys' | ys' <- shrunkenAltList shrinkDepth xs, x `sublang` la (fuseAlt ys') ]
                 ++ [ ys' | ys' <- coShrunkenAltList coShrinkDepth xs, fuseAlt ys' `sublang` lang ]
                 -- ++ [ ys' | c>=OptCxt, ys' <- coShrunkenOptAltList xs, fuseAlt ys' `sublang` lang ]
                 -- extra power but at significant extra cost?
      where x    = Alt i xs
            la   = contextFunction c
            lang = la x

{-
shrinkFactorizedAlt y  
              |  not (null yss')
              =  shrinkAlt $ head yss'              
              |  otherwise 
              =  y           
  where
  Alt _ ys    =  y
  yss'        =  [ys' | ys' <- shrunkenAltList ys,
                        y `sublang` fuseAlt ys' ] ++
                 [ys' | ys' <- coShrunkenAltList ys,
                        fuseAlt ys' `sublang` y]
-}

{-                    
shrinkCat :: [ShrunkRE] -> ShrunkRE
shrinkCat xs = shrinkFactorized(refactCat xs)
-}

shrinkCatList :: RewRule
shrinkCatList c i xs =
      list2OK xs $  [ ys' | ys' <- shrunkenCatList shrinkDepth xs, x `sublang` la(fuseCat ys') ]
                 ++ [ ys' | ys' <- coShrunkenCatList coShrinkDepth xs, fuseCat ys' `sublang` lang ]
                 -- ++ [ ys' | c>=OptCxt, ys'<-coShrunkenOptCatList xs, fuseCat ys' `sublang` lang]
                 -- extra power but at significant extra cost?
      where x    = Cat i xs
            la   = contextFunction c
            lang = la x

{-
shrinkFactorizedCat y 
              |  not (null yss')
              =  shrinkCat $ head yss'              
              |  otherwise 
              =  y           
  where
  Cat _ ys    =  y
  yss'        =  [ys' | ys' <- shrunkenCatList ys,
                        y `sublang` fuseCat ys' ] ++
                 [ys' | ys' <- coShrunkenCatList ys,
                        fuseCat ys' `sublang` y ] 
-}

{-
shrinkRep :: ShrunkRE -> ShrunkRE
shrinkRep x = shrinkFactorized(reFuseREp x)

shrinkFactorizedRep y
              |  not (null ys')
              =  shrinkRep $ head ys'
              |  otherwise 
              =  y           
  where
  ys'         =  [y' | y' <- shrunken(unRep y), y `sublang` normRep y' ] ++
                 [y' | y' <- coShrunken(unRep y), normRep y' `sublang` y ] --or: coShrunkenRepBody SMK

shrinkOpt :: ShrunkRE -> ShrunkRE
shrinkOpt x = shrinkFactorized(refactOpt x)
-}
-- added cands: if x? shrinks to y, then (x+z)? shrinks to y+z (SMK 5/9/2015)
{-
shrinkFactorizedOpt y  
              |  not (null ys')
              =  shrinkOpt $ head ys'
              |  isAlt(unOpt y) && not(null cands)
              =  shrinkAlt $ head cands
              |  otherwise 
              =  y           
  where
  ys'         =  [y' | y' <- shrunken(unOpt y), y `sublang` normOpt y' ] ++
                 [y' | y' <- coShrunken(unOpt y), normOpt y' `sublang` y ]
  cands       =  [ z':zs | (z,zs)<-itemRest (unAlt(unOpt y)),
                               let z'=shrinkOpt z, not (isOpt z') ]
-}


