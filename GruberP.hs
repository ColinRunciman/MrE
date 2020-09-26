-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module GruberP (ggTrans, gSize, linearTrans) where

import Expression
import Parser
import Info

--using simple parser with ewp for GruberGulan style

ggTrans (Alt i [x,y]) = ggBinAlt (ggTrans x) (ggTrans y)
ggTrans (Cat i [x,y]) = synCat   (ggTrans x) (ggTrans y)
ggTrans (Opt r)    = gOpt $ ggTrans r
ggTrans (Rep r)    = gRep $ ggRepTrans r
ggTrans x          = x

ggRepTrans Lam             = Emp
ggRepTrans a@(Alt i [x,y]) = synAlt (ggRepTrans x)(ggRepTrans y)
ggRepTrans c@(Cat i [x,y]) | ew i
                           = synAlt (ggRepTrans x)(ggRepTrans y)
                           | otherwise
                           = synCat (ggTrans x)(ggTrans y)
ggRepTrans (Rep x)         = ggRepTrans x
ggRepTrans (Opt x)         = ggRepTrans x
ggRepTrans x               = x

gOpt x | ewp x      = x
       | otherwise  = Opt x

gRep Emp = Lam
gRep x   = Rep x

ggBinAlt :: RE -> RE -> RE
ggBinAlt (Opt x) y = gOpt $ ggBinAlt x y
ggBinAlt x (Opt y) = gOpt $ ggBinAlt x y
ggBinAlt x y       = synAlt x y

linearTrans :: String -> RE
linearTrans s = ggTrans (readFullExp s)

-- since size is not memoized for this trafo, the normal size function does not work
gSize :: RE -> Int
gSize = gSizeAcc 0

gSizeAcc :: Int -> RE -> Int
gSizeAcc n Emp = n
gSizeAcc n Lam = n
gSizeAcc n (Sym _) = n+1
gSizeAcc n (Alt _ xs) = lSize n xs
gSizeAcc n (Cat _ xs) = lSize n xs
gSizeAcc n (Rep x)    = gSizeAcc (n+1) x
gSizeAcc n (Opt x)    = gSizeAcc (n+1) x

lSize :: Int -> [RE] -> Int
lSize n [] = n-1
lSize n (x:xs) = lSize (gSizeAcc (n+1) x) xs

