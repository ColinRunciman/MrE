module Normalization (NormRE, whiteAltList, normalize, normRep, white, normP, isNormal,
                    normAlt, normBinAlt, normCat, normBinCat, normOpt, norm, normH, normK, normKP) where

import Expression
import List
import Context
import Info
import Function ((===>))

-- First-stage normalization gives a strengthened form of the
-- Gruber-Gulan SSNF (strong star normal form) which all
-- subsequent stages preserve.  In a normalized RE:
-- Emp can only occur as the entire expression;
-- Lam can only occur as the entire expression;
-- Alt lists are strictly ordered with no syntactic duplicates;
-- Cat lists do not contain a star next to a like-bodied star or option; 
-- Opt bodies are not ewp.
-- Rep bodies are not ewp.

-- NB. Just a type synonym. No checking power, just documenting
-- intentions and expectations.
type NormRE  =  RE

{-
-- predicates for normal expressions
normP :: RecPred
normP = standardP { altP=ap, catP=cp, repP=rp, optP=op }
        where
        ap pa b xs  =  altP standardP pa b xs &&
                       not (any (\x -> isEmp x || isLam x || isOpt x) xs) && 
                       not (or $ linkWith (==) xs)
        cp pa b xs  =  catP standardP pa b xs &&
                       not (any (\x -> isEmp x || isLam x) xs) && 
                       not (or $ linkWith normFusable xs)
        rp x        =  not (ewp x) && normRepBody x
        op x        =  not (ewp x) && not (isEmp x)

normRepBody Emp           =  False
normRepBody x@(Alt _ xs)  =  all isSym xs || (any (\c-> not (swp c x)) (alpha x) && all normRepBody xs)
normRepBody x@(Cat _ xs)  =  any (\c -> not (swp c x)) (alpha x)
normRepBody _             =  True



normFusable :: RE -> RE -> Bool
normFusable (Rep x) (Rep y)  =  x==y
normFusable (Rep x) (Opt y)  =  x==y
normFusable (Opt x) (Rep y)  =  x==y
normFusable _       _        =  False
-}

-- choice between two SSNFs in RootCxt, uncertified
normBinAlt :: NormRE -> NormRE -> NormRE
normBinAlt Emp         x              =  x
normBinAlt x           Emp            =  x
normBinAlt Lam         x              =  normOpt x
normBinAlt x           Lam            =  normOpt x
normBinAlt (Opt x)     y              =  normOpt $ normBinAlt x y
normBinAlt x           (Opt y)        =  normOpt $ normBinAlt x y
normBinAlt (Alt ix xs) (Alt iy ys)    =  mkAlt $ nubMerge xs ys
normBinAlt (Alt ix xs) y              =  mkAlt $ nubMerge xs [y]
normBinAlt x           (Alt iy ys)    =  mkAlt $ nubMerge [x] ys
normBinAlt x           y              =  case compare x y of
                                         LT -> mkAlt [x,y]
                                         EQ -> x
                                         GT -> mkAlt [y,x]

-- sequence between two SSNFs in RootCxt, uncertified
normBinCat :: NormRE -> NormRE -> NormRE
normBinCat Emp x = Emp
normBinCat x Emp = Emp
normBinCat Lam x = x
normBinCat x Lam = x
normBinCat x@(Cat i1 xs) y@(Cat i2 ys) = mkCatI (infoCat x y) (normAppend xs ys)
normBinCat x@(Cat i1 xs) y             = mkCatI (infoCat x y) (normAppend xs [y])
normBinCat x y@(Cat i2 ys)             = mkCatI (infoCat x y) (normAppend [x] ys)
normBinCat a b                         = mkCatI (infoCat a b) (normAppend [a] [b])

normAppend :: [NormRE] -> [NormRE] -> [NormRE]
normAppend xs []  =  xs -- optimization, otherwise we end up reversing xs twice
normAppend [] ys  =  ys
normAppend xs ys  =  na (reverse xs) ys
  where
  na (Rep x:xs) (Rep y:ys)  |  x == y
                            =  na xs (Rep y:ys)
  na (Rep x:xs) (Opt y:ys)  |  x == y
                            =  na (Rep x:xs) ys
  na (Opt x:xs) (Rep y:ys)  |  x == y
                            =  na xs (Rep y:ys)
  na xs         ys          =  reverse xs ++ ys


-- The following laws are included here:
-- X** --> X*
-- (...+X*+...)* --> (...+X+...)*
-- (X1*X2*...Xn*)* --> (X1+X2+...+Xn)*

-- normRep :: NormRE -> NormRE
{-
normRep Emp = Lam
normRep Lam = Lam
normRep (Rep x) = Rep x
normRep (Opt x) = Rep x
normRep x = Rep $ white x
-}

-- this is the 'white' operator of Gruber-Gulan SSNF
white :: NormRE -> NormRE
white Emp         =  Emp
white Lam         =  Emp
white (Sym s)     =  Sym s
white (Alt i xs)  |  ew i
                  =  normAlt $ map white xs
                  |  otherwise
                  =  Alt i xs
white (Cat i xs)  |  ew i
                  =  normAlt $ map white xs
                  |  otherwise
                  =  Cat i xs
white (Rep x)     =  x
white (Opt x)     =  x

-- like white, but anticipates normAlt/pressAlt/factAlt... as next step
-- whiteAltList only returns a list of subREs of its argument
whiteAltList :: RE -> [RE]
whiteAltList Emp            =  []
whiteAltList Lam            =  []
whiteAltList (Alt i xs)     |  ew i
                            =  concatMap whiteAltList xs
                            |  otherwise
                            =  xs
whiteAltList (Cat i xs)     |  ew i
                            =  concatMap whiteAltList xs
whiteAltList (Rep re)       =  [re]
whiteAltList (Opt re)       =  [re]
whiteAltList x              =  [x]


altNormList :: Cxt -> Info -> [NormRE] -> OK [KataRE]
altNormList RepCxt i xs  =  guardApply (ew i) whiteList xs
altNormList _ _ xs       =  unchanged xs

catNormList :: Cxt -> Info -> [NormRE] -> OK [KataRE]
catNormList RepCxt i xs  |  ew i
                         =  changed [ kataAlt (whiteList xs) ]
catNormList _ i xs       =  updateEQ xs $ normListProcess [] xs

-- left argument: list of already processed elements, in reverse order
-- right argument: unprocessed, but all cat-elements
normListProcess :: [NormRE] -> [NormRE] -> [NormRE]
normListProcess xs []     =  reverse xs
normListProcess [] (x:xs) =  normListProcess [x] xs
normListProcess (Rep x:xs) (Rep y:ys)
                          |  x == y
                          =  normListProcess (Rep x:xs) ys
normListProcess (Rep x:xs) (Opt y:ys)
                          |  x == y
                          =  normListProcess (Rep x:xs) ys
normListProcess (Opt x:xs) (Rep y:ys)
                          |  x == y
                          =  normListProcess xs (Rep y:ys)
normListProcess xs (y:ys) =  normListProcess (y:xs) ys


-- input: KataRE that occurs as list element in either Cats or Alts in a RepCxt in trafos
-- snd arg is a list of already whited ones
whiteListS :: KataRE -> [KataRE] -> [KataRE]
whiteListS Emp xs         =  xs -- or: error; this should not occur here
whiteListS Lam xs         =  xs -- or: error
whiteListS (Alt i xs) ys  |  ew i
                          =  whiteListL xs ys
                          |  otherwise
                          =  xs++ys
whiteListS (Cat i xs) ys  |  ew i
                          =  whiteListL xs ys
whiteListS (Rep re) ys    =  re:ys -- or: error; this should not occur here either
whiteListS (Opt re) ys    =  re:ys -- or: error
whiteListS x        ys    =  x:ys

whiteListL :: [KataRE] -> [KataRE] -> [KataRE]
whiteListL [] xs = xs
whiteListL (x:xs) ys = whiteListS x $ whiteListL xs ys

whiteList :: [KataRE] -> [KataRE]
whiteList xs = whiteListL xs []

-- giving names to the boilerplated entities:

normEX :: Extension
normEX = mkExtension altNormList catNormList kataGradeKP Normal

normK :: Katahom
normK = trg normEX
-- normK = Katahom { kalt=normAltK, kcat=normCatK, grade=Normal}

norm :: Cxt -> RE -> OK RE
norm  = katahom normK

normalize :: RE -> NormRE
normalize = fst . katahom normK NoCxt
--normalize  =  homTrans $ normH

-- normH = HomTrans { falt=normAlt,  fcat=normCat, frep= normRep, fopt=normOpt}
HomTrans { falt=normAlt,  fcat=normCat, frep= normRep, fopt=normOpt} = normH
normH = mkHomTrans normK

normP :: RecPred
normP = tpr normEX

isNormal :: RE -> Bool
isNormal = checkWith normP


normKP = target normEX



          






