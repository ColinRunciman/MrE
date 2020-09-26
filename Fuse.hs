-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module Fuse (
  fuse, fuseH, fuseP, fuseKP, fuseAlt, fuseCat, fuseOpt, fuseRep,
  isFused, fuseListProcess, isNorm, whiteAltList ) where

import List
import Expression
import OK
import Context
import Info
import Function ((===>))
import Alphabet
import Data.List

-- Transformations in this module include rules of no worse than log-linear complexity.
-- For example:
-- (1) factorisation of common prefixes or suffixes in Alts, and some more
--     specialised transformations for Alts that are Rep bodies
--     (see altFuseList)
-- (2) combination of neighbouring Opt x and Rep x in Cats, also commuting these
--     with any intervening x occurrences to enable such fusion, and again
--     some more specialised transformations for Cats that are Rep bodies
--     (see catFuseList)

-- predicate for RE-invariant, see Expression module, grade Normal
-- besides checking structural constraints also the info is tested for correctness,
-- except for grading

isNorm :: RE -> Bool
isNorm = checkWith normP

normP :: RecPred
normP = RecPred { empP = empnormP, lamP = lamnormP, symP = symnormP,
                  altP = altnormP, catP = catnormP, repP = repnormP, optP = optnormP }

-- 0 and 1 are only allowed at the root
empnormP, lamnormP :: Cxt -> Bool
empnormP c = c==RootCxt
lamnormP c = c==RootCxt

-- Symbols are allowed everywhere
symnormP :: Cxt -> Char -> Bool
symnormP _ _ = True

altElem :: Cxt -> RE -> Bool
altElem _ (Sym _)   = True
altElem _ (Cat _ _) = True
altElem c (Rep _)   = c/=RepCxt
altElem _ _         = False

altnormP c i xs = plural xs && all (altElem c) xs && strictlyOrdered xs &&
                  ew i == any ewp xs && si i == listSize xs &&
                  la i == lasAlt xs&& fi i == firAlt xs

catElem :: RE -> Bool
catElem (Sym _)   = True
catElem (Alt _ _) = True
catElem (Rep _)   = True
catElem (Opt _)   = True
catElem _         = False

catnormP c i xs =  plural xs && all catElem xs &&
                   ew i == all ewp xs && si i == listSize xs &&
                   la i == lasCat xs && fi i == firCat xs

repnormP :: Cxt -> RE -> Bool
repnormP RepCxt _     =  False
repnormP _ (Sym _)    =  True
repnormP _ (Cat _ _)  =  True
repnormP c (Alt _ xs) =  all (repnormP c) xs
repnormP _ _          =  False

optnormP :: Cxt -> RE -> Bool
optnormP RepCxt _    =  False
optnormP _ (Sym _)   =  True
optnormP _ (Alt i _) =  not (ew i)
optnormP _ (Cat i _) =  not (ew i)
optnormP _  _        =  False


fuseK :: Katahom
fuseK  =  Katahom { kalt = altFuseList, kcat = catFuseList, grade = Fused }

fuseKP :: KataPred
fuseKP  =  KataPred { khom = fuseK, kpred = fuseP, thisfun = fuse }

fuse :: RE -> RE
fuse = mkTransform fuseK

fuseCxt :: Cxt -> RE -> OK RE
fuseCxt = katahom fuseK

HomTrans { falt=fuseAlt,  fcat=fuseCat, frep=fuseRep, fopt=fuseOpt} = fuseH
fuseH = mkHomTrans fuseK

fuseP :: RecPred
fuseP = mkPredExtension altFuseList catFuseList normP

isFused :: RE -> Bool
isFused = checkWith fuseP

-- end of boilerplate

type Fusion a = a -> a -> Either a Bool

-- assumption: both input lists, are ordered/fused
-- the fusion operation, when successful is monotonic
mergeFuse :: Fusion a -> [a] -> [a] -> [a]
mergeFuse fuseop [] xs = xs
mergeFuse fuseop xs [] = xs
mergeFuse fuseop (x:xs) (y:ys) =
   case fuseop x y of
       Left xy     -> xy : mergeFuse fuseop xs ys
       Right True  -> x: mergeFuse fuseop xs (y:ys)
       Right False -> y : mergeFuse fuseop (x:xs) ys

leftOrderedFusion :: Fusion RE
leftOrderedFusion e1 e2 =
   case commonList (theList e1)(theList e2) of
       Right x -> Right x
       Left (comm,e1s,e2s) -> Left (rebuild (from e1 comm)(from e1 e1s)(from e2 e2s))
   where
   from e []  = Lam
   from e [x] = x
   from e xs  = catSegment e xs
   rebuild co a1 a2 = fuseCat [co,mkAlt [a1,a2]]

theList :: RE -> [RE]
theList (Cat _ xs) = xs
theList x          = [x]

revList :: RE -> [RE]
revList (Cat _ xs) = reverse xs
revList x          = [x]

rightOrderedFusion :: Fusion RE
rightOrderedFusion e1 e2 =
   case commonList (revList e1)(revList e2) of
       Right x -> Right x
       Left (comm,e1s,e2s) -> Left (rebuild (from e1 e1s)(from e2 e2s)(from e2 comm))
   where
   from e []  = Lam
   from e [x] = x
   from e xs  = catSegment e (reverse xs)
   rebuild a1 a2 co = fuseCat [mkAlt [a1,a2],co]

commonList :: Ord a => [a] -> [a] -> Either ([a],[a],[a]) Bool
commonList xs ys | n==0
                 = Right bb
                 | otherwise
                 = Left(take n xs,drop n xs,drop n ys)
    where
    (n,bb) = firstDiff 0 xs ys

firstDiff :: Ord a => Int -> [a] -> [a] -> (Int,Bool)
firstDiff k [] xs = (k,True)
firstDiff k xs [] = (k,True)
firstDiff k (x:xs) (y:ys) =
    case compare x y of
        EQ -> firstDiff(k+1) xs ys
        bb -> (k,bb==LT)

fuseSort :: Fusion a -> [a] -> [a]
fuseSort fuseop xs = foldMerge (mergeFuse fuseop) [] $ fuseChains fuseop xs

-- trying to be cleverer than map(:[])xs
fuseChains :: Fusion a -> [a] -> [[a]]
fuseChains fuseop = foldr addOne []
    where
    addOne x [] = [[x]]
    addOne x ([]:yss) = error "empty arg in fuse partition"
    addOne x ((y:ys):yss) =
         case fuseop x y of
             Left z      -> (z:ys):yss
             Right True  -> (x:y:ys):yss
             Right False -> [x]:((y:ys):yss)

leftfuse :: [RE] -> OK [RE]
leftfuse xs = mkOK lf (length xs > length lf)
              where
              lf = fuseSort leftOrderedFusion xs

rightfuse :: [RE] -> OK [RE]
rightfuse xs = mkOK rf (length xs > length rf)
              where
              rf = fuseSort rightOrderedFusion xs

altFuseList :: Cxt -> Info -> [RE] -> OK [RE]
altFuseList c i xs = leftfuse xs `orOK` rightfuse xs

-- (1) remove optional suffixes/prefixes with alphabet <= sw of whole Cat.
-- (2) replace bodies that have sw as alphabet with sw

catFuseList :: Cxt -> Info -> [RE] -> OK [RE]
catFuseList RepCxt i xs  |  ew i
                         =  changed [ alt (concatMap whiteAltList xs) ]
catFuseList _ i xs       =  fuseListProcess xs

fuseListProcess :: [RE] -> OK [RE]
fuseListProcess xs = updateEQ xs $ concat $ fuseChains fuseCatElem xs

fuseCatElem :: Fusion RE
fuseCatElem (Rep x)(Rep y) =  if x==y then Left(Rep x) else Right True
fuseCatElem (Rep x)(Opt y) =  if x==y then Left(Rep x) else Right True
fuseCatElem (Opt x)(Rep y) =  if x==y then Left(Rep x) else Right True
fuseCatElem x y            =  Right True

-- The whiteAltList function is similar to the Gruber-Gulan white function,
-- but instead of a single RE it returns a list of subREs of its argument.
-- The following laws are included here:
-- X** --> X*
-- (...+X*+...)* --> (...+X+...)*
-- (X1*X2*...Xn*)* --> (X1+X2+...+Xn)*

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
