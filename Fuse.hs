module Fuse (
  FuseRE, fuse, fuseH, fuseP, fuseKP, fuseAlt, fuseCat, fuseOpt, fuseRep,
  isFused, whiteAltList, fuseListProcess ) where

import List
import Expression
import OK
import Context
import Info
import Function ((===>))
import Alphabet
import Data.List

-- Transformations in this module include the Gruber-Gulan rules and additional
-- rules of no worse than log-linear complexity.  For example:
-- (1) factorisation of common prefixes or suffixes in Alts, and some more
--     specialised transformations for Alts that are Rep bodies
--     (see altFuseList)
-- (2) combination of neighbouring Opt x and Rep x in Cats, also commuting these
--     with any intervening x occurrences to enable such fusion, and again
--     some more specialised transformations for Cats that are Rep bodies
--     (see catFuseList)

-- KATA STUFF TO BE INCORPORATED APPROPRIATELY

{-
kataGradeH :: HomTrans
kataGradeH = mkHomTrans kataGradeKatahom
HomTrans { falt = kataAlt, fcat = kataCat, frep = kataRep, fopt = kataOpt } = kataGradeH

kataGrade :: RE -> RE
--kataGrade = valOf . katahom kataGradeKatahom NoCxt
kataGrade = mkTransform kataGradeKatahom

kataGradeKP = KataPred { khom = kataGradeKatahom, kpred = kataP, thisfun = kataGrade }
-}

isKata :: RE -> Bool
isKata = checkWith kataP

-- predicate for bottom-line system, grade Kata
-- besides checking structural constraints also the info is tested for correctness, except for grading
kataP :: RecPred
kataP = RecPred { empP = empKataP, lamP = lamKataP, symP = symKataP,
                  altP = altKataP, catP = catKataP, repP = repKataP, optP = optKataP }

-- 0 and 1 are only allowed at the root
empKataP, lamKataP :: Cxt -> Bool
empKataP c = c==RootCxt
lamKataP c = c==RootCxt

-- Symbols are allowed everywhere
symKataP :: Cxt -> Char -> Bool
symKataP _ _ = True

altElem :: Cxt -> RE -> Bool
altElem _ (Sym _)   = True
altElem _ (Cat _ _) = True
altElem c (Rep _)   = c/=RepCxt
altElem _ _         = False

altKataP c i xs = plural xs && all (altElem c) xs && strictlyOrdered xs &&
                  ew i == any ewp xs && si i == listSize xs &&
                  la i == lasAlt xs&& fi i == firAlt xs 

catElem :: RE -> Bool
catElem (Sym _)   = True
catElem (Alt _ _) = True
catElem (Rep _)   = True
catElem (Opt _)   = True
catElem _         = False

catKataP c i xs =  plural xs && all catElem xs &&
                   ew i == all ewp xs && si i == listSize xs &&
                   la i == lasCat xs && fi i == firCat xs 
                   
repKataP :: Cxt -> RE -> Bool
repKataP RepCxt _     =  False
repKataP _ (Sym _)    =  True
repKataP _ (Cat _ _)  =  True
repKataP c (Alt _ xs) =  all (repKataP c) xs
repKataP _ _          =  False

optKataP :: Cxt -> RE -> Bool
optKataP RepCxt _    =  False
optKataP _ (Sym _)   =  True
optKataP _ (Alt i _) =  not (ew i)
optKataP _ (Cat i _) =  not (ew i)
optKataP _  _        =  False

-- END OF KATA STUFF

type FuseRE = RE

fuseK :: Katahom
fuseK  =  Katahom { kalt = altFuseList, kcat = catFuseList, grade = Fused }

fuseKP :: KataPred
fuseKP  =  KataPred { khom = fuseK, kpred = fuseP, thisfun = fuse }

fuse :: RE -> FuseRE
fuse = mkTransform fuseK

fuseCxt :: Cxt -> RE -> OK FuseRE
fuseCxt = katahom fuseK

HomTrans { falt=fuseAlt,  fcat=fuseCat, frep=fuseRep, fopt=fuseOpt} = fuseH
fuseH = mkHomTrans fuseK

fuseP :: RecPred
fuseP = mkPredExtension altFuseList catFuseList kataP

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

altFuseList :: Cxt -> Info -> [FuseRE] -> OK [RE]
altFuseList c i xs = guardApply (ew i && c==RepCxt) whiteList xs `orOK`
                     altSigmaStar c i xs `orOK`
                     leftfuse xs `orOK` rightfuse xs

-- assumption: in RepCxt this is not ewp,
-- because altFuseList would get to break it up first
altSigmaStar :: Cxt -> Info -> [RE] -> OK [RE]
altSigmaStar c i xs |  c/=RepCxt || isEmptyAlpha (sw i)
                    =  unchanged xs
                    |  al i == sw i
                    =  updateEQ xs (map Sym (alpha2String $ sw i))
                    |  otherwise
                    =  kataliftAlt (alphaCrush (sw i)) xs

-- if re is sublang of cs* replace it with cs', where cs' is its alphabet
-- the re is a subexp of an alt, so if re=sigma' already then re is a symbol
alphaCrush :: Alphabet -> RE -> OK RE
alphaCrush cs (Sym c) =  unchanged (Sym c)
alphaCrush cs re      |  subAlpha alset cs
                      =  changed (mkAlt (map Sym allst))
                      |  otherwise
                      =  fixCrushRE cs re -- removes prefixes/suffixes
                         where
                         alset = alpha re
                         allst = alpha2String (swa re) 

fixCrushRE :: Alphabet -> RE -> OK RE
fixCrushRE cs re@(Cat i xs) = list2OK re [ catSegment re (valOf yso)
                                         | let yso=fixCrush cs xs, hasChanged yso ]
fixCrushRE cs re            = unchanged re

fixCrush :: Alphabet -> [RE] -> OK [RE]
fixCrush cs = suffixCrush cs `aft` prefixCrush cs

prefixCrush, suffixCrush :: Alphabet -> [RE] -> OK [RE]
prefixCrush cs (x:xs) |  ewp x && subAlpha (alpha x) cs
                      =  unsafeChanged $ prefixCrush cs xs
                      |  otherwise
                      =  unchanged (x:xs)
prefixCrush cs []     =  unchanged [] -- should not occur

suffixCrush cs xs     |  hasChanged rxs
                      =  okmap reverse rxs
                      |  otherwise 
                      =  unchanged xs 
                         where rxs = prefixCrush cs (reverse xs)

-- (1) remove optional suffixes/prefixes with alphabet <= sw of whole Cat.
-- (2) replace bodies that have sw as alphabet with sw

catFuseList :: Cxt -> Info -> [FuseRE] -> OK [KataRE]
catFuseList RepCxt i xs  |  ew i
                         =  changed [ alt (whiteList xs) ]
                         |  sw i==al i
                         =  changed [ alt (map Sym (alpha2String $ sw i)) ]
                         |  not (isEmptyAlpha (sw i)) 
                         =  fuseListProcess `app` fixCrush (sw i) xs
catFuseList _ i xs       =  fuseListProcess xs

fuseListProcess :: [RE] -> OK [RE]
fuseListProcess xs = updateEQ xs $ concat $ fuseChains fuseCatElem xs

fuseCatElem :: Fusion RE
fuseCatElem (Rep x)(Rep y) |  x == y
                           =  Left (Rep x)
                           |  a == alpha y && singularAlpha a
                           =  Left (fuse(rep(alt[x,y])))
                           |  otherwise
                           =  Right True -- no swap
                              where
                              a = alpha x
fuseCatElem (Rep x)(Opt y) =  if x==y then Left(Rep x) else Right True
fuseCatElem (Opt x)(Rep y) =  if x==y then Left(Rep x) else Right True
fuseCatElem x y            =  Right True

-- The first argument occurs as an item in either a Cats or an Alts in a RepCxt.
-- The second argument accumulates a list of already whited items.

whiteListS :: KataRE -> [KataRE] -> [KataRE]
whiteListS Emp xs         =  error "whiteListS Emp"  -- was xs
whiteListS Lam xs         =  error "whiteListS Lam"  -- was xs
whiteListS (Alt i xs) ys  |  ew i
                          =  whiteListL xs ys
                          |  otherwise
                          =  xs++ys
whiteListS (Cat i xs) ys  |  ew i
                          =  whiteListL xs ys
whiteListS (Rep re) ys    =  re:ys
whiteListS (Opt re) ys    =  re:ys
whiteListS x        ys    =  x:ys

whiteListL :: [KataRE] -> [KataRE] -> [KataRE]
whiteListL [] xs      =  xs
whiteListL (x:xs) ys  =  whiteListS x $ whiteListL xs ys

whiteList :: [KataRE] -> [KataRE]
whiteList xs = whiteListL xs []

-- The following laws are included here:
-- X** --> X*
-- (...+X*+...)* --> (...+X+...)*
-- (X1*X2*...Xn*)* --> (X1+X2+...+Xn)*

-- The whiteAltList function is similar to the Gruber-Gulan white function,
-- but instead of a single RE it returns a list of subREs of its argument.

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

