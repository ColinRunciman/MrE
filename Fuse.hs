module Fuse (
  FuseRE, fuse, fuseH, fuseP, fuseKP, fuseAlt, fuseCat, fuseOpt, fuseRep, fuseBinCat,
  isFused, whiteAltList, normBinAlt, contextFunction ) where

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

type FuseRE = RE

fuseEX :: Extension
fuseEX = mkExtension altFuseList catFuseList kataGradeKP Fused

fuseK :: Katahom
fuseK = trg fuseEX

fuseKP :: KataPred
fuseKP = target fuseEX

fuse :: RE -> FuseRE
fuse = mkTransform fuseK

fuseCxt :: Cxt -> RE -> OK FuseRE
fuseCxt = katahom fuseK

HomTrans { falt=fuseAlt,  fcat=fuseCat, frep= fuseRep, fopt=fuseOpt} = fuseH
fuseH = mkHomTrans fuseK

fuseP :: RecPred
fuseP = tpr fuseEX

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
       Left (comm,e1s,e2s) -> Left (rebuild (from2 e1 e2 comm)(from e1 e1s)(from e2 e2s))
   where
   from e []  = Lam
   from e [x] = x
   from e xs  = catSegment e xs
   from2 e1 e2 [x]  = x
   from2 e1 e2 xs   = catSegment2 e1 e2 xs
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
       Left (comm,e1s,e2s) -> Left (rebuild (from e1 e1s)(from e2 e2s)(from2 e1 e2 comm))
   where
   from e []  = Lam
   from e [x] = x
   from e xs  = catSegment e (reverse xs)
   from2 e1 e2 [x]  = x
   from2 e1 e2 xs   = catSegment2 e1 e2 (reverse xs)
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
                     leftfuse xs `orOK` rightfuse xs `orOK`
                     singleLetterFuseLeft xs `orOK` singleLetterFuseRight xs


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

-- also RepCxt can be promoted to suffixes (prefixes) if the complementary prefix (suffix)
-- is nullable.  So if sw is non-trivial then:
-- (i) remove optional suffixes/prefixes having sw as alphabet from sequence
-- (ii) replace bodies that have sw as alphabet with sw
catFuseList :: Cxt -> Info -> [FuseRE] -> OK [KataRE]
catFuseList RepCxt i xs  |  ew i
                         =  changed [ kataAlt (whiteList xs) ]
                         |  sw i==al i
                         =  changed [ kataAlt (map Sym (alpha2String $ sw i)) ]
                         |  not (isEmptyAlpha (sw i)) 
                         =  fixCrush (sw i) xs
                         |  otherwise
                         =  unchanged xs
                            where
catFuseList _ i xs       =  fuseListProcess False [] xs

-- left argument: list of already processed elements, in reverse order
-- right argument: unprocessed, but all cat-elements
fuseListProcess :: Bool -> [FuseRE] -> [FuseRE] -> OK [FuseRE]
fuseListProcess changed xs []     =  mkOK (reverse xs) changed
fuseListProcess changed [] (x:xs) =  fuseListProcess changed [x] xs
fuseListProcess changed (Rep x:xs) (Rep y:ys)
                          |  x == y
                          =  fuseListProcess True (Rep x:xs) ys
                          |  a == alpha y && singularAlpha a
                          =  fuseListProcess True xs (fuse(Rep(alt[x,y])):ys)
                             where
                             a = alpha x
fuseListProcess changed (Rep x:xs) (Opt y:ys)
                          |  x == y
                          =  fuseListProcess True (Rep x:xs) ys
fuseListProcess changed (Opt x:xs) (Rep y:ys)
                          |  x == y
                          =  fuseListProcess True xs (Rep y:ys)
fuseListProcess changed (Opt x:xs) (y:ys)
                          |  x == y
                          =  fuseListProcess True xs (y:Opt x:ys)
fuseListProcess changed xs (y:ys) =  fuseListProcess changed (y:xs) ys

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

-------------------------- Normalisation --------------------------

-- choice between two SSNFs in RootCxt, uncertified
normBinAlt :: FuseRE -> FuseRE -> FuseRE
normBinAlt Emp         x              =  x
normBinAlt x           Emp            =  x
normBinAlt Lam         x              =  fuseOpt x
normBinAlt x           Lam            =  fuseOpt x
normBinAlt (Opt x)     y              =  fuseOpt $ normBinAlt x y
normBinAlt x           (Opt y)        =  fuseOpt $ normBinAlt x y
normBinAlt (Alt ix xs) (Alt iy ys)    =  mkAlt $ nubMerge xs ys
normBinAlt (Alt ix xs) y              =  mkAlt $ nubMerge xs [y]
normBinAlt x           (Alt iy ys)    =  mkAlt $ nubMerge [x] ys
normBinAlt x           y              =  case compare x y of
                                         LT -> mkAlt [x,y]
                                         EQ -> x
                                         GT -> mkAlt [y,x]

-- sequence between two SSNFs in RootCxt, uncertified
fuseBinCat :: FuseRE -> FuseRE -> FuseRE
fuseBinCat Emp x = Emp
fuseBinCat x Emp = Emp
fuseBinCat Lam x = x
fuseBinCat x Lam = x
fuseBinCat x@(Cat i1 xs) y@(Cat i2 ys) = mkCatI (infoCat x y) (normAppend xs ys)
fuseBinCat x@(Cat i1 xs) y             = mkCatI (infoCat x y) (normAppend xs [y])
fuseBinCat x y@(Cat i2 ys)             = mkCatI (infoCat x y) (normAppend [x] ys)
fuseBinCat a b                         = mkCatI (infoCat a b) (normAppend [a] [b])

normAppend :: [FuseRE] -> [FuseRE] -> [FuseRE]
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

-- this is the 'white' operator of Gruber-Gulan SSNF
white :: FuseRE -> FuseRE
white Emp         =  Emp
white Lam         =  Emp
white (Sym s)     =  Sym s
white (Alt i xs)  |  ew i
                  =  fuseAlt $ map white xs
                  |  otherwise
                  =  Alt i xs
white (Cat i xs)  |  ew i
                  =  fuseAlt $ map white xs
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

contextFunction :: Cxt -> RE -> RE
contextFunction RepCxt  =  fuseRep
contextFunction OptCxt  =  fuseOpt
contextFunction _       =  id

-- the REs are alt-elements, we can ignore the Sym case, as these are factored via sorting
-- and leftfusion; for rightLetterFusion this is not True though
singleLetterFuseLeft :: [RE] -> OK [RE]
singleLetterFuseLeft [x] = unchanged [x]
singleLetterFuseLeft (x:xs) = app (addSingleFuse x) (singleLetterFuseLeft xs)

-- dual
singleLetterFuseRight :: [RE] -> OK [RE]
singleLetterFuseRight [x] = unchanged [x]
singleLetterFuseRight xs = app (addSingleFuseR (last xs)) (singleLetterFuseRight $ init xs)

-- the first RE is an alt-element, so it's not an Alt/Opt/Emp/Lam
addSingleFuse :: RE -> [RE] -> OK [RE]
addSingleFuse c@(Cat i xs) ys | not (singularAlpha a)
                              = unchanged (c:ys)
                              | otherwise
                              = list2OK (c:ys) facts
                                where
                                a     = alpha (head xs)
                                bs    = alphaSplit a ys -- to avoid recomputation on backtracking
                                facts = [ kataCat [z,kataAlt[zr,zr']] : zs
                                        | (z,zr)<-factorAlpha a c, (z',zr',zs)<-bs, z==z']
addSingleFuse e ys            | not (singularAlpha a)
                              = unchanged (e:ys)
                              | otherwise
                              = list2OK (e:ys) [ kataCat [e,kataOpt zr'] : zs
                                               | (z',zr',zs)<-alphaSplit a ys, e==z']
                                where a=alpha e

-- the first RE is an alt-element, so it's not an Alt/Opt/Emp/Lam
addSingleFuseR :: RE -> [RE] -> OK [RE]
addSingleFuseR c@(Cat i xs) ys | not (singularAlpha a)
                               = unchanged (c:ys)
                               | otherwise
                               = list2OK (c:ys) facts
                                 where
                                 a     = alpha (last xs)
                                 bs    = alphaSplitR a ys -- to avoid recomputation on backtracking
                                 facts = [ kataCat [kataAlt[zr,zr'],z] : zs
                                         | (z,zr)<-factorAlphaR a c, (z',zr',zs)<-bs, z==z']
addSingleFuseR e ys            | not (singularAlpha a)
                               = unchanged (e:ys)
                               | otherwise
                               = list2OK (e:ys) [ kataCat [kataOpt zr',e] : zs
                                                | (z',zr',zs)<-alphaSplitR a ys, e==z']
                                 where a=alpha e

alphaSplit :: Alphabet -> [RE] -> [(RE,RE,[RE])]
alphaSplit alp xs  = [ (fy,fr,ys) | (y,ys)<-itemRest xs, (fy,fr)<-factorAlpha alp y ]
alphaSplitR :: Alphabet -> [RE] -> [(RE,RE,[RE])]
alphaSplitR alp xs = [ (fy,fr,ys) | (y,ys)<-itemRest xs, (fy,fr)<-factorAlphaR alp y ]

-- must only be used for singleton alphabet, otherwise the catSegment is unsound
factorAlpha :: Alphabet -> RE -> [(RE,RE)]
factorAlpha alp c@(Cat i xs) = [ (y,catSegment c ys) | (y,ys) <- factorAlphaCat alp xs ]
factorAlpha alp e            | alpha e==alp
                             = [(e,Lam)]
                             | otherwise
                             = []

factorAlphaR :: Alphabet -> RE -> [(RE,RE)]
factorAlphaR alp c@(Cat i xs) = [ (y,catSegment c (reverse ys)) | (y,ys) <- factorAlphaCat alp (reverse xs) ]
factorAlphaR alp e            | alpha e==alp
                              = [(e,Lam)]
                              | otherwise
                              = []

factorAlphaCat :: Alphabet -> [RE] -> [(RE,[RE])]
factorAlphaCat alp (x:xs) | alpha x/=alp
                          = []
                          | otherwise
                          = (x,xs) : [ (y,x:zs) | (y,zs)<- factorAlphaCat alp xs ]
factorAlphaCat alp []     = []

