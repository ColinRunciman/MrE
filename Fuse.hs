module Fuse where

import List
import Expression
import Context
import Info
import Function ((===>))
import Alphabet
import Data.List

-- boilerplate, giving things names
type FuseRE = RE

fuseEX :: Extension
fuseEX = mkExtension altFuseList catFuseList kataGradeKP Fused

fuseK :: Katahom
fuseK = trg fuseEX
-- normK = Katahom { kalt=normAltK, kcat=normCatK, grade=Normal}

fuseKP :: KataPred
fuseKP = target fuseEX

fuse :: RE -> FuseRE
fuse = mkTransform fuseK

fuseCxt :: Cxt -> RE -> OK FuseRE
fuseCxt = katahom fuseK


-- normH = HomTrans { falt=normAlt,  fcat=normCat, frep= normRep, fopt=fuseOpt}
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

{-
-- extendfusion would correspond to a different linear order on REs
leftOrderedFusion :: Fusion RE
leftOrderedFusion x@(Cat ix xs) y@(Cat iy ys) =
    case compare (head xs) (head ys) of
        LT -> Right True
        EQ -> Left (fuseCat [head xs, mkAlt [catSegment x (tail xs), catSegment y (tail ys)] ])
        GT -> Right False
leftOrderedFusion x y@(Cat iy ys) =
    case compare x (head ys) of
        LT -> Right True
        EQ -> Left (fuseCat [ x, Opt(catSegment y (tail ys))])
        GT -> Right False 
leftOrderedFusion x@(Cat ix xs) y =
    case compare (head xs) y of
        LT -> Right True
        EQ -> Left (fuseCat [ y, Opt(catSegment x (tail xs))])
        GT -> Right False
leftOrderedFusion x y =
    case compare x y of
        LT -> Right True
        EQ -> Left x
        GT -> Right False
-}
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
{-
rightOrderedFusion :: Fusion RE
rightOrderedFusion x@(Cat ix xs) y@(Cat iy ys) =
    case compare (last xs) (last ys) of
        LT -> Right True
        EQ -> Left (fuseCat [mkAlt [catSegment x (init xs), catSegment y (init ys)],last xs])
        GT -> Right False
rightOrderedFusion x y@(Cat iy ys) =
    case compare x (last ys) of
        LT -> Right True
        EQ -> Left (fuseCat [Opt(catSegment y (init ys)), x])
        GT -> Right False 
rightOrderedFusion x@(Cat ix xs) y =
    case compare (last xs) y of
        LT -> Right True
        EQ -> Left (fuseCat [Opt(catSegment x (init xs)), y])
        GT -> Right False
rightOrderedFusion x y =
    case compare x y of
        LT -> Right True
        EQ -> Left x
        GT -> Right False
-}
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

{-
idea for a better commonList function
commonList2 :: [RE] -> [RE] -> Either ([RE],[RE],[RE]) ([RE],[RE])
commonList2 [] xs = Right ([],xs)
commonList2 xs [] = Right (xs,[])
commonList2 (x:xs) (y:ys) | x==y
                          = addElem x $ commonList2 xs ys
                          | xa == ya && singletonAlpha xa
                          = case commonMultiSet (sort xs1)(sort ys1) of
                                 Right _ -> Right (x:xs,y:ys)
                                 Left(zs,[],[]) -> case commonList2 xs2 ys2 of
                                                       Right _        -> Left(zs,xs2,ys2)
                                                       Left(cs,ds,es) -> Left (zs++cs,ds,es)
                                 Left(zs,as,bs) -> Left(zs,as++xs2,bs++ys2)
                          | otherwise
                          = Right(x:xs,y:ys)
                            where
                            xa = alpha x
                            ya = alpha y
                            (xs1,xs2) = oneletterSplit (x:xs)
                            (ys1,ys2) = oneletterSplit (y:ys)

commonMultiSet :: [RE] -> [RE] -> Either ([RE],[RE],[RE]) ([RE],[RE])
commonMultiSet [] xs = Right ([],xs)
commonMultiSet xs [] = Right (xs,[])
commonMultiSet (x:xs) (y:ys) =
    case compare x y of
        LT -> leftAdd x $ commonMultiSet xs (y:ys)
        GT -> rightAdd y $ commonMultiSet (x:xs) ys
        EQ -> addElem x $ commonMultiSet xs ys

oneletterSplit :: [RE] -> ([RE],[RE])
oneletterSplit [] = ([],[])
oneletterSplit (x:xs) | singletonAlpha a
                      = (x:ys,zs)
                      | otherwise
                      = ([],x:xs)
                        where
                        a = alpha x
                        (ys,zs) = span ((==a).alpha) xs

addElem, leftAdd, rightAdd :: RE -> -> Either ([RE],[RE],[RE]) ([RE],[RE]) -> Either ([RE],[RE],[RE]) ([RE],[RE])
addElem x (Left(cs,ls,rs)) = Left(x:cs,ls,rs)
addElem x (Right(ls,rs))   = Left([x],ls,rs)

leftAdd x ((Left(cs,ls,rs)) = Left(cs,x:ls,rs)
leftAdd x (Right(ls,rs))    = Right(x:ls,rs) 

rightAdd x ((Left(cs,ls,rs)) = Left(cs,ls,x:rs)
rightAdd x (Right(ls,rs))    = Right(ls,x:rs) 
-}

firstDiff :: Ord a => Int -> [a] -> [a] -> (Int,Bool)
firstDiff k [] xs = (k,True)
firstDiff k xs [] = (k,True)
firstDiff k (x:xs) (y:ys) =
    case compare x y of
        EQ -> firstDiff(k+1) xs ys
        bb -> (k,bb==LT)
        



-- maps shallow-mirrored REs into other shallow-mirrored ones
-- so cat-lists moving away from the root need to be reversed
{- no longer used, was buggy
backfusion :: Fusion RE
backfusion (Cat ix (x:xs)) (Cat iy (y:ys)) =
    case compare x y of
        LT -> Right True
        EQ -> Left (mkCat [x, mkAlt [mkCatFrom (gr ix)(reverse xs), mkCatFrom (gr iy) (reverse ys)] ])
        GT -> Right False
backfusion x (Cat iy (y:ys)) =
    case compare x y of
        LT -> Right True
        EQ -> Left (mkCat [ x, Opt(mkCatFrom (gr iy)(reverse ys))])
        GT -> Right False 
backfusion (Cat ix (x:ys)) y =
    case compare x y of
        LT -> Right True
        EQ -> Left (mkCat [ x, Opt(mkCatFrom (gr ix) (reverse ys))])
        GT -> Right False
backfusion x y =
    case compare x y of
        LT -> Right True
        EQ -> Left x
        GT -> Right False
-}

{-
extractCompare :: Eq a => Fusion a -> (a->a->Ordering)
extractCompare fuse x y =
    case fuse x y of
        Left _ -> if x==y then EQ else LT -- or GT, should not matter as they fuse
        Right True -> LT
        Right False -> GT
-}
    
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

{-
OBSOLETE
-- notice that info field really applies to the fully-mirrored RE
-- however, size, swp, ewp, alphabet remain unchanged anyway
-- gradings are preserved, because graded REs will be mirrored back anyway
shallowMirror :: FuseRE -> RE
shallowMirror (Cat i xs) =  Cat ni rxs
                            where
                            rxs = reverse xs
                            ni  = i{fi=la i, la=fi i}
                            --ni = if null (gr i) then i{fi=firCat rxs} else i
shallowMirror r          =  r
-}

-- fusion compatible with standard order on REs only
{- NOT USED!
basicfusion :: Fusion RE
basicfusion (Cat _ (x:xs)) (Cat _ (y:ys)) =
    case compare x y of
        LT -> Right True
        EQ -> Left (mkCat [ x, mkAlt [mkCat xs, mkCat ys] ])
        GT -> Right False
basicfusion x y =
    case compare x y of
        LT -> Right True
        EQ -> Left x
        GT -> Right False
-}

altFuseList :: Cxt -> Info -> [FuseRE] -> OK [RE]
altFuseList c i xs = guardApply (ew i && c==RepCxt) whiteList xs `orOK`
                     altSigmaStar c i xs `orOK`
                     leftfuse xs `orOK` rightfuse xs `orOK`
                     singleLetterFuseLeft xs `orOK` singleLetterFuseRight xs


altSigmaStar :: Cxt -> Info -> [RE] -> OK [RE]
altSigmaStar c i xs |  c/=RepCxt || isEmptySet (sw i)
                    =  unchanged xs
                    |  charSet(al i) == sw i
                    =  updateEQ xs (map Sym (enumerateSet $ sw i))
                    |  otherwise
                    =  kataliftAlt (debunk (sw i)) xs

-- if re is sublang of cs* replace it with cs', where cs' is its alphabet
-- the re is a subexp of an alt, so if re=sigma' already then re is a symbol
-- TO DO: could possibly be strengthened by removing cs* from nullable prefixes/suffixes too
debunk :: CharSet -> RE -> OK RE
debunk cs (Sym c) =  unchanged (Sym c)
debunk cs re      |  subsetS alset cs
                  =  changed (mkAlt (map Sym allst))
                  |  otherwise
                  =  unchanged re
                     where
                     alset = charSet $ alpha re
                     allst = enumerateSet (swa re) -- was alset, swa re suffices 31072019

-- might also do first-rolls in here, but only when also mirrored, and with las attribute
-- TO DO: could be strengthened too by removing sw* from nullable prefixes/suffixes
-- TO DO: the RepCxt can/should be promoted to suffixes (prefixes) if the omitted prefix (suffix) is nullable
--  this means: if sw is non-trivial then (i) remove optional suffixes/prefixes having sw as alphabet from sequence
--  and (ii) replace bodies that have sw as alphabet with sw
catFuseList :: Cxt -> Info -> [FuseRE] -> OK [KataRE]
catFuseList RepCxt i xs  |  ew i
                         =  changed [ kataAlt (whiteList xs) ]
                         |  sw i==charSet(al i)
                         =  changed [ kataAlt (map Sym (enumerateSet $ sw i)) ]
                            --where sw=allswpsCat xs
catFuseList _ i xs       =  fuseListProcess False [] xs
{- the stuff below is not wrong, but creates issues with the termination of compRE
   SMK 170719
catFuseList _ i xs       |  singletonAlpha(al i) --to avoid bubblesorting the lot
                         =  fuseListProcess (xs/=nxs) [] nxs
                         |  otherwise
                         =  fuseListProcess False [] xs
                            where nxs=sort xs
-}

-- left argument: list of already processed elements, in reverse order
-- right argument: unprocessed, but all cat-elements
fuseListProcess :: Bool -> [FuseRE] -> [FuseRE] -> OK [FuseRE]
fuseListProcess changed xs []     =  mkOK (reverse xs) changed
fuseListProcess changed [] (x:xs) =  fuseListProcess changed [x] xs
fuseListProcess changed (Rep x:xs) (Rep y:ys)
                          |  x == y
                          =  fuseListProcess True (Rep x:xs) ys
                          -- new 06072018, fusing * when single-letter alphabet
                          |  a == alpha y && singletonAlpha a
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
{- sorting for single-letter alpha taken out, because it interfere with compRE
   SMK 17072019
fuseListProcess changed (x:xs) (y:ys)
                          -- new 05092018, ordering when single-letter alphabet
                          |  alpha y == a && singletonAlpha a && x>y -- singleton alphabet segment acts as multiset, so we (bubble-)sort
                          =  fuseListProcess True xs (y:x:ys)
                             where
                             a = alpha x
-}                
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

-------------------------- Normalisation ----------------------------------------------------------------------------


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

-- normRep :: FuseRE -> FuseRE
{-
normRep Emp = Lam
normRep Lam = Lam
normRep (Rep x) = Rep x
normRep (Opt x) = Rep x
normRep x = Rep $ white x
-}

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
addSingleFuse c@(Cat i xs) ys | not (singletonAlpha a)
                              = unchanged (c:ys)
                              | otherwise
                              = list2OK (c:ys) facts
                                where
                                a     = alpha (head xs)
                                bs    = alphaSplit a ys -- to avoid recomputation on backtracking
                                facts = [ kataCat [z,kataAlt[zr,zr']] : zs
                                        | (z,zr)<-factorAlpha a c, (z',zr',zs)<-bs, z==z']
addSingleFuse e ys            | not (singletonAlpha a)
                              = unchanged (e:ys)
                              | otherwise
                              = list2OK (e:ys) [ kataCat [e,kataOpt zr'] : zs
                                               | (z',zr',zs)<-alphaSplit a ys, e==z']
                                where a=alpha e

-- the first RE is an alt-element, so it's not an Alt/Opt/Emp/Lam
addSingleFuseR :: RE -> [RE] -> OK [RE]
addSingleFuseR c@(Cat i xs) ys | not (singletonAlpha a)
                               = unchanged (c:ys)
                               | otherwise
                               = list2OK (c:ys) facts
                                 where
                                 a     = alpha (last xs)
                                 bs    = alphaSplitR a ys -- to avoid recomputation on backtracking
                                 facts = [ kataCat [kataAlt[zr,zr'],z] : zs
                                         | (z,zr)<-factorAlphaR a c, (z',zr',zs)<-bs, z==z']
addSingleFuseR e ys            | not (singletonAlpha a)
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

                              
                              

