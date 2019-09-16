module StarPromotion (
  promote, promoteP, promoteKP, isPromoted,
  promoteAlt, promoteCat, promoteOpt, promoteRep, promoteCxt ) where

import Expression
import Fuse
import OneLetterFactorization
import OK
import Context
import Info
import List
import Data.List (partition)
import Data.Bits
import Alphabet

-- Transformations in this module concern Rep x where x has the single-word
-- property for some sub-alphabet A --- a property memoised in the Info
-- fields of REs.  For example, if the Rep x occurs in an Alt or a Cat it may
-- absorb other Alt or Cat items, either wholly or in part.
-- (see altPromotion and catPromotion)
-- it also deals with transformations based on the notion that
-- concatenation of REs over a singular alphabet is commutative;
-- this is exploited for enhanced factorization/fusion in OneLetterFactorization module

promoteExtension :: Extension
promoteExtension = mkExtension altPromotion catPromotion fuseKP Promoted

promote :: RE -> RE
promote = mkTransform promoteK

promoteCxt = katahom promoteK

promoteK = trg promoteExtension
promoteH = mkHomTrans promoteK
HomTrans { falt=promoteAlt,  fcat=promoteCat, frep= promoteRep, fopt=promoteOpt} = fuseH

promoteKP = target promoteExtension

promoteP = tpr promoteExtension
isPromoted = checkWith promoteP

altPromotion, catPromotion :: RewRule
altPromotion c i xs = altSigmaStarPromotion i xs `orOK` altStarPrune c i xs `orOK`
                      altCharSubsumption i xs `orOK` altFactor1 c i xs

catPromotion c i xs = catSigmaStarPromotion i xs `orOK` catStarPrune c i xs `orOK` cat1Crush

catStarPrune RepCxt i xs | not (ew i) && not (isEmptyAlpha swx)
                         = crushRightWrt swx xs `orOK` crushLeftWrt swx xs `orOK` innerPrune True xs
                           where
                           swx = sw i
catStarPrune c _ xs = innerPrune (c>=OptCxt) xs

-- new 24072019 SMK
innerPrune :: Bool -> [RE] -> OK [RE]
innerPrune True [x,Rep y] | x==y
                          = changed [Rep y]
innerPrune True [Rep y,x] | x==y
                          = changed [Rep y]
innerPrune b xs =
    list2OK xs [valOf pp ++ (e:valOf ss) | (pre,e,suf)<-segElemSuf xs, isRep e,
                                            let swx=swa e, not(isEmptyAlpha swx),
                                            let pp=crushLeftWrt swx pre, let ss=crushRightWrt swx suf,
                                            hasChanged pp || hasChanged ss]
                                    
altStarPrune RepCxt i xs | not (ew i) && not (isEmptyAlpha swx)
                         = list2OK xs [ catSegment x xs':ys | (x@(Cat _ xs),ys) <-itemRest xs,
                                        xs' <- [ valOf xs1 | let xs1=crushRightWrt swx xs, hasChanged xs1 ]
                                            ++ [ valOf xs2 | let xs2=crushLeftWrt swx xs, hasChanged xs2 ]
                                      ]
                           where
                           swx = sw i
altStarPrune _ _ xs      = unchanged xs

altSigmaStarPromotion :: Info -> [RE] -> OK [RE]
altSigmaStarPromotion i xs |  any (==sigmastar) xs -- most common special case, singled out for efficiency
                           =  changed [ sigmastar ]
                           |  otherwise
                           =  list2OK xs cands                    
    where
    alphabet  = alpha2String (al i)
    sigmastar = Rep (kataAlt (map Sym alphabet))
    cands     = [ Rep y: ys2 |
                  (Rep y,ys)<-itemRest xs, let al1=swa y, not(isEmptyAlpha al1),
                  let (ys1,ys2)=partition (\r->subAlpha (alpha r) al1) ys,
                  not $ null ys1 ]

starredAlphas :: [RE] -> [Alphabet] -> [Alphabet]
starredAlphas [] ys         = nubSort ys
starredAlphas (Rep x:xs) ys = starredAlphas xs (swa x:ys)
starredAlphas (_ : xs)   ys = starredAlphas xs ys

altSigmaStarSubsumption :: Info -> [RE] -> OK [RE]
altSigmaStarSubsumption i xs = filterOK (not . demote css) xs
    where
    css = drop1 $ starredAlphas xs []
    drop1 (0:xs) = xs
    drop1 xs     = xs

isAlphabet :: RE -> Bool
isAlphabet (Sym _) = True
isAlphabet (Alt i xs) = not (ew i) && al i==sw i && all isSym xs

filterOK :: (a->Bool) -> [a] -> OK [a]
filterOK p xs = fOK xs [] False
                where
                fOK [] ys b = mkOK (reverse ys) b
                fOK (x:xs) ys b | p x
                                = fOK xs (x:ys) b
                                | otherwise
                                = fOK xs ys True

demote :: [Alphabet] -> RE -> Bool
demote css (Rep y) | isAlphabet y
                   = any (strictSubAlpha (alpha y)) css
                     where
                     ys=alpha y
demote css x       = any (subAlpha (alpha x)) css

altCharSubsumption :: Info -> [RE] -> OK [RE]
altCharSubsumption i xs = list2OK xs [ filter (goodElem cs) xs
                                     | not(isEmptyAlpha(sw i)), let cs=droppableAltSymbols xs,
                                       not(isEmptyAlpha cs) ]
                          where
                          goodElem chset (Sym c) = not $ elemAlpha c chset
                          goodElem chset _       = True

droppableAltSymbols :: [RE] -> Alphabet
droppableAltSymbols xs = dralsy xs emptyAlpha emptyAlpha
                         where
                         dralsy [] csym osym = csym .&. osym
                         dralsy (Sym x:xs) csym osym = dralsy xs (char2Alpha x .|. csym) osym
                         dralsy (y    :xs) csym osym = dralsy xs csym (swa y .|. osym)

swcheck :: Char -> RE -> Bool
swcheck c re = elemAlpha c (swa re) --elem c (fir re) && elem c (las re) && swp c re 

sigmaStarTest :: Alphabet -> RE -> Bool
sigmaStarTest cs (Rep x) = swa x==cs
sigmaStarTest cs _       = False

catSigmaStarPromotion :: Info -> [RE] -> OK [RE]
catSigmaStarPromotion i xs | ew i && sw i==cs
                           = list2OK xs [ [x] | x<-xs, sigmaStarTest cs x]
                           | otherwise
                           = unchanged xs
                             where cs = al i

crushRightWrt :: Alphabet -> [RE] -> OK [RE]
crushRightWrt al1 []      = unchanged []
crushRightWrt al1 (re:ps) | isLam nre
                       = unsafeChanged $ crushRightWrt al1 ps -- greedy
                       | b && not(ewp nre) && singularAlpha al3 && subAlpha al3 al1
                       = unsafeChanged $ okmap (nre:) $ crushRightWrt al3 ps --greedy
                       | not b && not(ewp re) && singularAlpha al2 && subAlpha al2 al1 
                       = okmap (re:) $ crushRightWrt al2 ps -- changed: used to require al1==al2
                       | b
                       = changed (nre:ps)
                       | otherwise
                       = unchanged (re:ps)
                         where
                         al2 = alpha re
                         al3 = alpha nre
                         c   = crushRightInCxt False al1 re
                         nre = valOf c
                         b   = hasChanged c 

crushRightInCxt :: Bool -> Alphabet -> RE -> OK RE
crushRightInCxt c al1 re | (c||ewp re) && subAlpha (alpha re) al1
                     = changed Lam
crushRightInCxt c al1 (Alt i res) = okmap kataAlt $ katalift (crushRightInCxt (c||ew i) al1) res
crushRightInCxt _ al1 (Cat _ res) = okmap mkCat $ crushRightWrt al1 res
crushRightInCxt _ al1 (Opt re)    = okmap Opt   $ crushRightInCxt True al1 re
crushRightInCxt _ al1 (Rep c@(Cat i xs)) -- a Conway rule, alphaLength condition for efficiency only
                              | alphaLength (al i)>1 && isRep y && subAlpha(alpha r) al1
                              = changed $ Rep (kataAlt [r,catSegment c ys])
                                where
                                Just(ys,y) = unsnoc xs
                                Rep r      = y
crushRightInCxt _ _    e          = unchanged e                       

crushLeftWrt :: Alphabet -> [RE] -> OK [RE]
crushLeftWrt al1 [] = unchanged []
crushLeftWrt al1 xs | isLam ny
                  = unsafeChanged $ crushLeftWrt al1 ys
                  | b && not(ewp ny) && singularAlpha al3 && subAlpha al3 al1
                  = unsafeChanged $ okmap (++ [ny]) $ crushLeftWrt al3 ys
                  | not b && not(ewp y) && singularAlpha al2 && subAlpha al2 al1 
                  = okmap (++[y]) $ crushLeftWrt al2 ys
                  | b
                  = changed (ys ++ [ny])
                  | otherwise
                  = unchanged xs
                    where
                    Just (ys,y) = unsnoc xs
                    al2 = alpha y
                    al3 = alpha ny
                    c   = crushLeftInCxt False al1 y
                    ny  = valOf c
                    b   = hasChanged c

crushLeftInCxt :: Bool -> Alphabet -> RE -> OK RE
crushLeftInCxt c al1 re | (c||ewp re) && subAlpha (alpha re) al1
                     = changed Lam
crushLeftInCxt c al1 (Alt i res) = okmap kataAlt $ katalift (crushLeftInCxt (c||ew i) al1) res
crushLeftInCxt _ al1 (Cat _ res) = okmap mkCat $ crushLeftWrt al1 res
crushLeftInCxt _ al1 (Opt re)    = okmap Opt   $ crushLeftInCxt True al1 re
crushLeftInCxt _ al1 (Rep c@(Cat i (Rep r:ys))) | subAlpha(alpha r) al1
                              = changed $ Rep (kataAlt [r,catSegment c ys])
crushLeftInCxt _ _   e           = unchanged e
