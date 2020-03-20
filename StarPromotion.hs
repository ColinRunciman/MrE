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
promote = extension2trafo promoteExtension

promoteCxt = katahom promoteK

promoteK = trg promoteExtension
promoteH = mkHomTrans promoteK
HomTrans { falt=promoteAlt,  fcat=promoteCat, frep= promoteRep, fopt=promoteOpt} = fuseH

promoteKP = target promoteExtension

promoteP = tpr promoteExtension
isPromoted = checkWith promoteP

altPromotion, catPromotion :: RewRule
altPromotion c i xs = altSigmaStar c i xs `orOK` altSigmaStarPromotion i xs `orOK` altStarPrune c i xs `orOK`
                      altCharSubsumption i xs `orOK` altFactor1 c i xs `orOK`
                      altFactor1 c i xs `orOK` charFactor i xs

catPromotion c i xs = catSigmaStarPromotion c i xs `orOK` catStarPrune c i xs `orOK`
                      singularPrune xs `orOK` cat1Crush c i xs

catStarPrune RepCxt i xs | not (ew i) && not (isEmptyAlpha swx)
                         = innercrush swx xs `orOK` crushRightWrt swx xs `orOK` crushLeftWrt swx xs `orOK` innerPrune True xs
                           where
                           swx = sw i
catStarPrune OptCxt i xs | transitiveLift xs && hasChanged xs2
                         = okmap ((:[]).rep.cat) xs2
                           where
                           xs2 = catStarPrune RepCxt i xs
catStarPrune c _ xs = innerPrune (c>=OptCxt) xs

-- a sufficient, attribute-based condition for the sequence being transitive
transitiveLift :: [RE] -> Bool
transitiveLift (x:xs) = isRep x && not(isEmptyAlpha a1) && subAlpha a2 a1 ||
                        isRep y && not(isEmptyAlpha b1) && subAlpha b2 b1
                        where
                        a1 = swa x
                        b1 = swa y
                        a2 = al (catInfo xs)
                        b2 = al (catInfo ys)
                        Just(ys,y) = unsnoc (x:xs)


-- we need swa (cat xs)/=0 and not(all ewp xs) for this to be sound
innercrush :: Alphabet -> [RE] -> OK [RE]
innercrush swx xs = kataliftCat (remSig1 swx) xs

-- remove swx^+ from the language, this may (or not) be provided by other alternatives
wholyCrush :: Alphabet -> [RE] -> OK [RE]
wholyCrush al1 xs = alcatCrush al1 True xs

remSig1 swx x = if ewp x then remSigOuter swx x else remSigInner swx x

-- remSigOuter removes al1^+ from the language of x, these are (originally) cat-elems of a starred cat
-- it can also do that for rep-bodies, as the whole thing operates in a RepCxt
remSigOuter :: Alphabet  -> RE -> OK RE
remSigOuter al1 (Sym c)    | elemAlpha c al1 -- must be part of an optional expression, can be removed
                           = changed Emp
remSigOuter al1 (Alt i xs) | subAlpha (al i) al1
                           = changed Lam
                           | otherwise
                           = okmap alt $ katalift (remSigOuter al1) xs
remSigOuter al1 (Cat i xs) | subAlpha (al i) al1
                           = changed Lam -- in case the cat-was the only ewp-alternative
                           | otherwise
                           = okmap cat $ alcatCrush al1 False xs
remSigOuter al1 (Rep x)    = okmap rep (remSigOuter al1 x)
remSigOuter al1 (Opt x)    = okmap opt $ remSigOuter al1 x
remSigOuter _ x            = unchanged x

-- here we can remove al1^+ except that we need to keep al1 itself
remSigInner :: Alphabet -> RE -> OK RE
remSigInner al1 (Alt i xs) = okmap alt $ katalift (remSigInner al1) xs -- all alternatives are non-ewp
remSigInner al1 (Cat i xs) | subAlpha (al i) al1
                           = changed (alpha2Regexp (sw i))
                           | otherwise
                           = okmap cat $ alcatCrush al1 (not $ isEmptyAlpha (sw i .&&. al1)) xs
remSigInner _ x            = unchanged x

-- remove al1^+ from cat-sequence
-- if b is True then al1 itself needs to be preserved, but in that case xs contains at most one non-ewp element
alcatCrush :: Alphabet -> Bool -> [RE] -> OK [RE]
alcatCrush al1 b xs   | null mid || not(null (tail mid))
                      = unchanged xs
                      | b && not(ewp m)-- al1 itself needs to be preserved, and m is the one
                      = f (remSigInner al1 m)
                      | otherwise
                      = f (remSigOuter al1 m)
                        where
                        f           = okmap (\x->pref++(x:suff))
                        m           = head mid
                        pred e      = subAlpha (alpha e) al1
                        (pre1,suff) = spanEnd pred xs
                        (pref,mid)  = span pred pre1

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

-- this merges consecutive Rep's over the same singular alphabet, used to be part of Fuse
singularPrune :: [RE] -> OK [RE]
singularPrune xs = spl [] xs False
   where
   spl ts (Rep x:Rep y:zs) b | not(singularAlpha(alpha y))
                             = spl (Rep y:Rep x:ts) zs b
                             | alpha x==alpha y
                             = spl ts (rep(alt[x,y]) : zs) True
                             | otherwise
                             = spl (Rep x :ts) (Rep y:zs) b
   spl ts (x:xs) b           = spl (x:ts) xs b
   spl ts [] False           = unchanged xs
   spl ts [] True            = changed (reverse ts)

altStarPrune RepCxt i xs | not (ew i) && not (isEmptyAlpha swx)
                         = list2OK xs [ catSegment x xs':ys | (x@(Cat _ xs),ys) <-itemRest xs,
                                        xs' <- [ valOf xs1 | let xs1=crushRightWrt swx xs, hasChanged xs1 ]
                                            ++ [ valOf xs2 | let xs2=crushLeftWrt swx xs, hasChanged xs2 ]
                                            ++ [ valOf xs3 | let xs3=wholyCrush swx xs, hasChanged xs3 ]
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
    sigmastar = Rep (alpha2Regexp (al i))
    cands     = [ Rep y: ys2 |
                  (Rep y,ys)<-itemRest xs, let al1=swa y, not(isEmptyAlpha al1),
                  let (ys1,ys2)=partition (\r->subAlpha (alpha r) al1) ys,
                  not $ null ys1 ]

alpha2Regexp :: Alphabet -> RE
alpha2Regexp al1 = alt [Sym c | c<- alpha2String al1]

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

-- removes chars from alternatives that are subsumed by other alternatives
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

catSigmaStarPromotion :: Cxt-> Info -> [RE] -> OK [RE]
catSigmaStarPromotion RepCxt i xs   |  sw i==al i
                                    =  changed [ alpha2Regexp $ sw i ]
                                    |  not (isEmptyAlpha (sw i)) && hasChanged fc
                                    =  fc
                                       where fc = fixCrush (sw i) xs
catSigmaStarPromotion        c i xs | sw i /= cs
                                    = unchanged xs
                                    | ew i || c==OptCxt
                                    = list2OK xs [ [x] | x<-xs, sigmaStarTest cs x]
                                    | si i>totalplusSize cs && any (sigmaStarTest cs) xs -- size test ensures decrease
                                    = changed $ totalplus cs
                                    | otherwise
                                    = unchanged xs
                                      where cs = al i

-- language of non-empty  sequences of chars of the alphabet, as a cat-list
totalplus :: Alphabet -> [RE]
totalplus a = [ e1, rep e1] where e1=alpha2Regexp a

-- size of totalplus a
-- size ((a1+...+an)(a1+...+an)*) = 2*(2*n-1) + 2 = 4*n
totalplusSize :: Alphabet -> Int
totalplusSize a = 4*alphaLength a

crushRightWrt :: Alphabet -> [RE] -> OK [RE]
crushRightWrt al1 []      = unchanged []
crushRightWrt al1 (re:ps)
                       | isLam nre
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
crushRightInCxt c al1 re | c1 && c2
                         = changed Lam
                         | not c1 && c2 && swa re==al1 && size re>=2*alphaLength al1
                         = changed (alpha2Regexp al1)
                           where
                           c1 = c || ewp re
                           c2 = subAlpha (alpha re) al1
crushRightInCxt c al1 (Alt i res) = okmap alt $ katalift (crushRightInCxt (c||ew i) al1) res
crushRightInCxt _ al1 (Cat _ res) = okmap mkCat $ crushRightWrt al1 res
crushRightInCxt _ al1 (Opt re)    = okmap Opt   $ crushRightInCxt True al1 re
crushRightInCxt _ al1 (Rep c@(Cat i xs)) -- a Conway rule, alphaLength condition for efficiency only
                              | alphaLength (al i)>1 && isRep y && subAlpha(alpha r) al1
                              = changed $ rep (alt [r,catSegment c ys])
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
crushLeftInCxt c al1 re  | c1 && c2
                         = changed Lam
                         | not c1 && c2 && swa re==al1 && size re>=2*alphaLength al1
                         = changed (alpha2Regexp al1)
                           where
                           c1 = c || ewp re
                           c2 = subAlpha (alpha re) al1
crushLeftInCxt c al1 (Alt i res) = okmap alt $ katalift (crushLeftInCxt (c||ew i) al1) res
crushLeftInCxt _ al1 (Cat _ res) = okmap mkCat $ crushLeftWrt al1 res
crushLeftInCxt _ al1 (Opt re)    = okmap Opt   $ crushLeftInCxt True al1 re
crushLeftInCxt _ al1 (Rep c@(Cat i (Rep r:ys))) | subAlpha(alpha r) al1
                                                = changed $ rep (alt [r,catSegment c ys])
crushLeftInCxt _ _   e           = unchanged e


charFactor :: Info -> [RE] -> OK [RE]
charFactor i res =
    list2OK res $
    [ cat[Sym c,re2]:ys | c<-alpha2String (fi i), let (xs,ys)=partition (leftChar c) res, plural xs,
                          Just (_,re2) <- [refactor True (alt xs)]] ++
    [ cat[re2,Sym c]:ys | c<-alpha2String (la i), let (xs,ys)=partition (rightChar c) res, plural xs,
                          Just (_,re2) <- [refactor False (alt xs)]]


-- regexps satisfying these predicates can have the char left-factorised/right-factorised
leftChar, rightChar :: Char -> RE -> Bool
leftChar c re  = not (ewp re) && fir re==char2Alpha c
rightChar c re = not (ewp re) && las re==char2Alpha c


-- tries to factor out a single Character from an RE, support for Museum and alt-refactoring
refactor :: Bool -> RE -> Maybe (Char,RE)
refactor b (Sym c)     = Just (c,Lam)
refactor b (Alt i xs)  | ew i || b && not (singularAlpha (fi i)) || not b && not (singularAlpha (la i))
                       = Nothing
                       | otherwise
                       = Just (c,alt ys)
                          where
                          (c,ys) = process (map (refactor b) xs)
                          process (Just (d,x):ys) = (d,x:[y|Just(_,y)<- ys])
refactor b (Cat i xs)  | ew i || b && not (singularAlpha (fi i)) || not b && not (singularAlpha (la i))
                       = Nothing
                       | otherwise
                       = Just (c, (cat $ if b then ys else reverse ys))
                         where (c,ys) = refactorSequence b (if b then xs else reverse xs)
refactor b _           = Nothing


refactorSequence :: Bool -> [RE] -> (Char,[RE])
refactorSequence b (x:xs) | not (ewp x)
                          = (c,e:xs)
                          | otherwise
                          = (d,refactorRoll x d b:ys)
                            where
                            Just (c,e) = refactor b x
                            (d,ys)     = refactorSequence b xs
refactorSequence _ []     = error "empty sequence not factorisable"

-- add the char at the end/beginning, remove it from the other end
refactorRoll :: RE -> Char -> Bool -> RE
refactorRoll Emp  _ _       = error "invariant violation in rolling"
refactorRoll Lam  _ _       = Lam -- not needed because of options
refactorRoll (Sym c) _ _    = Sym c
refactorRoll (Alt _ xs) d b = alt [ refactorRoll x d b | x<- xs ]
refactorRoll (Cat _ xs) d True =   cat ys
                                   where (_,ys) = refactorSequence True (xs ++ [Sym d])
refactorRoll (Cat _ xs) d False =  cat (reverse ys)
                                   where (_,ys) = refactorSequence False $ reverse (Sym d: xs)
refactorRoll (Rep x) d b    = Rep (refactorRoll x d b)
refactorRoll (Opt x) d b    = Opt (refactorRoll x d b)

-- assumption: in RepCxt this is not ewp,
-- because altFuseList would get to break it up first
altSigmaStar :: Cxt -> Info -> [RE] -> OK [RE]
altSigmaStar c i xs |  c/=RepCxt || isEmptyAlpha (sw i)
                    =  unchanged xs
                    |  al i == sw i
                    =  updateEQ xs (map Sym $ alpha2String $ sw i)
                    |  otherwise
                    =  kataliftAlt (alphaCrush (sw i)) xs

-- if re is sublang of cs* replace it with cs', where cs' is its alphabet
-- the re is a subexp of an alt, so if re=sigma' already then re is a symbol
alphaCrush :: Alphabet -> RE -> OK RE
alphaCrush cs (Sym c) =  unchanged (Sym c)
alphaCrush cs re      |  subAlpha (alpha re) cs
                      =  changed (alpha2Regexp $ swa re)
                      |  otherwise
                      =  fixCrushRE cs re -- removes prefixes/suffixes

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
