-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module OneLetterFactorization (altFactor1,cat1Crush) where
import Alphabet
import Info
import Expression
import Context
import OK
import Data.List
import List
import Fuse (fuseListProcess)

-- various transformation associated with cat-segments of an expression
-- belonging to a singular alphabet; these can be permuted, allowing for additional factorisations/fusions

altFactor1 :: RewRule
altFactor1 c i xs | singularAlpha (al i) -- for singular alphabet, common suffix/prefixes are the same thing
                  = altFactor1b True c i xs
                  | otherwise
                  = altFactor1b True c i xs `orOK` altFactor1b False c i xs

-- in the following, the Bool parameter means that this is the prefix version of the function
-- when True, otherwise the suffix version

altFactor1b :: Bool -> RewRule
altFactor1b b _ i xs = foldr (altFactorChar b) (unchanged xs) (alpha2String (fixchars b i))

altFactorChar :: Bool -> Char -> OK [RE] -> OK [RE]
altFactorChar b c oxs = app (altFactorFix b c) oxs

fixchars True  = fi
fixchars False = la

altFactorFix :: Bool -> Char -> [RE] -> OK [RE]
altFactorFix b c xs = ps `orOK` unchanged xs -- restore order if there is no change
    where
    al = char2Alpha c
    ps = okmap (map snd emps ++) $ fixMerge b $ listOp b $ sort $ nonemps
    (emps,nonemps) = partition (null . fst) $ map (altCharFix b al) xs

listOp :: Bool -> [a] -> [a]
listOp True  = reverse
listOp False = id

spanList :: Bool -> (a-> Bool) -> [a] -> ([a],[a])
spanList True  p xs = span p xs
spanList False p xs = -- spanEnd p xs, flipped
                      (reverse as, reverse bs)
                      where
                      (as,bs) = span p (reverse xs)

-- altCharFix produces a list of the common prefixes/suffixes
-- over (singluar) alphabet al of the expression, paired with its remainder
altCharFix :: Bool -> Alphabet -> RE -> ([RE],RE)
altCharFix b al (Cat _ xs)  =  (listOp b $ sort pre, cat suf)
                               where
                               (pre,suf) = spanList b ((==al) . alpha) xs
altCharFix b al e  | alpha e==al
                   = ([e],Lam)
                   | otherwise
                   = ([],e)

startsWith :: Eq a => a -> [a] -> Bool
startsWith x [] = False
startsWith x (y:xs) = x==y

dropFactor :: ([a],b) -> ([a],b)
dropFactor (x:xs,y) = (xs,y)

bsnoc :: Bool -> [RE] -> RE -> RE
bsnoc True  xs x = cat (xs ++ [x])
bsnoc False xs x = cat (x:xs)

bcat :: Bool -> RE -> RE -> RE
bcat True x y  = cat [y,x]
bcat False x y = cat [x,y]

insertFun :: Ord a => Bool -> a -> [a] -> [a]
insertFun True  = insertBy (flip compare)
insertFun False = insert

fixMerge :: Bool -> [([RE],RE)] -> OK [RE]
fixMerge _ []               =  unchanged []
fixMerge b [(fix,e)]        =  unchanged [ bsnoc b fix e ] -- one alternative left, no common factors
fixMerge b (([],e):xs)      =  okmap (e:) $ fixMerge b xs  -- not an eligible prefix/suffix, skip it
fixMerge b ((p1:ps,e1):xs)  |  null xs1 && null ps -- p1 not shared, no remaining prefix, avoid inserting it
                            =  okmap (bcat b e1 p1:) $ fixMerge b xs
                            |  null xs1 -- fix p1 is not shared, push it to tail, try others
                            =  fixMerge b (insertFun b (ps,bcat b e1 p1) xs)
                            |  otherwise
                            =  do 
                               nx1 <- fixMerge b ((ps,e1):map dropFactor xs1)
                               let ne1 = bcat b (alt nx1) p1
                               nx2 <- fixMerge b xs2
                               changed (ne1:nx2)
                               where
                               (xs1,xs2) = span (startsWith p1 . fst) xs

-- rewrite rule for cats, context & info are ignored
cat1Crush :: RewRule
--cat1Crush _ _ = singularCatSort . partSegments
cat1Crush _ _ xs  |  hasChanged nxs
                  =  nxs
                  |  xs == valOf nxs
                  =  nxs
                  |  otherwise -- rearrangment, but no size change; report change
                  =  unsafeChanged nxs
                     where nxs = singularCatSort (partSegments xs)

data ReSegment = Plain [RE] | Special Alphabet [RE]

-- for testing purposes; these segments are local to the module
instance Show ReSegment where
    showsPrec _ (Plain xs)     = showsPrec 0 xs
    showsPrec _ (Special a xs) = (alpha2String a ++) . showsPrec 0 xs

-- splits the list into plain segments and special segments
-- each special segment is a maximal segment over a singular alphabet
-- and (eventually) not a singleton
partSegments :: [RE] -> [ReSegment]
partSegments = crushTop . foldr addRE []

addRE :: RE -> [ReSegment] -> [ReSegment]
addRE e xs | singularAlpha ae
           = addSpecial e ae xs
           | otherwise
           = addPlain e xs
             where ae = alpha e

addSpecial :: RE -> Alphabet -> [ReSegment] -> [ReSegment]
addSpecial e ae (Special a xs : ys) 
                   |  ae==a -- increase segment
                   =  Special a (e:xs) : ys
                   |  not(plural xs) -- singleton segment becomes plain, start fresh one
                   =  Special ae [e] : addPlain (head xs) ys
                   |  otherwise      -- just start fresh segment
                   =  Special ae [e] : Special a xs : ys
addSpecial e ae ys =  Special ae [e] : ys

addPlain e (Plain xs : ys)     =  Plain(e:xs) : ys
addPlain e (Special a xs : ys) |  plural xs -- start fresh segment
                               =  Plain [e] : Special a xs : ys
                               |  otherwise -- crush singleton special
                               =  addPlain e $ addPlain (head xs) ys
addPlain e []                  =  [Plain [e]]

-- if first segment is special singleton, crush it
crushTop :: [ReSegment] -> [ReSegment]
crushTop (Special a [x] : xs) = addPlain x xs
crushTop xs                   = xs

singularCatSort :: [ReSegment] -> OK [RE]
singularCatSort []                  = unchanged []
singularCatSort (Plain xs : ys)     = okmap (xs++) $ singularCatSort ys
singularCatSort (Special a xs : ys) =
    do
        nxs <- fuseListProcess (sort xs)
        nys <- singularCatSort ys
        return (nxs++nys)





 
