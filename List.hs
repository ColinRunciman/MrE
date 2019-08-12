module List (
   unsnoc, linkWith, plural, strictlyOrdered, maximaBy,
   nubMerge, foldMerge, nubSort, chainSort,
   segments, segPreSuf, segElemSuf, segmentsPred, segmentsLPred,
   splits, allSplits, powerSplits, allPowerSplits, powerSplitsPred, powerSplitsLPred,
   compareLength, itemRest, sublists, isSublistOf,
   subsetRest, intersectSet, unions, unionsMulti, removeFromSet,
   lift2SeqAll ) where

import Data.Maybe (fromMaybe, isNothing)
import Data.List (inits, tails, union)

-- A plural list has at least two elements.
plural :: [a] -> Bool
plural (x:y:etc)  =  True
plural _          =  False

lift2SeqAll :: (a->Maybe a) -> [a] -> Maybe [a]
lift2SeqAll trans xs
    | all isNothing ys  =  Nothing
    | otherwise         =  Just $ zipWith fromMaybe xs ys
    where
    ys = map trans xs

-- The result of linkedBy r xs is true if r x x' holds for all
-- segments [x,x'] of xs.
linkedBy :: (a->a->Bool) -> [a] -> Bool
linkedBy r (x:y:etc)  =  r x y && linkedBy r (y:etc)
linkedBy _ _          =  True 

linkWith :: (a->a->b) -> [a] -> [b]
linkWith f (x:y:etc) = f x y : linkWith f (y:etc)
linkWith _ _ = []

ordered, strictlyOrdered :: Ord a => [a] -> Bool
ordered          =  linkedBy (<=)
strictlyOrdered  =  linkedBy (<)

orderedBy, strictlyOrderedBy :: (a->a->Ordering) -> [a] -> Bool
orderedBy cmp               =  linkedBy (\x y->cmp x y /= GT)
strictlyOrderedBy cmp       =  linkedBy (\x y->cmp x y == LT)

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys          =  ys
merge xs []          =  xs
merge (x:xs) (y:ys)  =  case compare x y of
                        LT -> x : merge xs (y:ys)
                        EQ -> x : y : merge xs ys
                        GT -> y : merge (x:xs) ys

nubMerge :: Ord a => [a] -> [a] -> [a]
nubMerge [] ys          =  ys
nubMerge xs []          =  xs
nubMerge (x:xs) (y:ys)  =  case compare x y of
                           LT -> x : nubMerge xs (y:ys)
                           EQ -> x : nubMerge xs ys
                           GT -> y : nubMerge (x:xs) ys

compareLength :: [a] -> [b] -> Ordering
compareLength [] [] = EQ
compareLength [] _  = LT
compareLength _  [] = GT
compareLength (_ :xs) (_ : ys) = compareLength xs ys

foldMerge :: (a->a->a) -> a -> [a] -> a
foldMerge b e [] = e
foldMerge b e [x] = x
foldMerge b e xs = foldMerge b e (foldMerge1 b xs)

foldMerge1 :: (a->a->a) -> [a] -> [a]
foldMerge1 b [] = []
foldMerge1 b [x] = [x]
foldMerge1 b (x:y:xs) = b x y : foldMerge1 b xs

-- sorts a list into a set whilst throwing out dups, mergeSort style
nubSort :: Ord a => [a] -> [a]
nubSort = foldMerge nubMerge [] . nubChains

-- splits a list into its segments of increasing chains
chains :: Ord a => [a] -> [[a]]
chains = foldr addOne []
            where
            addOne x [] = [[x]]
            addOne x chains@((y:ys):yss) = if x<=y then (x:y:ys):yss else [x]:chains

-- bottom-up mergeSort
chainSort :: Ord a => [a] -> [a]
chainSort = foldMerge merge [] . chains 

-- like chains, but the produced chains are dup-free
nubChains :: Ord a => [a] -> [[a]]
nubChains = foldr addOne []
            where
            addOne x [] = [[x]]
            addOne x chains@((y:ys):yss) =
                case compare x y of 
                    LT -> (x:y:ys):yss
                    EQ -> chains
                    GT -> [x]:chains

-- like \\ but for set-like lists and exploits order
nubRemove :: Ord a => [a] -> [a] -> [a]
nubRemove [] _          = []
nubRemove xs []         = xs
nubRemove (x:xs) (y:ys) =
    case compare x y of
        LT -> x : nubRemove xs (y:ys)
        EQ -> nubRemove xs ys
        GT -> nubRemove (x:xs) ys

mergeBy :: (a->a->Ordering) -> [a] -> [a] -> [a]
mergeBy cmp [] ys          =  ys
mergeBy cmp xs []          =  xs
mergeBy cmp (x:xs) (y:ys)  =  case cmp x y of
                           LT -> x : mergeBy cmp xs (y:ys)
                           _  -> y : mergeBy cmp (x:xs) ys

insertSet :: Ord a => a -> [a] -> [a]
insertSet x [] = [x]
insertSet x inp@(y:ys) =
    case compare x y of
        LT -> x:inp
        EQ -> inp
        GT -> y:insertSet x ys

-- intersection of sorted set-like list
intersectSet :: Ord a => [a] -> [a] -> [a]
intersectSet (x:xs)(y:ys) =
    case compare x y of
        LT -> intersectSet xs (y:ys)
        EQ -> x : intersectSet xs ys
        GT -> intersectSet (x:xs) ys
intersectSet [] _  = []
intersectSet _ []  = []

-- subset of set-like lists
subsetOrd :: Ord a => [a] -> [a] -> Bool
subsetOrd (x:xs) (y:ys) =
    case compare x y of
        LT -> False
        EQ -> subsetOrd xs ys
        GT -> subsetOrd (x:xs) ys
subsetOrd [] _     = True
subsetOrd (_:_) [] = False

-- removes an element from a set-like list, but fails if element is not there
-- spec: removeFromSet x ys = listToMaybe [ zs | (y,zs)<-itemRest ys, y==x]
removeFromSet :: Ord a => a -> [a] -> Maybe [a]
removeFromSet x xs = rfs xs id
    where
    rfs [] _     = Nothing
    rfs (y:ys) f =
       case compare x y of
           LT -> Nothing
           EQ -> Just $ f ys
           GT -> rfs ys (f . (y:))

-- The result of anyRest p q xs is True when for some item x in xs, p x is True
-- and for all other items q x is True.  The item x need not be unique.
anyRest :: (a->Bool) -> (a->Bool) -> [a] -> Bool
anyRest p q xs = any (all q) [ys | (x,ys) <- itemRest xs, p x]

-- All choices of one item from a list paired with the list of remaining items.
itemRest :: [a] -> [(a,[a])]
itemRest []     = []
itemRest (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- itemRest xs]

-- All possible divisions of a list into non-empty prefix and suffix.
splits :: [a] -> [([a],[a])]
splits []     = []
splits [_]    = []
splits (x:ys) = ([x],ys) : [(x:ys1, ys2) | (ys1,ys2) <- splits ys]

-- Like splits but allowing empty prefix and/or suffix.
allSplits :: [a] -> [([a],[a])]
allSplits []      =  [([],[])]
allSplits (x:ys)  =  ([],x:ys) : [(x:ys1, ys2) | (ys1,ys2) <- allSplits ys]

-- similar as splits, for set-like lists,
-- so it's a form of powerset of non-empty subsets and non-empty remainders
powerSplits :: [a] -> [([a],[a])]
powerSplits [] = []
powerSplits xs = init $ tail $ allPowerSplits xs

-- similar as allSplits, for set-like lists, so it's a form of powerset,
-- but with the remainder
allPowerSplits :: [a] -> [([a],[a])]
allPowerSplits []     = [([],[])]
allPowerSplits (x:xs) = [(x:ys1,ys2)|(ys1,ys2)<-nxs] ++ [(ys1,x:ys2)|(ys1,ys2)<-nxs]
    where
    nxs = allPowerSplits xs

-- splits a list-set into two parts, the first of being non-empty and elements satisfying the predicate
powerSplitsPred :: (a->Bool) -> [a] -> [([a],[a])]
powerSplitsPred p [] = []
powerSplitsPred p (x:xs) | p x
                         = ([x],xs) : [ (x:ys1,ys2)|(ys1,ys2)<-nxs] ++ [(ys1,x:ys2)|(ys1,ys2)<-nxs]
                         | otherwise
                         = [(ys1,x:ys2)|(ys1,ys2)<-nxs]
                           where
                           nxs = powerSplitsPred p xs

-- like powerSplitsPred, but with a predicate working for lists
-- p is meant to be sublist-closed
-- the selected segments satisfy p and are non-empty
powerSplitsLPred :: ([a]->Bool) -> [a] -> [([a],[a])]
powerSplitsLPred p [] = []
powerSplitsLPred p (x:xs) | p [x]
                         = ([x],xs) : [ (x:ys1,ys2)|(ys1,ys2)<-nxs, p(x:ys1)] ++ [(ys1,x:ys2)|(ys1,ys2)<-nxs]
                         | otherwise
                         = [(ys1,x:ys2)|(ys1,ys2)<-nxs]
                           where
                           nxs = powerSplitsLPred p xs

-- The result of prefixRest n xs is list which is empty if n exceeds the length
-- of xs, or else a singleton list containing (take n xs, drop n xs).
prefixRest :: Int -> [a] -> [([a],[a])]
prefixRest n xs = [splitAt n xs | n <= length xs]

-- The result of segPreSuf n xs is a list of all triples (pre,seg,suf)
-- such that seg is a segment of xs of length n, pre is the prefix of
-- xs before seg and suf is the suffix of xs after seg.
segPreSuf :: Int -> [a] -> [([a],[a],[a])]
segPreSuf n xs = [ (pre,seg,suf)
                 | m <- [0..(length xs - n)],
                   (pre,xs') <- prefixRest m xs,
		   (seg,suf) <- prefixRest n xs' ]

-- spec: segElemSuf xs == [(ys,x,zs)|(ys,[x],zs)<-segPreSuf 1 xs]
segElemSuf :: [a] -> [([a],a,[a])]
segElemSuf [] = []
segElemSuf (x:xs) = ([],x,xs) : [ (x:ys,y,zs) | (ys,y,zs)<-segElemSuf xs ]

-- partitions a list into all segments, so that all elements of the middle segment satisfy predicate
-- and that middle part is non-empty
segmentsPred :: (a->Bool) -> [a] -> [([a],[a],[a])]
segmentsPred p []     = []
segmentsPred p (x:xs) |  p x
                      =  ([],[x],xs) :
                         [ (l,r,c) | (a,b,c)<-rec, (l,r) <- (x:a,b) : [ ([],x:b) | null a]]
                      |  otherwise
                      =  [ (x:a,b,c) | (a,b,c)<-rec ]
                        where
                        rec = segmentsPred p xs

-- like segmentsPred, but the predicate applies to segments, and is meant to be subsegment-closed
segmentsLPred :: ([a]->Bool) -> [a] -> [([a],[a],[a])]
segmentsLPred p []     = []
segmentsLPred p (x:xs) |  p [x]
                      =  ([],[x],xs) :
                         [ (l,r,c) | (a,b,c)<-rec, (l,r) <- (x:a,b) : [ ([],x:b) | null a, p(x:b)]]
                      |  otherwise
                      =  [ (x:a,b,c) | (a,b,c)<-rec ]
                        where
                        rec = segmentsLPred p xs
 


isSublistOf :: Eq a => [a] -> [a] -> Bool
isSublistOf []     _       =  True
isSublistOf _      []      =  False
isSublistOf (x:xs) (y:ys)  |  x==y
                           =  isSublistOf xs ys
                           |  otherwise
                           =  isSublistOf (x:xs) ys

-- The result of sublists xs is a list of all sublists
-- of xs (ie. lists like xs but with zero or more items omitted).
sublists :: [a] -> [[a]]
sublists []      =  [[]]
sublists (x:xs)  =  xss ++ map (x:) xss
                    where
                    xss  =  sublists xs

-- A variation of sublists: only items satisfying a given predicate
-- may be omitted.
sublistsBy :: (a->Bool) -> [a] -> [[a]]
sublistsBy p []      =  [[]]
sublistsBy p (x:xs)  |  p x
                     =  xss ++ map (x:) xss
                     |  otherwise
                     =  map (x:) xss
                     where
                        xss  =  sublistsBy p xs

-- The result of segments xs is a list of all
-- segments of xs (ie. lists like xs but with zero or more
-- items omitted at each end).
segments :: [a] -> [[a]]
segments xs  =  [] : [s | t <- tails xs, not (null t),
                          s <- inits t,  not (null s)]

maxSegmentedBy :: (a->a->Bool) -> [a] -> [[a]]
maxSegmentedBy _ []         =  []
maxSegmentedBy _ [x]        =  [[x]]
maxSegmentedBy r (x:y:etc)  |  r x y
                            =  (x:ys) : yss
                            |  otherwise
                            =  [x] : ys : yss
  where
  ys:yss  =  maxSegmentedBy r (y:etc)


-- The result of subsetRest n xs lists all subsequences of xs of length n,
-- each paired with the corresponding residue of xs.
subsetRest :: Int -> [a] -> [([a],[a])]
subsetRest 0 xs      =  [([], xs)]
subsetRest _ []      =  []
subsetRest n (x:xs)  =  [(x:as, bs) | (as,bs) <- subsetRest (n-1) xs] ++
                        [(as, x:bs) | (as,bs) <- subsetRest n     xs]

-- The result of segPartitionBy p xs is a pair (yss,nss) where yss lists the
-- maximal segments in which each element satisfies p and ns the maximal
-- non-p  segments.  By convention xs = concat (interleave yss nss), so the
-- first element of yss may be [].
segPartitionBy :: (a->Bool) -> [a] -> ([[a]],[[a]])
segPartitionBy p xs  =  if null etc then ([ys],[]) else (ys:yss,ns:nss) 
   where
   (ys, etc)  =  span p xs 
   (ns, xs')  =  span (not . p) etc
   (yss,nss)  =  segPartitionBy p xs' 

interleave :: [a] -> [a] -> [a]
interleave [] ys = ys
interleave (x:xs) ys = x:interleave ys xs

-- cross product
cross :: [a] -> [b] -> [(a,b)]
cross xs ys =  [(x,y) | x<- xs, y<-ys]

-- Given a list xs :: [a] of distinct items, and a predicate
-- p :: a -> a -> Bool, obtain a minimal sublist ys of xs such that
-- for every x in xs \\ ys there is a y in ys for which p x y holds.
-- The predicate p may be assumed transitive.
-- NB. The method here is "greedy": it considers successive elements
-- of xs for addition to an accumulating sublist.  The result is the
-- only one possible if p is also anti-symmetric.  If it is not, and
-- the choice of solution may matter, the function could be generalised
-- to give all possible results.
maximaBy :: (a->a->Bool) -> [a] -> [a]
maximaBy p  =  mb []
  where
  mb ms []      =  reverse ms
  mb ms (x:xs)  |  any (p x) ms || any (p x) xs
                =  mb ms xs
                |  otherwise
                =  mb (x:ms) xs

-- Given a list xs :: [a] of distinct items, and a predicate
-- p :: a -> [a] -> Bool, obtain a minimal sublist ys such that
-- p x ys holds for every x in xs \\ ys.  A monotonicity condition
-- may be assumed for p: if p x ys and ys is a sublist of zs then p x zs.
-- NB The method here is "greedy": it considers successive items of
-- xs for addition to an accumulating sublist.  So the result may
-- depend on list order even though p does not.  If the choice matters,
-- the function could be generalised to give all possible results.
minSubListBy :: (a->[a]->Bool) -> [a] -> [a]
minSubListBy p  =  msl [] 
  where
  msl ms []      =  ms
  msl ms (x:xs)  |  p x (ms++xs)
                 =  msl ms xs
                 |  otherwise
                 =  msl (ms++[x]) xs

-- Is there a way to split a list xs into non-empty segments,
-- each of which satisfies a predicate p?
anySegsAll :: ([a]->Bool) -> [a] -> Bool
anySegsAll p []  =  True
anySegsAll p xs  =  p xs ||
                    or [ p xs1 && anySegsAll p xs2
                       | (xs1, xs2) <- splits xs ]

-- Is there a way to split each of two lists xs and ys into the same
-- number of non-empty segments xs1...xsn and ys1...ysn so that a
-- given binary predicate p holds for each xsi ysi?
anyPairedSegsAll p [] []  =  True
anyPairedSegsAll p xs ys  =  p xs ys ||
                             or [ p xs1 ys1 && anyPairedSegsAll p xs2 ys2
                                | (xs1, xs2) <- splits xs,
                                  (ys1, ys2) <- splits ys ]
-- dual to span, at end of list
spanEnd :: (a->Bool) -> [a] -> ([a],[a])
spanEnd p xs = foldr addElem ([],[]) xs
               where
               addElem x ([],ys) = if p x then ([],x:ys) else ([x],ys)
               addElem x (xs,ys) = (x:xs,ys)

-- concat for set-like lists, given as sorted lists without duplicates
unions :: Ord a => [[a]] -> [a]
unions = foldMerge nubMerge []

-- concat for set-like lists, when given as lists without duplicates
unionsEQ :: Eq a => [[a]] -> [a]
unionsEQ = foldr union []

-- concat for multiset-like lists, given as sorted lists
unionsMulti :: Ord a => [[a]] -> [a]
unionsMulti = foldMerge merge []

unsnoc :: [a] -> Maybe([a],a)
unsnoc xs = uns id xs where
            uns f []     = Nothing
            uns f [x]    = Just(f [],x)
            uns f (y:ys) = uns (f.(y:)) ys
