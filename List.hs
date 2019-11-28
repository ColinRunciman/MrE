module List (
   snoc, unsnoc, linkWith, plural, ordered, strictlyOrdered, maximaBy,
   nubMergeMap, nubMerge, foldMerge, nubSort, chainSort,
   segments, segPreSuf, segElemSuf, segmentsPred, segmentsLPred, segsLtd, subsLtd,
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

merge :: Ord a => [a] -> [a] -> [a]
merge [] ys          =  ys
merge xs []          =  xs
merge (x:xs) (y:ys)  =  case compare x y of
                        LT -> x : merge xs (y:ys)
                        EQ -> x : y : merge xs ys
                        GT -> y : merge (x:xs) ys

-- f must give ordered results
nubMergeMap :: Ord b => (a -> [b]) -> [a] -> [b]
nubMergeMap f  =  unions . map f

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

mergeBy :: (a->a->Ordering) -> [a] -> [a] -> [a]
mergeBy cmp [] ys          =  ys
mergeBy cmp xs []          =  xs
mergeBy cmp (x:xs) (y:ys)  =  case cmp x y of
                           LT -> x : mergeBy cmp xs (y:ys)
                           _  -> y : mergeBy cmp (x:xs) ys

-- intersection of sorted set-like list
intersectSet :: Ord a => [a] -> [a] -> [a]
intersectSet (x:xs)(y:ys) =
    case compare x y of
        LT -> intersectSet xs (y:ys)
        EQ -> x : intersectSet xs ys
        GT -> intersectSet (x:xs) ys
intersectSet [] _  = []
intersectSet _ []  = []

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

-- splits a list-set into two parts in all possible ways such that the first part
-- is non-empty and contains only elements satisfying the predicate
powerSplitsPred :: (a->Bool) -> [a] -> [([a],[a])]
powerSplitsPred p [] = []
powerSplitsPred p (x:xs) | p x
                         = ([x],xs) : [(x:ys1,ys2)|(ys1,ys2)<-nxs] ++
                                      [(ys1,x:ys2)|(ys1,ys2)<-nxs]
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

-- Non-empty segments and sublists, limited by weight, in context.
-- *** NB *** Weights increased by one as if for "listsize". ***

segsLtd :: (a->Int) -> Int -> [a] -> [([a],[a],[a])]
segsLtd _ _ []  =  []
segsLtd w m xs  =  f True m (map w xs) xs
  where
  f _ 0 _      xs      =  []
  f _ _ _      []      =  []
  f p m (w:ws) (x:xs)  =  [ (x:pre,seg,suf)
                          | p, (pre,seg,suf) <- f True m ws xs ] ++
                          [ ([], [x], xs)
                          | w <= m ] ++
                          [ ([],x:pre,suf)
                          | w <  m, ([],pre,suf) <- f False (m-w-1) ws xs ]

subsLtd :: (a->Int) -> Int -> [a] -> [([a],[a])]
subsLtd _ _ []  =  []
subsLtd w m xs  =  f m (map w xs) xs
  where
  f 0 _      xs      =  []
  f _ _      []      =  []
  f m (w:ws) (x:xs)  =  [ (sub,x:cxt) | (sub,cxt) <- f m ws xs ] ++
                        [ ([x],xs)    | w <= m ] ++
                        [ (x:sub,cxt) | w <  m, (sub,cxt) <- f (m-w-1) ws xs ]

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

-- The result of subsetRest n xs lists all subsequences of xs of length n,
-- each paired with the corresponding residue of xs.
subsetRest :: Int -> [a] -> [([a],[a])]
subsetRest 0 xs      =  [([], xs)]
subsetRest _ []      =  []
subsetRest n (x:xs)  =  [(x:as, bs) | (as,bs) <- subsetRest (n-1) xs] ++
                        [(as, x:bs) | (as,bs) <- subsetRest n     xs]

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

-- concat for set-like lists, given as sorted lists without duplicates
unions :: Ord a => [[a]] -> [a]
unions = foldMerge nubMerge []

-- concat for set-like lists, when given as lists without duplicates
unionsEQ :: Eq a => [[a]] -> [a]
unionsEQ = foldr union []

-- concat for multiset-like lists, given as sorted lists
unionsMulti :: Ord a => [[a]] -> [a]
unionsMulti = foldMerge merge []

snoc :: [a] -> a -> [a]
snoc xs x  =  foldr (:) [x] xs

unsnoc :: [a] -> Maybe([a],a)
unsnoc xs = uns id xs where
            uns f []     = Nothing
            uns f [x]    = Just(f [],x)
            uns f (y:ys) = uns (f.(y:)) ys
