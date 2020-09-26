-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module List (
   snoc, unsnoc, linkWith, plural, ordered, strictlyOrdered,
   nubMergeMap, nubMerge, foldMerge, nubSort,
   segments, segElemSuf, segsLtd, subsLtd, maxSegsLtd, maxSubsLtd,
   splits, allSplits, powerSplits, allPowerSplits, spanEnd,
   itemRest, sublists, isSublistOf,
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

-- splits a list into segments of increasing duplicate-free chains
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

-- The result of segElemSuf xs is a list of all triples (pre,x,suf)
-- such that x is an element of xs, pre is the prefix before x
-- and suf the suffix after it.
segElemSuf :: [a] -> [([a],a,[a])]
segElemSuf [] = []
segElemSuf (x:xs) = ([],x,xs) : [ (x:ys,y,zs) | (ys,y,zs)<-segElemSuf xs ]

-- Non-empty segments and sublists, limited by weight, in context.
-- *** NB *** Weights increased by one as if for "listsize". ***

segsLtd :: (a->Int) -> Int -> [a] -> [([a],[a],[a])]
segsLtd _ _ []  =  []
segsLtd w m xs  =  f True m (map w xs) xs
  where
  f _ 0 _      xs      =  []
  f _ _ _      []      =  []
  f p m (w:ws) (x:xs)  =  [ ([],[x],xs)
                          | w <= m ] ++
                          [ ([],x:pre,suf)
                          | w <  m, ([],pre,suf) <- f False (m-w-1) ws xs ] ++
                          [ (x:pre,seg,suf)
                          | p, (pre,seg,suf) <- f True m ws xs ]

subsLtd :: (a->Int) -> Int -> [a] -> [([a],[a])]
subsLtd _ _ []  =  []
subsLtd w m xs  =  f m (map w xs) xs
  where
  f 0 _      xs      =  []
  f _ _      []      =  []
  f m (w:ws) (x:xs)  =  [ ([x],xs)
                        | w <= m ] ++
                        [ (x:sub,cxt)
                        | w <  m, (sub,cxt) <- f (m-w-1) ws xs ] ++
                        [ (sub,x:cxt)
                        | (sub,cxt) <- f m ws xs ]

-- maxSegsLtd and maxSubLtd are like segsLtd and subsLtd but their
-- results include only maximal segments

maxSegsLtd :: (a->Int) -> Int -> [a] -> [([a],[a],[a])]
maxSegsLtd _ _ []  =  []
maxSegsLtd w m xs  =  map fst $ f True m (map w xs) xs
  where
  f _ 0 _      xs      =  []
  f _ _ _      []      =  []
  f p m (w:ws) (x:xs)  =  [ (([],[x],xs), w)
                          | w <= m,
                            null xs || w + head ws > m ] ++
                          [ (([],x:pre,suf), n+w+1)
                          | w <  m, (([],pre,suf), n) <- f False (m-w-1) ws xs ] ++
                          [ ((x:pre,seg,suf), n)
                          | p, ((pre,seg,suf), n) <- f True m ws xs,
                            n+w+1 > m ]

maxSubsLtd :: (a->Int) -> Int -> [a] -> [([a],[a])]
maxSubsLtd _ _ []  =  []
maxSubsLtd w m xs  =  map fst $ f m (map w xs) xs
  where
  f 0 _      xs      =  []
  f _ _      []      =  []
  f m (w:ws) (x:xs)  =  [ (([x],xs), w)
                        | w <= m,
                          all (\n -> n+w+1 > m) ws ] ++
                        [ ((x:sub,cxt), n+w+1)
                        | w <  m, ((sub,cxt), n) <- f (m-w-1) ws xs ] ++
                        [ ((sub,x:cxt),n)
                        | ((sub,cxt),n) <- f m ws xs,
                          n+w+1 > m ]

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

-- predefined in Data.List.Extra which we avoid to import
-- but this is more efficient anyway
spanEnd :: (a->Bool) -> [a] -> ([a],[a])
spanEnd p [] = ([],[])
spanEnd p (x:xs) = add (spanEnd p xs)
    where
    add ([],ys) | p x
                = ([],x:ys)
    add (ys,zs) = (x:ys,zs)
