module PreOrderTrees
  (RB, buildTree, addUniqTree, pruneTree, lookupPT, classReps, treeClasses, groupOrder, quotientMap, quotMap, sizeT) where

import List (plural)
import qualified Data.Map.Strict as M

-- red-black trees over a linear pre-order
-- labels are non-empty lists
data Color = R | B deriving (Read,Show)
data RB a = E | T Color (RB a) [a] (RB a) deriving (Read,Show)

sizeT :: RB a -> Int
sizeT E = 0
sizeT (T _ l _ r) = 1+sizeT l + sizeT r

-- rebuildTree uses a list in ascending order to build the tree,
-- so no comparisons necessary
rebuildTree :: [[a]] -> RB a
rebuildTree xss = rbt xss (length xss)
    where
    rbt [] _ = E
    rbt [xs] _ = T B E xs E
    rbt [xs,ys] _ = T B E xs (T R E ys E)
    rbt yss n = T B (rbt lss m) xs (rbt rss (n-m-1))
        where
        m = div n 2
        lss = take m yss
        (xs:rss) = drop m yss

-- remove all nodes with singleton lists
-- result is the tree without these nodes, and a list containing those elements
removeSingletons :: RB a -> ([a],RB a)
removeSingletons t =
    let (si,mss) = removeSing t [] []
    in  (si,rebuildTree mss)

removeSing :: RB a -> [a] -> [[a]]-> ([a],[[a]])
removeSing E si ns = (si,ns)
removeSing (T _ l xs r) si ns
    |  plural xs
    =  removeSing l rsi (xs:rns)
    |  otherwise
    =  removeSing l (head xs:rsi) rns
    where
    (rsi,rns) = removeSing r si ns



insert :: (a->a->Ordering) -> a -> RB a -> RB a
insert rel x s =
        T B a z b
        where
        T _ a z b = ins s
        ins E = T R E [x] E
        ins s@(T B a y@(yh:_) b) =
            case rel x yh of
                LT -> balance (ins a) y b
                GT -> balance a y (ins b)
                EQ -> T B a (x:y) b
        ins s@(T R a y@(yh:_) b) =
            case rel x yh of
                LT -> T R (ins a) y b
                GT -> T R a y (ins b)
                EQ -> T R a (x:y) b

-- do not add elements already present
insertPO :: (a->a->Ordering) -> a -> RB a -> RB a
insertPO rel x s =
        T B a z b
        where
        T _ a z b = ins s
        ins E = T R E [x] E
        ins s@(T B a y@(yh:_) b) =
            case rel x yh of
                LT -> balance (ins a) y b
                GT -> balance a y (ins b)
                EQ -> s
        ins s@(T R a y@(yh:_) b) =
            case rel x yh of
                LT -> T R (ins a) y b
                GT -> T R a y (ins b)
                EQ -> s

lookupPT :: a -> (a->a->Ordering) -> ([a]->a) -> RB a -> Maybe a
lookupPT x rel sel E = Nothing
lookupPT x rel sel (T _ le y@(yh:_) ri) =
    case rel x yh of
        LT -> lookupPT x rel sel le
        GT -> lookupPT x rel sel ri
        EQ -> Just $ sel y

lookupT  :: a -> (a->a->Ordering)-> RB a -> [a]
lookupT x rel E = []
lookupT x rel (T _ le y@(yh:_) ri) =
    case rel x yh of
        LT -> lookupT x rel le
        GT -> lookupT x rel ri
        EQ -> y

pruneTree :: ([a]->[a]) -> RB a -> RB a
pruneTree _ E = E
pruneTree f (T col l xs r) = T col (pruneTree f l) (f xs) (pruneTree f r)

showTree :: Show a => RB a -> IO ()
showTree = showTreeAtDepth 0

showTreeAtDepth :: Show a => Int -> RB a -> IO ()
showTreeAtDepth d t =  do
                         putStr $ take d (repeat ' ')
                         guts t
  where
  guts E            = putStrLn "---"
  guts (T _ l xs r) =  do
                         putStrLn (show xs)
                         showTreeAtDepth (d+1) l
                         showTreeAtDepth (d+1) r

buildTree :: (a->a->Ordering) -> [a] -> RB a
buildTree rel xs = foldl (flip $ insert rel) E xs

addUniqTree :: (a->a->Ordering) -> [a] -> RB a -> RB a
addUniqTree rel xs t = foldl (flip $ insertPO rel) t xs

buildQuotientMap :: Ord a => (a->a->Ordering) -> ([a]->a) -> [a] -> M.Map a a
buildQuotientMap rel pick xs = quotMap pick $ groupOrder rel xs

buildQuotientAL :: Ord a => (a->a->Ordering) -> ([a]->a) -> [a] -> [(a,a)]
buildQuotientAL rel pick xs = quotAssocList pick $ groupOrder rel xs

-- balance: first equation is new, to make it work with a weaker invariant
balance :: RB a -> [a] -> RB a -> RB a
balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance a x b = T B a x b

-- extracting equivalence classes from a tree
treeClasses :: RB a -> [[a]]
treeClasses t = tc t []
    where
    tc E xss = xss
    tc (T _ l xs r) xss = tc l (xs : tc r xss)

-- extracting representatives of classes from a tree
classReps :: RB a -> [a]
classReps t = cr t []
    where
    cr E xs = xs
    cr (T _ l x r) xs = cr l (head x : cr r xs)

groupOrder :: (a->a->Ordering) -> [a] -> [[a]]
groupOrder rel xs = treeClasses $ buildTree rel xs

quotMap :: Ord a => ([a]->a) -> [[a]] -> M.Map a a
quotMap selector [] = M.empty
quotMap selector (xs:xss) = M.union (M.fromList (zip xs (repeat (selector xs)))) (quotMap selector xss)

quotAssocList :: ([a]->a) -> [[a]] -> [(a,a)]
quotAssocList selector [] = []
quotAssocList selector (xs:xss) = let p = selector xs in
                                  foldr (\x ps->(x,p):ps) (quotAssocList selector xss) xs

quotientMap :: Ord a => ([a]->a) ->[[a]] -> a -> a
quotientMap selector xss = (mm M.!)
    where mm = quotMap selector xss
