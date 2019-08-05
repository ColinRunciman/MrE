module UnionFind where

import qualified Data.Map.Strict as Map

type UF a = Map.Map a a

emptyUF :: UF a
emptyUF = Map.empty

unionTest :: Ord a => a -> a -> UF a -> (Bool,UF a)
unionTest x y u  =  (xn==yn,Map.union(Map.fromList [(y,xn)|y<-zs]) u)
             where
                (xn,xs)   =  findL x [] u
                (yn,ys)   =  findL y [] u
                zs = [ yn | xn/=yn ] ++ xs ++ ys

-- auxiliary to compute the list of all nodes that lead to a root
findL :: Ord a => a -> [a] -> UF a -> (a,[a])
findL x xs u = case Map.lookup x u of
               Nothing -> (x,xs)
               Just x' -> findL x' (x:xs) u

