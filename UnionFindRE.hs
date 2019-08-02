module UnionFindRE where
import Expression
import Fuse
import qualified Data.Map.Strict as Map
import Data.List (minimumBy)
import Data.Maybe (fromMaybe)
import List

type UFRE = Map.Map RE RE

emptyUF :: UFRE
emptyUF = Map.empty

-- auxiliary to compute the list of all nodes that lead to a root
findL :: RE -> [RE] -> UFRE -> (RE,[RE])
findL x xs u = case Map.lookup x u of
               Nothing -> (x,xs)
               Just x' -> findL x' (x:xs) u

unionTest :: RE -> RE -> UFRE -> (RE,RE,UFRE)
unionTest x y u  =  (xn,yn,Map.union(Map.fromList [(y,zn)|y<-zs]) u)
             where
                (xn,xs)   =  findL x [] u
                (yn,ys)   =  findL y [] u
                zn  =  pickMin xn yn
                zs  =  [ yn | zn/=yn ] ++ [xn | zn/=xn] ++ xs ++ ys

unionUF :: RE -> RE -> UFRE -> UFRE
unionUF x y u  =  Map.union(Map.fromList [(y,zn)|y<-zs]) u
             where
                (xn,xs)   =  findL x [] u
                (yn,ys)   =  findL y [] u
                zn  =  pickMin xn yn
                zs  =  [ yn | zn/=yn ] ++ [xn | zn/=xn] ++ xs ++ ys

-- root lookup without path compression
rootUF :: UFRE -> RE -> RE
rootUF u x =  case Map.lookup x u of
               Nothing -> x
               Just x' -> rootUF u x'

fixUF :: UFRE -> UFRE
fixUF uf = Map.fromList al2 where
    f x  = fromMaybe x (Map.lookup x uf')
    dom = nubSort (Map.elems uf ++ Map.keys uf)
    al1 = [(x,simpl(rootUF uf x))|x<-dom]
    uf' = Map.fromList al1
    al2 = [(x,fuse y)|(x,y)<-al1]
    simpl (Alt i xs) = Alt i (map f xs)
    simpl (Cat i xs) = Cat i (map f xs)
    simpl (Rep x)    = Rep (f x)
    simpl (Opt x)    = Opt (f x)
    simpl y          = y




{- has been downgraded to pickMin, for efficiency
-- upper produces an RE that is an upper bound for both
-- inputs, and equal to both if the languages coincide
upper :: RE -> RE -> RE
--upper (Rep x) (Rep y) = normRep (upper x y)
--upper (Rep x) y       = normRep (upper x y)
--upper x       (Rep y) = normRep (upper x y)
upper x       y       = normBinAlt x y
-}

-- actually a commutative monoid, with emptyUF as mempty
mergeUF :: UFRE -> UFRE -> UFRE
mergeUF m1 m2  |  Map.size m1 <= Map.size m2
               =  addToUF m1 m2
               |  otherwise
               =  addToUF m2 m1

addToUF :: UFRE -> UFRE -> UFRE
addToUF m1 m2  = Map.foldrWithKey unionUF m2 m1





