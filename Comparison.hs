module Comparison (
  (===), (<<==), (====), istransitive, eqr, subExpr, strictSubExpr,
  sublang, compRE, (&&&), sizeOrder, pickMin, pickMinList ) where

import Data.Maybe
import Data.Bits
import Data.List (sortBy,(\\),minimumBy)
import qualified Data.Set as S
import qualified Data.Map.Strict as Map
import Data.Monoid (mappend)
import Function
import List
import Expression
import Info
import Fuse
import Alphabet
import Queue
import Derivative

-- This module defines various comparison functions over regular expressions
-- or their languages.  

(&&&) :: Ordering -> Ordering -> Ordering
(&&&) = mappend

-- comparing on ewp and firsts alone
basicOrd :: RE -> RE -> Ordering
basicOrd x y = compare (ewp x) (ewp y) &&& compare (fir x)(fir y)

basicLEQ :: RE -> RE -> Bool
basicLEQ x y = basicOrd x y /= GT

-- size-based ordering and selection

sizeOrder :: RE -> RE  -> Ordering
sizeOrder x y = compare (size x)(size y) &&& compare x y

pickMin :: RE -> RE -> RE
pickMin x y = minimumBy sizeOrder [x,y]

pickMinList :: [RE] -> RE
pickMinList xs = minimumBy sizeOrder xs

-- Tests for syntactic subexpressions (reflexive and irreflexive).

subExpr :: RE -> RE -> Bool
subExpr x y            =  x == y || strictSubExpr x y

strictSubExpr :: RE -> RE -> Bool
strictSubExpr x (Alt _ ys)  =  any (subExpr x) ys ||
                               or [ x == mkAlt ys'
                                  | ys' <- sublists ys, ys' /= ys, length ys' > 1 ]
strictSubExpr x (Cat _ ys)  =  any (subExpr x) ys ||
                               or [ x == mkCat ys' 
                                  | ys' <- segments ys, ys' /= ys, length ys' > 1 ]
strictSubExpr x (Rep y)     =  subExpr x y
strictSubExpr x (Opt y)     =  subExpr x y
strictSubExpr x y           =  False

-- SUBLANGUAGE TEST

-- The sublang function tests for a subset relation between the languages of
-- two regular expressions.  It is heavily used in some transformation modules.
-- It works by building up a set of <= assumptions, re-using them in recursive tests.

type Hypothesis = S.Set(RE,RE)

assumed :: Hypothesis -> RE -> RE -> Bool
assumed hyp x y  =  S.member (x,y) hyp

addAssumption :: Hypothesis -> RE -> RE -> Hypothesis
addAssumption hyp re re2 = S.insert (re,re2) hyp

sublang :: RE -> RE -> Bool
sublang Emp x           =  True
sublang Lam x           =  ewp x
sublang x   y           =  isJust $ sublaHyp1 S.empty x y

-- first RE will never be Emp, second could be 
sublaHyp1 :: Hypothesis -> RE -> RE -> Maybe Hypothesis
sublaHyp1 _ x          Emp         =  Nothing
sublaHyp1 _ x          y           |  ewp x && not(ewp y)
                                   =  Nothing
-- In all the following cases we know ewp (1st arg) ==> ewp (2nd arg).
sublaHyp1 h Lam        x           =  Just h
sublaHyp1 _ _          Lam         =  Nothing
sublaHyp1 h (Sym x)    y           =  justIf (x `elemAlpha` swa y) h
sublaHyp1 _ _          (Sym z)     =  Nothing
sublaHyp1 h (Opt x)    y           =  sublaHyp1 h x y
sublaHyp1 h (Alt _ xs) y           =  sublaHypAlts xs y h
sublaHyp1 h x          (Rep  y)    |  ewp x
                                   =  sublaHypAlts (nubSort $ whiteAltList x) (Rep y) h
sublaHyp1 h x          y           =  assumedM h x y `mplus` sublaHyp2 (addAssumption h x y) x y

mplus Nothing x = x
mplus x       _ = x

assumedM h x y | assumed h x y = Just h
               | otherwise     = Nothing

-- This is a foldM but has an application-specific name.
sublaHypAlts []     _ h = Just h
sublaHypAlts (x:xs) y h = sublaHyp1 h x y >>= sublaHypAlts xs y

-- subla2Hyp passes assumptions on, but does not use them itself.
-- It decomposes complex cases into either simpler cases,
-- or cases the hypothesis should eventually cover.
-- By this stage the possible forms of the second argment are limited.

sublaHyp2 :: Hypothesis -> RE -> RE -> Maybe Hypothesis
sublaHyp2 h x@(Rep (Cat b xs))     y  =  sublaHyp1 h (mkCat (xs ++ [x])) y
sublaHyp2 h (Rep x)                y  =  sublaHyp1 h (mkCat [x,Rep x]) y
sublaHyp2 h (Cat _ (Sym c:rs))     y  =  sublaHyp1 h (mkCat rs) (derive c y)
sublaHyp2 h (Cat _ (Alt _ xs:rs))  y  =  let tl=mkCat rs in
                                               sublaHypAlts [cat [x, tl] | x<-xs ] y h
sublaHyp2 h (Cat _ (Opt x:rs))     y  =  let tl=mkCat rs in
                                              sublaHyp1 h tl y >>= 
                                              \h' -> sublaHyp1 h' (cat [x, tl]) y
sublaHyp2 h inp@(Cat _ (Rep x:rs)) y  =  sublaHyp1 h (mkCat rs) y >>=
                                           \h' -> sublaHyp1 h' (cat [x, inp]) y
sublaHyp2 h x                      y  =  error (show x ++ " in sublaHyp2 ")

-- The compRE function is a language-based linear ordering of REs.
-- It makes distinctions beyond those of sublang, but it is an
-- extension of it.  It is useful as:
-- (i) a quicker equality test than double application of sublang;
-- (ii) a better Poset Ordering for catalogue trees.

(===) :: RE -> RE -> Bool
x === y  =  compRE x y == EQ

istransitive :: RE -> Bool
istransitive x = opt x === rep x

compRE :: RE -> RE -> Ordering
compRE x y = solveGoals ido (makeGoal x y) emptyHyp

compREinUF :: UFRE -> RE -> RE -> UFOrdering
compREinUF uf x y = solveGoals ufo (makeGoal x y) uf

type EqHyp = UFRE

emptyHyp :: EqHyp
emptyHyp = emptyUF

type Goals = Queue (RE,RE)

makeGoal :: RE -> RE -> Goals
makeGoal x y = singletonQ (x,y)

makeGoals :: [RE] -> Goals
makeGoals xs = list2Q (linkWith (,) xs)

data UFOrdering  =  UFO Ordering UFRE

class OrdRE a where
  result :: a -> Ordering -> Goals -> EqHyp -> a
  success :: a -> EqHyp -> a

instance OrdRE Ordering where
  result  _ ord _ _  =  ord
  success _ _        =  EQ

instance OrdRE UFOrdering where
  result  _ ord _ _  =  UFO ord emptyUF
  success _ uf       =  UFO EQ uf

ido :: Ordering
ido  =  undefined

ufo :: UFOrdering
ufo  =  undefined

-- Each goal is a pair of expressions that needs to be proved equal.
-- If one fails then the whole comparison fails with the same result.

solveGoals :: OrdRE a => a -> Goals -> EqHyp -> a
solveGoals o gs = maybe (success o) (uncurry $ compREHyp1 o) (pollQM gs)

orderSelect :: OrdRE a => a -> Ordering -> (Goals -> EqHyp -> a) -> Goals -> EqHyp -> a
orderSelect _ EQ continuation = continuation
orderSelect o ot _            = result o ot

-- compREHyp1 o p gs e checks the goal p as follows.
-- (1) If the languages of p are elementarily different that difference is the result.
-- (2) If they are clearly the same the goal is dismissed and the remaining goals are checked.
-- (3) If p is found in e then the goal is dismissed.
-- (4) Otherwise the derivatives of p are added to the queue of goals to be solved.

compREHyp1 :: OrdRE a => a -> (RE,RE) -> Goals -> EqHyp -> a
compREHyp1 o (Emp,Emp)     =  solveGoals o
compREHyp1 o (Emp,_)       =  result o LT
compREHyp1 o (_  ,Emp)     =  result o GT
compREHyp1 o (Lam,Lam)     =  solveGoals o
compREHyp1 o (Lam,x)       =  result o $ if ewp x then LT else GT
compREHyp1 o (x,Lam)       =  result o $ if ewp x then GT else LT                  
compREHyp1 o (Sym c,Sym d) =  orderSelect o (compare c d) (solveGoals o)
compREHyp1 o (Opt x,Opt y) =  compREHyp1 o (x,y)
compREHyp1 o (x,y)         =  orderSelect o (basicOrd x y) (compREHyp2n o (alpha2String $ fir x) x y)

compREHyp2n o fir x y goals hyp
    |  xn==yn
    =  solveGoals o goals hyp'
    |  otherwise
    =  solveGoals o (enterListQ (map (\c ->(derive c x,derive c y)) fir) goals) hyp'
       where
       (xn,yn,hyp')  =  unionTest x y hyp

-- The eqr function compares two REs and if they are equivalent returns a smallest one.

eqr :: RE -> RE -> Maybe RE
eqr x y  =  justIf (x === y) (pickMin x y)

-- Using eqrList is more efficient than pair-wise comparison of consecutive
-- items, because (i) the hypothesis is shared and (ii) the UF structure picks
-- the minimum, possibly even smaller than any RE in list.

eqrList :: [RE] -> Maybe RE
eqrList xs = justIf (rel==EQ) (rootUF uf (head xs))
             where UFO rel uf = solveGoals ufo (makeGoals xs) emptyHyp

-- safe sublang, and lang
(<<==) :: RE -> RE -> Bool
x <<== y = validate x `sublang` validate y

(====) :: RE -> RE -> Bool
x ==== y = validate x === validate y

-- Union Find

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

-- actually a commutative monoid, with emptyUF as mempty
mergeUF :: UFRE -> UFRE -> UFRE
mergeUF m1 m2  |  Map.size m1 <= Map.size m2
               =  addToUF m1 m2
               |  otherwise
               =  addToUF m2 m1

addToUF :: UFRE -> UFRE -> UFRE
addToUF m1 m2  = Map.foldrWithKey unionUF m2 m1

