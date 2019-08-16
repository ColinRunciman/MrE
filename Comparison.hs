module Comparison (
  (===), (<<==), (====), eqr, eqv, subExpr, strictSubExpr, sublang, compRE ) where

import Function
import List
import Expression
import Info
import Fuse
import Data.List (sortBy,(\\))
import UnionFindRE
import qualified Data.Set as S
import Data.Maybe
import Data.Bits
import Alphabet
import Queue
import Derivative

-- This module defines various comparison functions over regular expressions
-- or their languages.  

-- comparing on ewp and firsts alone
basicOrd :: RE -> RE -> Ordering
basicOrd x y = compare (ewp x) (ewp y) &&& compare (fir x)(fir y)

basicLEQ :: RE -> RE -> Bool
basicLEQ x y = basicOrd x y /= GT

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
sublaHyp1 h (Sym x)    y           =  justIf (swp x y) h
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
                                               sublaHypAlts [fuseBinCat x tl | x<-xs ] y h
sublaHyp2 h (Cat _ (Opt x:rs))     y  =  let tl=mkCat rs in
                                              sublaHyp1 h tl y >>= 
                                              \h' -> sublaHyp1 h' (fuseBinCat x tl) y
sublaHyp2 h inp@(Cat _ (Rep x:rs)) y  =  sublaHyp1 h (mkCat rs) y >>=
                                           \h' -> sublaHyp1 h' (fuseBinCat x inp) y
sublaHyp2 h x                      y  =  error (show x ++ " in sublaHyp2 ")

-- The compRE function is a language-based linear ordering of REs.
-- It makes distinctions beyond those of sublang, but it is an
-- extension of it.  It is useful as:
-- (i) a quicker equality test than double application of sublang;
-- (ii) a better Poset Ordering for catalogue trees.

(===) :: RE -> RE -> Bool
x === y  =  compRE x y == EQ

compRE :: RE -> RE -> Ordering
compRE x y = solveGoals (makeGoal x y) emptyHyp

compREinUF :: UFRE -> RE -> RE -> (Ordering,UFRE)
compREinUF uf x y = solveGoalsUF (makeGoal x y) uf

type EqHyp = UFRE

emptyHyp :: EqHyp
emptyHyp = emptyUF

type Goals = Queue (RE,RE)

makeGoal :: RE -> RE -> Goals
makeGoal x y = singletonQ (x,y)

makeGoals :: [RE] -> Goals
makeGoals xs = list2Q (linkWith (,) xs)

success :: EqHyp -> Ordering
success _ = EQ

successUF :: EqHyp -> UFOrdering
successUF uf = (EQ,uf)

-- Each goal is a pair of expressions that needs to be proved equal.
-- If one fails then the whole comparison fails with the same result.

solveGoals :: Goals -> EqHyp -> Ordering
solveGoals gs = maybe success (uncurry compREHyp1) (pollQM gs)

type UFOrdering = (Ordering,UFRE)

{- retains the UF structure -}
solveGoalsUF :: Goals -> EqHyp -> UFOrdering
solveGoalsUF gs = maybe successUF (uncurry compREHyp1UF) (pollQM gs)

{- the 'return' of some function space monad, but non-monadic notation -}
result :: Ordering -> Goals -> EqHyp -> Ordering
result ord goals hyp = ord

{- returns emptyUF, because the process failed, so the current UF needs to be wiped -}
resultUF :: Ordering -> Goals -> EqHyp -> UFOrdering
resultUF ord goals hyp = (ord,emptyUF)

orderSelect :: Ordering -> (Goals -> EqHyp -> Ordering) -> Goals -> EqHyp -> Ordering
orderSelect EQ continuation = continuation
orderSelect ot _            = result ot

orderSelectUF :: Ordering -> (Goals -> EqHyp -> UFOrdering) -> Goals -> EqHyp -> UFOrdering
orderSelectUF EQ continuation = continuation
orderSelectUF ot _            = resultUF ot

-- compREHyp1 p gs e checks the goal p
-- if the languages of p are elementarily different that difference is the result
-- if they are clearly the same the goal is dismissed and the remaining goals are checked
-- if p is found in e then the goal is dimissed and...
-- otherwise the derivatives of p are computed, added to the queue of goals,
-- which is then solved

compREHyp1 :: (RE,RE) -> Goals -> EqHyp -> Ordering
compREHyp1 (Emp,Emp)     =  solveGoals
compREHyp1 (Emp,_)       =  result LT
compREHyp1 (_  ,Emp)     =  result GT
compREHyp1 (Lam,Lam)     =  solveGoals
compREHyp1 (Lam,x)       =  result $ if ewp x then LT else GT
compREHyp1 (x,Lam)       =  result $ if ewp x then GT else LT                  
compREHyp1 (Sym c,Sym d) =  orderSelect (compare c d) solveGoals
compREHyp1 (Opt x,Opt y) =  compREHyp1 (x,y)
compREHyp1 (x,y)         =  orderSelect (basicOrd x y) (compREHyp2n (alpha2String $ fir x) x y)

compREHyp1UF :: (RE,RE) -> Goals -> EqHyp -> UFOrdering
compREHyp1UF (Emp,Emp)     =  solveGoalsUF
compREHyp1UF (Emp,_)       =  resultUF LT
compREHyp1UF (_  ,Emp)     =  resultUF GT
compREHyp1UF (Lam,Lam)     =  solveGoalsUF
compREHyp1UF (Lam,x)       =  resultUF $ if ewp x then LT else GT
compREHyp1UF (x,Lam)       =  resultUF $ if ewp x then GT else LT                  
compREHyp1UF (Sym c,Sym d) =  orderSelectUF (compare c d) solveGoalsUF
compREHyp1UF (Opt x,Opt y) =  compREHyp1UF (x,y)
compREHyp1UF (x,y)         =  orderSelectUF (basicOrd x y) (compREHyp2nUF (alpha2String $ fir x) x y)

compREHyp2n fir x y goals hyp
    |  xn==yn
    =  solveGoals goals hyp'
    |  otherwise
    =  solveGoals (enterListQ (map (\c ->(derive c x,derive c y)) fir) goals) hyp'
       where
       (xn,yn,hyp')  =  unionTest x y hyp

compREHyp2nUF fir x y goals hyp
    |  xn==yn
    =  solveGoalsUF goals hyp'
    |  otherwise
    =  solveGoalsUF (enterListQ (map (\c ->(derive c x,derive c y)) fir) goals) hyp'
       where
       (xn,yn,hyp')  =  unionTest x y hyp

-- The eqr function compares two REs and if they are equivalent returns a smallest one.

eqr :: RE -> RE -> Maybe RE
eqr x y  =  justIf (x === y) (pickMin x y)

equivMin :: RE -> RE -> (Bool,RE)
equivMin x y  =  (isJust m, fromJust m)
              where  m  =  eqr x y

-- Using eqrList is more efficient than pair-wise comparison of consecutive
-- items, because (i) the hypothesis is shared and (ii) the UF structure picks
-- the minimum, possibly even smaller than any RE in list.

eqrList :: [RE] -> Maybe RE
eqrList xs = justIf (rel==EQ) (rootUF uf (head xs))
             where (rel,uf) = solveGoalsUF (makeGoals xs) emptyHyp

eqv :: RE -> RE -> Bool
eqv x y = isJust $ eqr x y

-- safe sublang, and lang
(<<==) :: RE -> RE -> Bool
x <<== y = validate x `sublang` validate y

(====) :: RE -> RE -> Bool
x ==== y = validate x === validate y

