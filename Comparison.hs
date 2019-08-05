module Comparison where

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
-- import Data.Map.Strict ((!))
-- import qualified Data.Map.Strict as Map
import Queue
import RegexpMemo
import Derivative

-- syntactic well-founded order on REs
smallerComp :: RE -> RE -> Ordering
smallerComp x y = compare (size x) (size y) &&& smallerComp2 x y

-- only to be used when x and y have equal size
smallerComp2 x y = rootCompare x y &&& lexComp x y

lexComp Emp Emp = EQ
lexComp Lam Lam = EQ
lexComp (Sym c) (Sym d) = compare c d
lexComp (Alt _ xs) (Alt _ ys) = altListComp (sortBy smallerComp xs)(sortBy smallerComp ys)
lexComp (Cat i1 xs) (Cat i2 ys)
     | ew i1 && not (ew i2) = LT
     | ew i2 && not (ew i1) = GT
     | otherwise    = compare xs ys
lexComp (Rep x) (Rep y) = smallerComp2 x y
lexComp (Opt x) (Opt y) = smallerComp2 x y

altListComp [] [] = EQ
altListComp [] _  = GT -- favour longer lists when overall size is the same
altListComp _ []  = LT
altListComp (x:xs) (y:ys) =
    smallerComp x y &&& altListComp xs ys

rootCompare Emp Emp = EQ
rootCompare Emp x   = LT
rootCompare _ Emp   = GT
rootCompare Lam Lam = EQ
rootCompare Lam _   = LT
rootCompare _ Lam   = GT
rootCompare (Sym _) (Sym _) = EQ
rootCompare (Sym _) _       = LT
rootCompare _ (Sym _)       = GT
rootCompare (Rep _) (Rep _) = EQ
rootCompare (Rep _) _       = LT
rootCompare _ (Rep _)       = GT
rootCompare (Cat _ xs) (Cat _ ys) = EQ
rootCompare (Cat _ _) _ = LT
rootCompare _ (Cat _ _) = GT
rootCompare (Alt _ xs) (Alt _ ys) = compare (length ys)(length xs)
rootCompare (Alt _ _) _ = LT
rootCompare _ (Alt _ _) = GT
rootCompare (Opt _) (Opt _) = EQ

-- listCompare is an ordering on set-like lists (ordered, dup-free) that could be used
-- as a linear order on those sets, which moreover is a refinement (linearisation)
-- of the subset relationship
-- if we do not care about that compatibility ordinary 'compare' would suffice
-- the reason for the flipped 'compare y x' in the last line is that an LT indicates
-- that x is present in the first set, but not the second;
-- so the sets differ and the first set could be a superset of the second
listCompare :: Ord a => [a] -> [a] -> Ordering
listCompare [] []        = EQ
listCompare [] (_:_)     = LT
listCompare (_:_) []     = GT
listCompare (x:xs)(y:ys) = compare y x &&& listCompare xs ys

-- comparing on ewp and firsts alone
basicOrd :: RE -> RE -> Ordering
-- basicOrd x y = compare (ewp x) (ewp y) &&& listCompare (fir x)(fir y)
basicOrd x y = compare (ewp x) (ewp y) &&& setOrder (fir x)(fir y)

basicLEQ :: RE -> RE -> Bool
basicLEQ x y = basicOrd x y /= GT

-- TESTS FOR SYNTACTIC SUBEXPRESSIONS (REFLEXIVE AND IRREFLEXIVE)

subExpr :: RE -> RE -> Bool
subExpr x y            =  x == y || subExpr' x y

subExpr' :: RE -> RE -> Bool
subExpr' x (Alt _ ys)  =  any (subExpr x) ys ||
                          or [ x == mkAlt ys'
                             | ys' <- sublists ys, ys' /= ys, length ys' > 1 ]
subExpr' x (Cat _ ys)  =  any (subExpr x) ys ||
                          or [ x == mkCat ys' 
                             | ys' <- segments ys, ys' /= ys, length ys' > 1 ]
subExpr' x (Rep y)     =  subExpr x y
subExpr' x (Opt y)     =  subExpr x y
subExpr' x y           =  False

-- SUBLANGUAGE TEST

-- Builds up more and more assumptions, re-using them in other branches.

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
sublaHyp1 _ x          y           |  ewp x && not(ewp y)--so we can remove these concerns from remaining cases
                                   =  Nothing
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

-- this is really a foldM
sublaHypAlts []     _ h = Just h
sublaHypAlts (x:xs) y h = sublaHyp1 h x y >>= sublaHypAlts xs y

-- subla2Hyp passes the assumption on, but does not use it
-- second arg is setArgSSNF, not a symbol either
-- the hypothesis will already contain (2nd,3rd)
-- it decomposes complex cases into either simpler cases,
-- or cases the hypothesis should eventually cover
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

-- SEMANTIC LINEAR ORDERING OF RES

-- Gives LT and GT more often than comparison using sublanguage
-- tests, but EQ in the same cases.
-- only to be used on FuseRE
-- double purpose:
-- (i) a quicker equality test than double application of sublang 
-- (ii) a better Poset Ordering for catalogue trees
-- however, a dedicated equality test might do better
-- note that we cannot do the white-trick here

(===) :: RE -> RE -> Bool
x === y  =  compEQ x y
            -- ? compEQ (normalize x) (normalize y)
            -- x `sublang` y && y `sublang` x
{-
  where
  x'  =  normalize x
  y'  =  normalize y
-}

-- new version of compRE
compRE :: RE -> RE -> Ordering
compRE x y = solveGoals (makeGoal x y) emptyHyp

compEQ :: RE -> RE -> Bool
compEQ x y = compRE x y == EQ

compREinUF :: UFRE -> RE -> RE -> (Ordering,UFRE)
compREinUF uf x y = solveGoalsUF (makeGoal x y) uf

compREDer :: Derivation -> RE -> RE -> Ordering
compREDer der x y = solveGoalsDer der (makeGoal x y) emptyHyp

-- alternative sublang
-- subEQ :: RE -> RE -> Bool
-- subEQ a b = compREn (normBinAlt a b) b == EQ

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

{- solveGoals tries to prove all the goals (to be equal) in order     -}
{- if one fails then the whole thing fails with the same result       -}
{- the EqHyp represents goals that -- should they fail -- should fail -}
{- with the already queued ones                                       -}
solveGoals :: Goals -> EqHyp -> Ordering
solveGoals gs = maybe success (uncurry compREHyp1) (pollQM gs)

solveGoalsDer :: Derivation -> Goals -> EqHyp -> Ordering
solveGoalsDer der gs = maybe success (uncurry (compREHyp1Der der)) (pollQM gs)

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
compREHyp1 (Sym c,Sym d) =  orderSelect (compare d c) solveGoals
compREHyp1 (Opt x,Opt y) =  compREHyp1 (x,y)
compREHyp1 (x,y)         =  orderSelect (basicOrd x y) (compREHyp2n (enumerateSet $ fir x) x y)

compREHyp1Der :: Derivation -> (RE,RE) -> Goals -> EqHyp -> Ordering
compREHyp1Der d (Emp,Emp)     =  solveGoalsDer d
compREHyp1Der _ (Emp,_)       =  result LT
compREHyp1Der _ (_  ,Emp)     =  result GT
compREHyp1Der d (Lam,Lam)     =  solveGoalsDer d
compREHyp1Der _ (Lam,x)       =  result $ if ewp x then LT else GT
compREHyp1Der _ (x,Lam)       =  result $ if ewp x then GT else LT                  
compREHyp1Der n (Sym c,Sym d) =  orderSelect (compare d c) (solveGoalsDer n)
compREHyp1Der d (Opt x,Opt y) =  compREHyp1Der d (x,y)
compREHyp1Der d (x,y)         =  orderSelect (basicOrd x y) (compREHyp2nDer d (enumerateSet $ fir x) x y)

compREHyp1UF :: (RE,RE) -> Goals -> EqHyp -> UFOrdering
compREHyp1UF (Emp,Emp)     =  solveGoalsUF
compREHyp1UF (Emp,_)       =  resultUF LT
compREHyp1UF (_  ,Emp)     =  resultUF GT
compREHyp1UF (Lam,Lam)     =  solveGoalsUF
compREHyp1UF (Lam,x)       =  resultUF $ if ewp x then LT else GT
compREHyp1UF (x,Lam)       =  resultUF $ if ewp x then GT else LT                  
compREHyp1UF (Sym c,Sym d) =  orderSelectUF (compare d c) solveGoalsUF
compREHyp1UF (Opt x,Opt y) =  compREHyp1UF (x,y)
compREHyp1UF (x,y)         =  orderSelectUF (basicOrd x y) (compREHyp2nUF (enumerateSet $ fir x) x y)

-- instead of continuing with x and y, we could continue
-- with xn and yn
compREHyp2n fir x y goals hyp
    |  xn==yn
    =  solveGoals goals hyp'
    |  otherwise
    =  solveGoals (enterListQ (map (\c ->(derive c x,derive c y)) fir) goals) hyp'
       where
       (xn,yn,hyp')  =  unionTest x y hyp

compREHyp2nDer d fir x y goals hyp
    |  xn==yn
    =  solveGoalsDer d goals hyp'
    |  otherwise
    =  solveGoalsDer d (enterListQ (map (\c ->let dv=deriv d c in (dv x,dv y)) fir) goals) hyp'
       where
       (xn,yn,hyp')  =  unionTest x y hyp

compREHyp2nUF fir x y goals hyp
    |  xn==yn
    =  solveGoalsUF goals hyp'
    |  otherwise
    =  solveGoalsUF (enterListQ (map (\c ->(derive c x,derive c y)) fir) goals) hyp'
       where
       (xn,yn,hyp')  =  unionTest x y hyp

{- This is now done by Derivative module
derive :: Char -> FuseRE -> FuseRE
derive c Lam             =  Emp
derive c Emp             =  Emp
derive c (Sym d)         =  if c==d then Lam else Emp
derive c (Rep re)        =  fuseCat [derive c re, Rep re]
derive c (Opt re)        =  derive c re
derive c (Alt _ xs)      =  fuseAlt [derive c x | x<-xs]
derive c (Cat _ (x:xs))  |  ewp x
                         =  fuseAlt [dx,dxs]
                         |  otherwise
                         =  dx
                         where  dx   =  fuseCat (derive c x : xs)
                                dxs  =  derive c (mkCat xs)

-- derivation from the end
evired :: FuseRE -> Char -> FuseRE
evired Lam c            =  Emp
evired Emp c            =  Emp
evired (Sym d) c        =  if c==d then Lam else Emp
evired (Rep re) c       =  fuseCat [Rep re, evired re c]
evired (Opt re) c       =  evired re c
evired (Alt _ xs) c     =  fuseAlt [evired x c | x<-xs]
evired (Cat _ xs) c     =  unsnocF aux xs
                           where  
                           aux ys y | ewp y
                                    = fuseAlt [dy,dys]
                                    | otherwise
                                    = dy
                                      where
                                      dy  = fuseCat (ys ++ [evired y c])
                                      dys = evired (mkCat ys) c

unsnocF :: ([a]->a->b) -> [a] -> b
unsnocF cont [x] = cont [] x
unsnocF cont (x:xs) = unsnocF (\ys y->cont (x:ys) y) xs
-}

-- really a list utility, for sorted lists
listOrder :: Ord a => [a] -> [a] -> Bool
listOrder [] _      = True
listOrder (x:xs) [] = False
listOrder (x:xs) (y:ys) =
    case compare x y of
        LT -> False
        EQ -> listOrder xs ys
        GT -> listOrder (x:xs) ys
{-
OBSOLETE
firstCheck :: RE->RE->Bool
--lastCheck,endCheck :: RE -> RE -> Bool
-- firstCheck r1 r2 = fir r1 `listOrder` fir r2
firstCheck r1 r2 = fir r1 `setOrder` fir r2
--lastCheck r1 r2 = lasts r1 `listOrder` lasts r2
--endCheck r1 r2 = firstCheck r1 r2 && lastCheck r1 r2
-}

sub :: RE -> RE -> Bool
sub x y = sublang x y

-- preserves property for stronger than FuseRE
-- eqr gives a tentative representative of the equivalence class
eqr :: FuseRE -> FuseRE -> Maybe FuseRE
eqr x y  =  justIf (compEQ x y) (pickMin x y)

equivMin :: FuseRE -> FuseRE -> (Bool,FuseRE)
equivMin x y  =  (isJust m, fromJust m)
              where  m  =  eqr x y


-- this should be more efficient, because
-- (i)  it uses compRE technology
-- (ii) the hypothesis is shared
-- (iii) the UF structure picks the minimum, possibly even smaller than any RE in list
eqrList :: [FuseRE] -> Maybe FuseRE
eqrList xs = justIf (rel==EQ) (rootUF uf (head xs))
             where (rel,uf) = solveGoalsUF (makeGoals xs) emptyHyp


eqv :: FuseRE -> FuseRE -> Bool
-- eqv  =  compEQ
eqv x y = isJust $ eqr x y

-- is x===alpha*?
sigmaStarTest :: RE -> Bool
sigmaStarTest x = stt [x] S.empty
                  where
                  sig = charSet $ alpha x
                  siglist = enumerateSet sig
                  stt [] _ = True
                  stt (y:ys) ss | S.member y ss
                                = stt ys ss
                                | not(ewp y) || fir y/=sig
                                = False
                                | otherwise
                                = stt ([derive c y|c<-siglist]++ys) (S.insert y ss)


