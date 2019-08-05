module Properties where

import Data.List
import Data.Maybe
import Expression
import Info
import Context
import Comparison
import Pressing
import LazySmallCheck

-- NB. Don't bother with Emp!
instance Serial RE where
  series  =  cons0 Lam \/ {- cons1 Sym -} const (drawnFrom [Sym 'a', Sym 'b']) \/ 
             -- cons2 Alt \/ cons2 Cat \/ 
             cons1 (alt) \/ cons1 (cat) \/
             cons1 Rep \/ cons1 Opt

instance Serial Info where
  series  =  const (drawnFrom [newInfo False, newInfo True])

for :: (a->Bool) -> (a->Bool) -> a -> Bool
for k p x  =  k x ==> p x

testFor :: (Show a, Serial a) => (a -> Bool) -> (a -> Bool) -> IO ()
testFor k p =  test $ for k p

after :: (b->Bool) -> (a->b) -> a -> Bool
p `after` f  =  p . f

keeps :: (a->a) -> (a->Bool) -> a -> Bool
f `keeps` p     =  for p (p `after` f)

obeys :: (a->b) -> (a->b->Bool) -> a -> Bool
f `obeys` r  =  \x -> r x (f x)

includes :: (a->b->Bool) -> (a->b->Bool) -> (a,b) -> Bool
s `includes` r  =  \(x,y) -> r x y ==> s x y

idempotent :: Eq a => (a->a) -> a -> Bool
idempotent f  =  (f `obeys` (==)) `after` f

reflexive :: Eq a => (a->a->Bool) -> (a,a) -> Bool
reflexive r   =  r `includes` (==)

transitive :: Eq a => (a->a->Bool) -> (a,a,a) -> Bool
transitive r (x,y,z)  =  r x y && r y x ==> r x z

soundSub :: (RE->RE->Bool) -> (RE,RE) -> Bool
soundSub s    =  sublang `includes` s

soundTrans :: (RE->RE) -> RE -> Bool
soundTrans t  =  t `obeys` (===)

shrinkingUnder :: Ord a => (RE->a) -> (RE->RE) -> RE -> Bool
shrinkingUnder m t x  =  m (t x) < m x

shrinkingBy :: (RE->RE->Ordering) -> (RE->RE) -> RE -> Bool
shrinkingBy order f t = order t (f t) == GT

nonExpandingUnder :: Ord a => (RE->a) -> (RE->RE) -> RE -> Bool
nonExpandingUnder m t x  =  m (t x) <= m x

nonExpandingBy :: (RE->RE->Ordering) -> (RE->RE) -> RE -> Bool
nonExpandingBy order f t  =  order t (f t) /= LT

{-
-- Obsolete?  We no longer have Normalization and isNormal.
-- Desired properties of a Cat-neighbour commuting function c.
soundCom :: ((RE,RE)->Maybe(RE,RE)) -> (RE,RE) -> Bool
soundCom c (x,y)  =  (isNormal x && isNormal y && isJust m) ==>
                       (normCat [y',x'] === normCat [x,y])
  where
  m             =  c (x,y)
  Just (y',x')  =  m
-}

{-
-- This property is not true of commute because of the special
-- rules for "rolling" through Cat bodies of Opts and Reps.
-- But it is nearly true, and a useful test: only rollables
-- should show up as counter-examples.
selfInverseCom :: ((RE,RE) -> Maybe (RE,RE)) -> (RE,RE) -> Bool
selfInverseCom c (x,y)  =  (isPressed x && isPressed y && isJust m) ==>
                             (c (y',x') == Just (x,y))
  where
  m             =  c (x,y)
  Just (y',x')  =  m
-}

-- SMK 9/2/2016
-- checking that the ordering is a linearisation of sublang
soundLinear :: (RE->RE->Ordering) -> (RE,RE) -> Bool
soundLinear s = \(x,y) -> sublang x y `refinedBy` s x y

refinedBy :: Bool -> Ordering -> Bool
refinedBy False o = o/= EQ
refinedBy True  o = o/= GT

antiSymmetric :: (a->a->Ordering) -> (a,a) -> Bool
antiSymmetric or = \(x,y)-> dual (or x y) == or y x

dual :: Ordering -> Ordering
dual LT = GT
dual GT = LT
dual EQ = EQ

linearOrder :: (a->a->Ordering) -> (a,a,a) -> Bool
linearOrder s (x,y,z) = linearTriple (s x y)(s y z)(s x z)

linearTriple :: Ordering -> Ordering -> Ordering -> Bool
linearTriple EQ x  y  = x==y
linearTriple x  EQ y  = x==y
linearTriple LT LT y  = y==LT
linearTriple GT GT y  = y==GT
linearTriple x  y  EQ = x==dual y
linearTriple _ _ _    = True

-- end of SMK 9/2/2016




