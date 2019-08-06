module Properties where

import Data.List
import Data.Maybe
import Expression
import Info
import Catalogue
import Context
import Comparison
import Fuse
import Pressing
import Sanify
import Stellation
import StarPromotion
import SyntaxCatalogue
-- import LazySmallCheck
import Test.LeanCheck

{- These instances were for Lazy SmallCheck

-- NB. Don't bother with Emp!
instance Serial RE where
  series  =  cons0 Lam \/ const (drawnFrom [Sym 'a', Sym 'b']) \/ 
             -- cons2 Alt \/ cons2 Cat \/ 
             cons1 (alt) \/ cons1 (cat) \/
             cons1 Rep \/ cons1 Opt

instance Serial Info where
  series  =  const (drawnFrom [newInfo False, newInfo True])
-}

instance Listable RE where
  tiers  =  cons0 Lam \/
            [[Sym 'a'], [Sym 'b'], [Sym 'c']] \/
            cons1 alt \/ cons1 cat \/
            cons1 Rep \/ cons1 Opt

for :: (a->Bool) -> (a->Bool) -> a -> Bool
for k p x  =  k x ==> p x

{- clashes with useful but differently typed function from LeanCheck

checkFor :: (Show a, Listable a) => (a -> Bool) -> (a -> Bool) -> IO ()
checkFor k p =  check $ for k p
-}

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
soundTrans t  =  t `obeys` equiv
  where
  equiv x y  =  sanify x === sanify y

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

-- The transformations used by MrE are sound and non-expanding.

soundMrE :: RE -> Bool
soundMrE x  =  and [soundTrans kataGrade x,
                    soundTrans fuse x,
                    soundTrans promote x,
                    soundTrans (stellate . promote) x,
                    soundTrans (catalogue . promote) x,
                    soundTrans (press . promote) x,
                    soundTrans syncat x]


