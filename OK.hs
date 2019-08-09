module OK where
-- computations of type a
-- True tag: something noteworthy has happened
-- False tag: nothing noteworthy has happened

import Data.Functor.Classes

data OK t = OK { valOf :: t, hasChanged :: Bool } 

instance Show1 OK where
    showsPrec1 n oka = showsPrec n (valOf oka) . (c:)
        where c = if hasChanged oka then '!' else '.'

instance Show a => Show (OK a)
    where showsPrec = showsPrec1


mkOK :: t -> Bool -> OK t
mkOK t x = OK { valOf=t, hasChanged=x }

unsafeChanged :: OK t -> OK t
unsafeChanged x = x { hasChanged = True }

instance Functor OK where
    fmap f val = val { valOf = f $ valOf val }

okmap :: (a->b) -> (OK a -> OK b)
okmap = fmap

instance Applicative OK where
    pure               =  unchanged
    f <*> a            =  mkOK (valOf f $ valOf a) (hasChanged f || hasChanged a)
    a *> b             =  mkOK (valOf b) (hasChanged a || hasChanged b)
    a <* b             =  b *> a

okmap2 :: (a->b->c) -> (OK a -> OK b -> OK c)
okmap2 binOp c1 c2 = mkOK (binOp (valOf c1)(valOf c2)) (hasChanged c1||hasChanged c2)


instance Monad OK where
    a >>= f = app f a

-- >>=, but with args swapped
app :: (a -> OK b) -> OK a -> OK b
app f oka  = oka *> f (valOf oka)

-- unchanged is the unit of the Kleisli composition of the OK monad
unchanged :: a -> OK a
unchanged x = mkOK x False

changed :: a -> OK a
changed x = mkOK x True

-- we computed on x, received y
-- has it changed?
updateEQ :: Eq a => a -> a -> OK a
updateEQ x y = mkOK y (x/=y)

-- instead of built-in equivalence provide a relation
updateEQby :: (a->a->Bool) -> a -> a -> OK a
updateEQby rel x y = mkOK y (rel x y)

ifchanged :: OK a -> (a -> OK b) -> (a -> OK b) -> OK b
ifchanged oka f g = app (if hasChanged oka then f else g) oka

appch :: (a -> OK a) -> (OK a -> OK a)
appch f x = ifchanged x f unchanged

-- Kleisli-composition, in function application order
aft :: (b -> OK c) -> (a -> OK b) -> a -> OK c
aft f g  =  \x -> f `app` g x

aftch :: (a -> OK a) -> (a -> OK a) -> a -> OK a
aftch f g  =  \x -> f `appch` g x

-- abandon calls not satisfying the relation
chapp :: (a->a-> Bool) -> (a -> OK a) -> (a -> OK a)
chapp p f x = if p x (valOf call) then call else unchanged x where call = f x

okmapIf :: (a->a) -> (OK a -> OK a)
okmapIf f oka = if hasChanged oka then changed (f (valOf oka)) else oka

single :: OK a -> OK [a]
single = okmap (:[])

-- mplus for OK type
-- this has no unit, hence more a semigroup than a monoid
orOK :: OK a -> OK a -> OK a
orOK a b = if hasChanged a then a else b

guardOK :: Bool -> OK a -> OK a -> OK a
guardOK False _ x  = x
guardOK True th el = orOK th el

guardApply :: Bool -> (a->a) -> a -> OK a
guardApply b f x = if b then changed (f x) else unchanged x

guardMap :: Bool -> (a->a) -> OK a -> OK a
guardMap b f x = if b then okmap f x else x

-- if predicate is True, flag a change regardless; no need to evaluate it if change has been flagged anyway
potentialChange :: (a->Bool) -> OK a -> OK a
potentialChange p x = mkOK vx (hasChanged x || p vx) where vx=valOf x


--not used any more
concatMapOK :: (a -> OK [b]) -> [a] -> OK [b]
concatMapOK f [] = unchanged []
concatMapOK f (x:xs) =
    do
        fx <- f x
        nxs <- concatMapOK f xs
        return (fx ++ nxs)

-- useful in combination with list comprehensions
list2OK :: a -> [a] -> OK a
list2OK x []    = unchanged x
list2OK _ (x:_) = changed x

-- not used
maybe2OK :: a -> Maybe a -> OK a
maybe2OK x Nothing  = unchanged x
maybe2OK _ (Just x) = changed x

-- apply the function on all elements of the list
-- noteworthy if any single is noteworthy
-- should coincide with mapM, but less convoluted
katalift :: (a -> OK b) -> [a] -> OK [b]
katalift k xs  =  unzipOK $ map k xs

unzipOK :: [OK a] -> OK [a]
unzipOK xs = mkOK (map valOf xs) (any hasChanged xs)

-- apply the function until a noteworthy change happens
-- not used?
katalift1 :: (a -> OK a) -> [a] -> OK [a]
katalift1 f []     =  unchanged []
katalift1 f (x:xs) |  b
                   =  changed (x' : xs)
                   |  otherwise
                   =  okmap (x' :) $ katalift1 f xs
                      where
                      fx  =  f x
                      x'  =  valOf fx
                      b   =  hasChanged fx

-- keep applying the function as long as there is a change
fixOK :: (a-> OK a) -> a -> OK a
fixOK f a  = appch (fixOK f) (f a)

