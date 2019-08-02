module Leonardo where

data Leonardo a = Cons !Int !Int (Tree a) (Leonardo a) | Nil deriving Show
data Tree a = Bin a (Tree a) (Tree a) | Empty deriving Show

empty :: Leonardo a
empty = Nil

cons :: a -> Leonardo a -> Leonardo a
cons a (Cons i j bs (Cons j' k cs zs))
  | j == j' = Cons k (next j k) (Bin a bs cs) zs
cons a rs = Cons 1 1 (Bin a Empty Empty) rs

tailL :: Leonardo a -> Leonardo a
tailL Nil = error "tail of empty list"
tailL (Cons 1 1 _ li) = li
tailL (Cons k njk (Bin _ le ri) li) = Cons i j le (Cons j k ri li)
                                      where
                                      j = prev k njk
                                      i = prev2 k njk

size :: Leonardo a -> Int
size (Cons _ i _ as) = i + size as
size Nil = 0

-- 1,1,3,5,9,15,25
next :: Int -> Int -> Int
next p q = p+q+1

prev :: Int -> Int -> Int
prev p q = q-p-1

prev2 :: Int -> Int -> Int
prev2 p q = 2*p-q

(!) :: Leonardo a -> Int -> a
Nil ! i = undefined
Cons j k a as ! i
  | i < k = go i (prev j k) j a
  | otherwise = as ! (i - k)
  where
    go _ _ _ Empty = undefined
    go 0 _ _ (Bin a _ _) = a
    go i j k (Bin _ l r)
      | i <= j    = go (i-1)  (prev2 j k) (prev j k) l
      | otherwise = go (i-j-1) (prev j k) j r

select :: Leonardo a -> a -> Int -> a
select xs defau n | n>=size xs
                  = defau
                  | otherwise
                  = xs ! n

headL :: Leonardo a -> a
headL Nil = error "head of empty list"
headL (Cons _ _ Empty _)       = error "illegal Leonardo structure"
headL (Cons _ _ (Bin x _ _) _) = x

lastL :: Leonardo a -> a
lastL Nil = error "last of empty list"
lastL (Cons _ _ t Nil) = lastT t
lastL (Cons _ _ t u)   = lastL u

lastT Empty = error "illegal Leonardo structure"
lastT (Bin x Empty Empty) = x
lastT (Bin _ _ u)         = lastT u

{-
uncons :: Leonardo a -> Maybe(a,Leonardo a)
uncons Nil = Nothing
uncons (Cons _ _ (Bin x Empty Empty) Nil) = Just(x,Nil)
uncons (Cons m n (Bin x (Bin y t1 t2) t3) le) =
    Just(x,Cons (prev m n) m (Bin y t1 t2)......
-}

tsrif :: Leonardo a -> a
tsrif Nil = error "tsrif of empty list"
tsrif (Cons _ _ t Nil) = tsrifT t
tsrif (Cons _ _ _ le)  = tsrif le

tsrifT Empty = error "tsrifT of empty tree"
tsrifT (Bin x Empty Empty) = x
tsrifT (Bin x t     Empty) = tsrifT t
tsrifT (Bin x t     u    ) = tsrifT u

sumL :: Num a => Leonardo a -> a
sumL Nil = 0
sumL (Cons _ _ tr le) = sumT tr + sumL le

sumT :: Num a => Tree a -> a
sumT Empty = 0
sumT (Bin x y z) = x + sumT y + sumT z

instance Functor Leonardo where
    fmap f Nil = Nil
    fmap f (Cons m n tr le) =
           (Cons m n (fmap f tr) (fmap f le))

instance Functor Tree where
    fmap f Empty = Empty
    fmap f (Bin x t1 t2) = Bin (f x) (fmap f t1)(fmap f t2)

listify :: Leonardo a -> [a]
listify Nil = []
listify lxs = headL lxs : listify (tailL lxs)

{-
instance Applicative Leonardo where
    pure x = cons x Nil
    x <*> y =
        case (uncons x,uncons y) of
             (Nothing,_) -> Nil
             (_,Nothing) -> Nil
             (Just(fx,x'),Just(ya,a')) -> cons (fx ya)(x' <*> a')
    Nil <*> _ = Nil
    _ <*> Nil = Nil
    x <*> y   = cons (fx ya) (x' <*> y')
                where
                (fx,x') = uncons x
                (ya,a') = uncons y
-}
