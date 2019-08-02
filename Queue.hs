module Queue where

data Queue a = Queue [a] [a] deriving Show

emptyQ :: Queue a
emptyQ = Queue [][]

singletonQ :: a -> Queue a
singletonQ a = Queue [a][]

enterQ :: a -> Queue a -> Queue a
enterQ x (Queue [][])  = Queue [x][]
enterQ x (Queue xs ys) = Queue xs (x:ys)

enterListQ :: [a] -> Queue a -> Queue a
enterListQ xs (Queue ys []) = Queue (ys++xs) []
enterListQ xs (Queue ne ys) = Queue ne (foldl (\q x->x:q) ys xs)

list2Q :: [a] -> Queue a
list2Q xs = Queue xs []

isEmptyQ :: Queue a -> Bool
isEmptyQ (Queue xs ys) = null xs && null ys

pollQ :: Queue a -> (a,Queue a)
pollQ (Queue [x] xs)    = (x,Queue (reverse xs) [])
pollQ (Queue (x:xs) ys) = (x,Queue xs ys)
pollQ (Queue [] [])     = error "poll of empty queue"
pollQ (Queue [] xs)     = error "internal error: ill-maintained queue"

pollQM :: Queue a -> Maybe (a,Queue a)
pollQM (Queue [x] xs)    = Just(x,Queue (reverse xs) [])
pollQM (Queue (x:xs) ys) = Just(x,Queue xs ys)
pollQM (Queue [] [])     = Nothing
pollQM (Queue [] xs)     = error "internal error: ill-maintained queue"
