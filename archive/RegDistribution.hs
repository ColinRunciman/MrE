module RegDistribution where
import Data.Ratio
import Data.Bits
--import qualified Leonardo as L

-- parameter is alphabet size
allRegexps :: Integer -> [Integer]
allRegexps n = thecoalg
               where
               thecoalg = 2 : from 1
               from n = at n : from (n+1)
               at 1 = n + normal 1
               at k = normal k
               normal m = 2*thecoalg!!(m-1)+
                          2*sum[ (thecoalg !! x) * (thecoalg !! y)| x<-[0..m-1], let y=m-1-x ]

allSaneRegexps :: Integer -> [Integer]
allSaneRegexps n = thecoalg
                   where
                   thecoalg = 2 : n : from 2
                   from n = at n : from (n+1)
                   at m | even m    = basic m
                        | otherwise = let k=div m 2 in basic m - 2*((thecoalg !! k)^2)
                   basic m = 2*thecoalg!!(m-1)+4*sum[ (thecoalg !! x) * (thecoalg !! y)| x<-[1..div (m-1) 2], let y=m-1-x ]
                   -- at m = 2*thecoalg!!(m-1)+2*sum[ (thecoalg !! x) * (thecoalg !! y)| x<-[1..m-2], let y=m-1-x ]
{-
allSanes :: Integer -> [Integer]
allSanes n = 2 : n : from 2 (L.cons n L.Nil)
                   where
                   from m leo = k : from (m+1) (L.cons k leo) where k = at m leo
                   at m leo   = shift(L.first leo + sum[ (leo L.! x) * (leo L.! y)| x<-[1..m-2], let y=m-1-x ]) 1
-}

allSanes :: Integer -> [Integer]
allSanes n = 2 : n : from [n]
             where
             from ms = k: from (k:ms) where k = at ms (reverse ms)
             at ms msr = shift(head ms+xsum (tail ms) msr)1

xsum :: [Integer] -> [Integer] -> Integer
xsum [] _ = 0
xsum (x:xs) (y:ys) = x*y + xsum xs ys

{-
allSanesLeo :: Integer -> [ L.Leonardo Integer ]
allSanesLeo n = leo0 : leo1 : from 2 leo1
    where
    leo0 = L.cons 2 L.Nil
    leo1 = L.cons n leo0     
    from m leo = leok : from (m+1) leok
                 where
                 k = at m leo
                 leok = L.cons k leo
    at m leo   = 2*L.first leo + 2*sum[ (leo L.! x) * (leo L.! y)| x<-[1..m-2], let y=m-1-x ]  
-}

allSanesL :: Integer -> [[Integer]]
allSanesL n = li0 : li1 : from li1
    where
    li0 = [2]
    li1 = n:li0    
    from li   = leok : from leok
              where
              k = at li (reverse li)
              leok = k:li
    at li lir = shift(head li+xsum (tail li) lir) 1
             

log10 :: Integer -> Integer
log10 x = if x>= 10 then 1+log10(div x 10) else 0

growthRate :: [Integer] -> [Double]
growthRate xs = zipWith divide (tail xs) xs

{-
frequency :: L.Leonardo Integer -> L.Leonardo Double
frequency leo = fmap (\x-> divide x su) leo where su=L.sumL leo

frequencies :: Integer -> [ L.Leonardo Double ]
frequencies n = map frequency $ allSanesLeo n
-}

frequency :: [Integer] -> [Double]
frequency xs = map (\x->divide x su) ys
               where
               ys = zipWith (*) (tail xs) (reverse xs)
               su = sum ys

frequencyDistribution :: [Integer] -> [Int]
frequencyDistribution xs =  [ fromIntegral (div x sm) | x<-ys ]
                            where
                            ys = zipWith (*) (tail xs) (reverse xs)
                            sm = minimum ys


frequencies :: Integer -> [[Double]]
frequencies n = map frequency $ allSanesL n

divide :: Integer -> Integer -> Double
divide x y = fromRational( x % y )


