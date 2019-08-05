module RegexpCount where
import Data.Ratio

-- parameter is alphabet size
-- prefixSizes sz !! n !! k is the number of (partial) regexp trees of arity k and size n, given alphabet size sz
-- k==0 gives completed regexps
prefixSizes :: Int -> [[Integer]]
prefixSizes k = [0,1] : s1 : follow s1
                where
                kn = fromIntegral k
                s1 = [kn,2,2]
                follow xs = let ys=next xs in ys : follow ys
                next (_ : x : y: xs) = (kn*x) : next1 (x:y:xs)
                next1 (x:y:xs)       = (2*x+kn*y) : next2 (x:y:xs)
                next2 (x:y:z:xs)     = (2*x+2*y+kn*z) : next2 (y:z:xs)
                next2 [x,y]          = [2*x+2*y,2*y]

sizeAt :: Int -> Int -> Integer
sizeAt sz n = prefixSizes sz !! n !! 0

-- an alternative way of describing the number of regexps, based on Catalan numbers
-- the even case is not right
formula :: Integer -> Integer -> Integer
formula kn n | even n
             = sum []
             | otherwise
             = kn* sum [ 2^(m+i)*catalan(m-i)*kn^(m-i)*| i<-[0..m]]
               where m = div n 2

{-
-- creating a prefix for alphabet size alpha of length size with k
-- what is prob that last symbol has arity 'ar'
probability :: Int -> Int -> Int -> Int -> Double
probability alpha size k ar = prob (prefixSizes alpha!!size) k ar

prob :: [Integer] -> Int -> Int -> Double
prob pcounts 0 ar = if ar==0 then 1 else 0  
prob pcounts 1 2  = 0
prob pcounts 1 1  = divide n1 (n1+n2)
                    where n1=2*(pcounts!!1)
                          n2=kn*(pcounts!!2)
prob pcounts k ar
prob pcounts k ar
prob pcounts k ar
-}
divide :: Integer -> Integer -> Double
divide x y = fromRational( x % y )

threewaySplits :: Integer -> [Integer] -> [(Double,Double)]
threewaySplits kn xs = th (drop 1 xs)
                       where
                       th [x,y]      = th [x,y,0]
                       th (0:_)      = []
                       th (x:y:z:xs) = (divide n1 su,divide n2 su): th(y:z:xs)
                           where
                           n1=2*x
                           n2=2*y
                           n3=kn*z
                           su=n1+n2+n3
           
