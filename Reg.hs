import Data.List (isPrefixOf)
import Test.QuickCheck
import System.Environment
import qualified Leonardo as L
import Data.Ratio
import Data.Bits

data Exp  =  Sym Char | Opt Exp | Rep Exp | Alt Exp Exp | Cat Exp Exp

allSanes :: Integer -> [Integer]
allSanes n = 2 : n : from [n]
             where
             from ms = k: from (k:ms) where k = at ms (reverse ms)
             at ms msr = shift(head ms+xsum (tail ms) msr)1

xsum :: [Integer] -> [Integer] -> Integer
xsum [] _ = 0
xsum (x:xs) (y:ys) = x*y + xsum xs ys

growthRates :: Int -> [Integer] -> L.Leonardo Double
growthRates n xs = L.cons (fromIntegral (head xn1)) $ foldr L.cons L.empty ds
                   where
                   xn1 = take (n+1) xs
                   ds  = zipWith divide (tail xn1) xn1

divide :: Integer -> Integer -> Double
divide x y = fromRational( x % y )

type Distribution = Int -> Double

createDistribution :: Int -> Int -> Distribution
createDistribution alphaSize accuracy =
    L.select ys (L.lastL ys)
    where
      ys  = growthRates accuracy (allSanes (fromIntegral alphaSize))

{-
-- relative ratio between subsequent generations, approximate formula found via curve-fitting
regRatio :: Int -> Double
regRatio x = let xx=fromIntegral x in 5*sqrt xx-0.5*xx

splitRatio :: Int -> Double
splitRatio x = fromIntegral (2*x) /(y*(y-2)) where y = regRatio x 

splitProbability :: Int -> Distribution -> Double
splitProbability 1 d = split1 d
splitProbability 2 d = splitProbability 1 d * (2 / ratio d)

acoordinate :: Int -> Double
acoordinate x = 6.93e-7*x'+0.000166913 where x' = fromIntegral x

bcoordinate :: Int -> Double
bcoordinate x = -0.06645198-0.0003571474*x' where x' = fromIntegral x

ccoordinate :: Int -> Double
ccoordinate x = -3.30768+0.03217*x' where x'=fromIntegral x

-- ratio is the regRatio for this alphabet
-- split1 is twice |alpha|/ratio*(ratio-2), the probability of the most uneven split
data Distribution = Distribution { ratio :: Double, split1 :: Double, aSize :: Int }
-}

repMultiplier :: Distribution -> Int -> Int
repMultiplier d n = round (20000 / (d n)) -- 10000/d is reps, another 10000/d is opts

binMultiplier d n = 10000 - repMultiplier d n

anExp :: [Char] -> Distribution -> Int -> Gen Exp
anExp cs d 1 = elements $ map Sym cs
anExp cs d 2 = do f<- elements [Opt,Rep]; c<-elements cs; return(f (Sym c))
anExp cs d n | n>2 
             =  frequency [(repMultiplier d n,anOptOrRep cs d n),
                           (binMultiplier d n,anAltOrCat cs d n)]

anOptOrRep cs d n =  do f <- elements [ Opt, Rep ]
                        e <- anExp cs d ( n-1 )
                        return (f e)

convert :: Double -> Double -> Distribution -> Int -> Int-> Int
convert _ _                    _ 1 _ = 1 -- reached the end
convert p thisSplitProbability d n b | p <= thisSplitProbability
                                     = n
                                     | otherwise
                                     = convert (p-thisSplitProbability) ns d (n-1)(b+1)
                                       where ns = (thisSplitProbability * d b) / d n

split1 :: Distribution -> Int -> Double
split1 d n = (2* d 0)/(d n-2*d(n-1))

anAltOrCat :: [Char] -> Distribution -> Int -> Gen Exp 
anAltOrCat cs d n =  do f <- elements [ Alt, Cat ]
                        p <- choose (0.0,1.0)
                        let i=convert p (split1 d n) d (n-2) 1
                        let j=n-(i+1)           -- the twinned index
                        (s0,s1)<- elements[(i,j),(j,i)]  -- pick forward/backward split
                        e1 <- anExp cs d s0
                        e2 <- anExp cs d s1
                        return (f e1 e2)
 
instance Show Exp where
  show (Sym c)      =  [c]
  show (Opt e)      =  brackIf (isAlt e || isCat e) (show e) ++ "?"
  show (Rep e)      =  brackIf (isAlt e || isCat e) (show e) ++ "*"
  show (Alt e1 e2)  =  show e1 ++ "+" ++ show e2
  show (Cat e1 e2)  =  brackIf (isAlt e1) (show e1) ++
                       brackIf (isAlt e2) (show e2)

brackIf :: Bool -> String -> String
brackIf True  s  =  "("++s++")"
brackIf False s  =  s

isAlt (Alt _ _)  =  True
isAlt _          =  False

isCat (Cat _ _)  =  True
isCat _          =  False

usage = "Reg [-w<no.>] [-s<no.>] [-q<no.>]\n"

data Params  =  Params {width, size, quantity :: Int} deriving Show

defaults  =  Params {width = 2, size = 10, quantity = 10}

main = do args <- getArgs ; generateBy (resetBy args defaults)

resetBy :: [String] -> Params -> Params
resetBy []     p  =  p
resetBy (s:ss) p  =  resetBy ss $
                     case letter of
                     'w' -> p {width    = number}
                     's' -> p {size     = number}
                     'q' -> p {quantity = number}
                     _   -> error usage
                     where
                       '-':letter:digits  =  s
                       number             =  read digits

globalAccuracy :: Int
globalAccuracy = 100

generateBy :: Params -> IO ()
generateBy p  =  generateQ (quantity p) g
                 where
                 g  =  anExp al d (size p)
                 d  =  createDistribution (width p) globalAccuracy
                 al =  take (width p) ['a' .. 'z']


generateQ :: Int -> Gen Exp -> IO ()
generateQ 0 g  =  return ()
generateQ n g  |  n > 0
               =  do
                     e <- generate g
                     print e
                     generateQ (n-1) g


