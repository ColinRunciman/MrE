-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module BigNum (BigNum, bigNumToDouble, doubleToBigNum, biggeomean, ratToBigNum) where

import Data.Ratio (numerator, denominator, (%))
import Data.Monoid (mappend)

-- makeshift floating point numbers with larger expos
data BigNum = BigNum { mantissa :: Double, expo :: Int }

zeroBigNum :: BigNum
zeroBigNum = BigNum { mantissa=0.0, expo = 0 }
-- these numbers mean: mantissa * 2**expo

normalise :: BigNum -> BigNum
normalise bn | ex == 0
             = bn
             | mantissa bn == 0.0 -- no silent =1 bit to begin with
             = zeroBigNum
             | otherwise
             = BigNum { mantissa=mantissa bn / (2**fromIntegral ex),
                        expo=ex+(expo bn) }
               where ex = exponent (mantissa bn)

adjust :: Double -> Int -> Double
adjust d n = d / (2 ** fromIntegral(abs n))

alignExponent :: BigNum -> Int -> Double -- returns aligned mantissa
alignExponent (BigNum { mantissa = m, expo = e }) target -- target always at least e
    | e==target
    = m
    | otherwise
    = adjust m (target - e)

addBigNums :: BigNum -> BigNum -> BigNum
addBigNums bn1 bn2 = normalise $ BigNum { mantissa=alignExponent bn1 m+alignExponent bn2 m, expo=m }
    where
    m = max (expo bn1)(expo bn2)

subBigNums bn1 bn2 = addBigNums bn1 (negateBigNum bn2)
negateBigNum bn = BigNum { mantissa = negate (mantissa bn), expo = expo bn }

mulBigNums bn1 bn2 = normalise $ BigNum { mantissa = mantissa bn1 * mantissa bn2,
                                          expo = expo bn1 + expo bn2 }

absBigNum bn |  mantissa bn >=0
             =  bn
             |  otherwise
             =  BigNum { mantissa=negate(mantissa bn), expo = expo bn }

sigBigNum bn = BigNum { mantissa = signum (mantissa bn), expo=0 }

-- not currently meant to be used to converting large integers to BigNum
bigNumfromInteger :: Integer -> BigNum
bigNumfromInteger 0 = zeroBigNum
bigNumfromInteger n = bnfI n 0
                      where
                      bnfI k m |  even k
                               =  bnfI (div k 2) (m+1)
                               |  otherwise
                               =  normalise $ BigNum { mantissa = fromInteger k, expo = m }

instance Show BigNum where
    show bn = shows (mantissa bn) (" * 2^" ++ show (expo bn))

instance Eq BigNum where
    x == y = mantissa nx == mantissa ny && expo nx == expo ny
             where
             nx = normalise x
             ny = normalise y

instance Num BigNum where
    (+) = addBigNums
    (*) = mulBigNums
    (-) = subBigNums
    negate = negateBigNum
    abs = absBigNum
    signum = sigBigNum
    fromInteger = bigNumfromInteger

recipBigNum :: BigNum -> BigNum
recipBigNum bn = normalise $ BigNum { mantissa = recip (mantissa bn), expo = negate(expo bn) }

ratToBigNum :: Rational -> BigNum
ratToBigNum r = r2b (numerator r) (denominator r) 0
                where
                r2b 0  _ _  = zeroBigNum
                r2b nu de e | even nu
                            = r2b (div nu 2) de (e+1)
                            | even de
                            = r2b nu (div de 2) (e-1)
                            | otherwise
                            = normalise $ BigNum { mantissa = fromRational (nu % de), expo = e }

instance Fractional BigNum where
    recip = recipBigNum
    fromRational = ratToBigNum

bigNumToRat :: BigNum -> Rational
bigNumToRat bn = toRational(mantissa bn) * toRational(2^expo bn)

-- assuming it is in range, otherwise it gives 0 or inf
bigNumToDouble :: BigNum -> Double
bigNumToDouble bn = mantissa bn * (2 ** fromIntegral (expo bn))

doubleToBigNum :: Double -> BigNum
doubleToBigNum d = normalise $ BigNum { mantissa = d, expo = 0}

compareBigNum :: BigNum -> BigNum -> Ordering
compareBigNum bn1 bn2 =
    compare (signum (mantissa bn1)) (signum (mantissa bn2)) `mappend`
    expocompare (expo cn1) (expo cn2) (mantissa bn1 >=0 ) `mappend`
    compare (mantissa cn1) (mantissa cn2)
    where
    cn1 = normalise bn1
    cn2 = normalise bn2
    expocompare k n True  = compare k n
    expocompare k n False = compare n k

instance Ord BigNum where
    compare = compareBigNum

instance Real BigNum where
    toRational = bigNumToRat

geomeanBig :: [BigNum] -> BigNum
geomeanBig xs = normalise b2
               where
               n = length xs
               nd = fromIntegral n
               exp2 = fromIntegral(expo b `mod` n) / nd
               efac = 2.0 ** exp2
               b = product xs
               m1 = mantissa b ** (1 / nd)
               b2 = BigNum { mantissa=m1 * efac, expo= expo b `div` n }

biggeomean :: [Double] -> Double
biggeomean xs = bigNumToDouble $ geomeanBig $ map doubleToBigNum xs
