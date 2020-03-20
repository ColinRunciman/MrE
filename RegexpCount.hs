module RegexpCount where

import BigNum
import Data.Ratio
import Test.QuickCheck
import Data.List (sort)
import qualified Data.IntMap.Strict as M

type PopNumber = BigNum -- was Integer

-- parameter is alphabet size
prefixSizes :: Int -> [[PopNumber]]
prefixSizes k = s1 : follow s1
                where
                kn = fromIntegral k
                s1 = [2,2]
                follow xs = let ys=next1 xs in ys : follow ys
                next1 (x:y:xs)       = (2*x+kn*y) : next2 (x:y:xs)
                next2 (x:y:z:xs)     = (2*x+2*y+kn*z) : next2 (y:z:xs)
                next2 [x,y]          = [2*x+2*y,2*y]



nextp :: BigNum -> [BigNum] -> [BigNum]
nextp kn ( _ : x : y : xs ) = (kn * x) : next1p kn (x:y:xs)

next1p kn (x:y:xs)       = (2*x+kn*y) : next2p kn (x:y:xs)

next2p kn (x:y:z:xs)     = (2*x+2*y+kn*z) : next2p kn (y:z:xs)
next2p kn [x,y]          = [2*x+2*y,2*y]


sizeAt :: Int -> Int -> PopNumber
sizeAt sz n = prefixSizes sz !! n !! 0




divideBN :: BigNum -> BigNum -> Double
divideBN x y = bigNumToDouble (x / y)

threewaySplitsBN :: BigNum -> [ BigNum ] -> [(Int,Int)]
threewaySplitsBN bn xs = th (0:xs ++ [0,0])
                       where
                       th (x:y:z:xs) = (dbn n1 su,dbn n2 su): th(y:z:xs)
                           where
                           n1=2*x
                           n2=2*y
                           n3=bn*z
                           su=n1+n2+n3
                       th _          = []
                       dbn x y       = promille (divideBN x y)

-- these are 3-way distinctions into arity 2 (first no), arity 1 (second no), arity 0 (1000-no1-no2)
type PrefixDistribution = [[(Int,Int)]]

-- turns a probability into an 1/1000 Int
promille :: Double -> Int
promille d = round (1000 * d)

-- first parameter: alphabet size, second target expression size
computeDistribution :: Int -> Int -> PrefixDistribution
computeDistribution aSize eSize =
    map (threewaySplitsBN bn) $ zipWith take [1..] (reverse (take (eSize-1) (prefixSizes aSize)))
    where
    bn = fromIntegral aSize

data Exp  =  Sym Char | Opt Exp | Rep Exp | Alt Exp Exp | Cat Exp Exp

generateExp :: [Char] -> PrefixDistribution -> Gen Exp
generateExp cs pd =
    do
        c <- genSym
        addPrefix 0 (tail pd) [c]
    where
    genSym           =  elements $ map Sym cs
    apfun 0 xs       =  fmap (:xs) genSym
    apfun 1 (x:xs)   =  elements [ Opt x : xs, Rep x : xs ]
    apfun 2 (x:y:xs) =  elements [ Alt x y : xs, Cat x y : xs ]
    apfun _ _        =  error "apfun: bad arity"
    addPrefix _ []          [t] = elements [Opt t, Rep t]
    addPrefix _ []        [t,u] = elements [Alt t u, Cat t u]
    addPrefix n []           ts = error $ "arity " ++ show n ++ ", "
                                           ++ show(length ts) ++ " terms on stack"
    addPrefix n (probs : pd) ts =
        do
            let (p1,p2) = probs !! n
            arity <- frequency [(p1,return 2),(p2,return 1),(1000-p1-p2,return 0)]
            nts   <- apfun arity ts
            addPrefix (n+1-arity) pd nts

instance Show Exp where
  showsPrec _ (Sym c)     =  (c:)
  showsPrec _ (Opt e)     =  showsPrec optPrec e . ('?':)
  showsPrec _ (Rep e)     =  showsPrec optPrec e . ('*':)
  showsPrec n (Alt e1 e2) =  showParen (n>altPrec) $
                             showsPrec (altPrec+1) e1 . ('+':) . showsPrec altPrec e2
  showsPrec n (Cat e1 e2) =  showParen (n>catPrec) $
                             showsPrec (catPrec+1) e1 . showsPrec catPrec e2

altPrec, catPrec, optPrec, repPrec :: Int
altPrec = 2
catPrec = 4
optPrec = 6
repPrec = optPrec


-------------------------------------------------------- population count under assoc ------------------
data PopCount a = PopCount { unary :: a, binary :: a, nullary :: a } deriving Show
tote :: PopCount BigNum -> BigNum
tote pc = unary pc + nullary pc + binary pc

leftArg :: PopCount BigNum -> BigNum
leftArg pc = unary pc + nullary pc + (binary pc / 2)

popInit :: BigNum -> PopCount BigNum
popInit kn = PopCount { unary =0, binary=0, nullary=kn }

popSizes :: BigNum -> [PopCount BigNum]
popSizes kn = x1 : next [x1]
              where
              x1 = popInit kn
              next xs = let ys=follow xs (reverse (tail xs)) in
                        ys : next (ys:xs)
              follow (x:xs) ys = PopCount { unary=(binary x+nullary x)*2,
                                            binary=sum [binary pc*pdk + 2*unary pc*pdk + 2*nullary pc*pdk|
                                                        (pc,pd)<-zip xs ys, let pdk = tote pd ],
                                            nullary=0 }

data Constraint = None | ParentUnary | ParentOtherBinary Bool

generateAssocExp :: [Char] -> Int -> Gen Exp
generateAssocExp cs n = gAssocExp cs n (computeDist (reverse $ take n pc)) None
                        where pc = popSizes (fromIntegral(length cs))

gAssocExp :: [Char] -> Int -> Distribution -> Constraint -> Gen Exp
gAssocExp cs 1 _ _      = elements $ map Sym cs -- size 1, must be symbol
gAssocExp cs 2 _ _      = elements [ f (Sym c) | f <- [ Rep, Opt ], c<- cs] -- size 2, no bin
gAssocExp cs 3 _ _      = elements [ f (Sym c) (Sym d) | f <- [ Alt, Cat ], c<-cs, d<- cs] -- size 3, no un
gAssocExp cs k (x:xs) c = generateArity x c >>= process c
    where
    process _ 1 = do
                      e <- gAssocExp cs (k-1) xs ParentUnary
                      f <- elements [Rep, Opt]
                      return $ f e
    process (ParentOtherBinary b) 2 = bin b
    process _ 2                     = elements [ True, False ] >>= bin
    bin b = do
              i <- generateSplit (binarySplits x)
              el <- gAssocExp cs i (lastN (i-1) xs) (ParentOtherBinary (not b))
              er <- gAssocExp cs (k-i-1) (lastN (k-i-2) xs) None
              return (binFunc b el er)


lastN n xs = reverse $ take n $ reverse xs
binFunc True  = Alt
binFunc False = Cat

generateArity :: DistElem -> Constraint -> Gen Int
generateArity de ParentUnary           = return 2 -- ok as it is not used for size 2
generateArity de (ParentOtherBinary _) = frequency [ (2*unaryFreq de, return 1),(binaryFreq de,return 2) ]
generateArity de None                  = frequency [ (unaryFreq de,return 1),(binaryFreq de,return 2)]

perbillion :: BigNum -> BigNum -> (Int,Int)
perbillion b1 b2 = (f b1,f b2) where f x = round(bigNumToDouble $ x*1000000000/(b1+b2))

perbillionList :: [BigNum] -> [Int]
perbillionList xs = map f xs
                    where
                    s = sum xs
                    f x = round(bigNumToDouble $ x*1000000000/s)

data DistElem = DistElem { unaryFreq, binaryFreq :: Int, binarySplits :: [Int] }
type Distribution = [ DistElem ]

computeDist :: [PopCount BigNum] -> Distribution
computeDist [_] = [] -- size 1, chars, are not included here
computeDist (pc:pcs) =
    DistElem {unaryFreq=u, binaryFreq=b,binarySplits=perbillionList $ binSplits (tail pcs)}: computeDist pcs
    where
    (u,b)=perbillion (unary pc)(binary pc)

binSplits :: [PopCount BigNum] -> [BigNum]
binSplits xs = zipWith f xs (reverse xs)
               where
               f pc1 pc2 = leftArg pc1 * tote pc2

generateSplit :: [Int] -> Gen Int
generateSplit xs = frequency (zip xs (map return [1..]))

--------------------------------------------------------------------------------------------------- counting total languages ------

data LangCount = LangCount { tot:: BigNum, totp:: BigNum, swplist :: [(BigNum,BigNum)] } deriving Show
nontotewp, allexp, allewp, nonewp, totswp :: LangCount -> BigNum
nontotewp x = sum (map fst (swplist x))
allewp x    = tot x + nontotewp x
allexp x    = tot x + totp x + sum [ y+z | (y,z)<-swplist x ]
nonewp x    = sum (map snd (swplist x)) + totp x
totswp x    = tot x + totp x + uncurry (+) (last $ swplist x)

ladd :: LangCount -> LangCount -> LangCount
ladd x y = LangCount { tot = tot x+tot y, totp = totp x + totp y,
                       swplist = [ (x1+x2,y1+y2) | ((x1,y1),(x2,y2))<-zip (swplist x)(swplist y) ] }

langSizes :: Int -> [ LangCount ] -- parameter is alphabet size
langSizes n = x1 : next [x1]
              where
              fu = makeMap n
              x1 = langInit n
              nb = fromIntegral n
              next xs = let ys=follow xs (reverse (tail xs)) in
                        ys : next (ys:xs)
              follow (x:xs) ys = starCount x `ladd` queryCount x `ladd` binCount xs ys
              binCount [] [] = LangCount { tot = 0, totp=0, swplist = take (n+1) $ repeat (0,0) }
              binCount (x:xs)(y:ys) = bin1Count x y `ladd` binCount xs ys
              bin1Count x y = seqCount x y fu `ladd` altCount x y fu

langReport :: Int -> Int -> String
langReport siz wid =
    "number of expressions:\t\t" ++ show (allexp pop) ++ "\n" ++
    "guaranteed total languages:\t" ++ show (100*totalRatio pop) ++ "%\n" ++
    "alpha(x)=swa(x) proportion:\t" ++ show (100*swpRatio pop) ++ "%\n"
    where pop = langSizes wid !! (siz-1)

totalRatio, swpRatio :: LangCount -> Double
totalRatio l = bigNumToDouble (tot l / allexp l)
swpRatio l   = bigNumToDouble (totswp l / allexp l)

totalRatios :: Int -> [Double]
totalRatios n = map totalRatio (langSizes n)
swpRatios   n = map swpRatio (langSizes n)

langInit ::  Int -> LangCount -- for size 1
langInit alsi = LangCount { tot=0, totp=0, swplist = [(0,0),(0,fromIntegral alsi)] ++ take (alsi - 1) (repeat (0,0)) }

queryCount :: LangCount -> LangCount
queryCount x = LangCount { tot=tot x+totp x, totp=0, swplist = [(y+z,0)|(y,z)<-swplist x] }

starCount :: LangCount -> LangCount
starCount x = LangCount { tot = tot x + totp x + uncurry (+) (last (swplist x)), totp=0,
                          swplist = init [(y+z,0)|(y,z)<-swplist x] ++ [(0,0)] }

seqCount :: LangCount -> LangCount -> Func -> LangCount
seqCount p1 p2 fu = LangCount { tot=tot p1*tot p2 + tot p1*nontotewp p2 + nontotewp p1*tot p2,
                                totp=totp p1*allewp p2 + allewp p1*totp p2 + tot p1 * snd(last (swplist p2)) + tot p2 * snd(last (swplist p1)),
                                swplist = [ swpfunc (n-1) | n <- [1..length(swplist p1)]] }
                   where
                   nn = ( length (swplist p1) - 1)
                   swpfunc k | k==nn -- do not count sequences with tot, as these are totp now
                             = (ewpfunc k,nonewpfunc k)
                             | otherwise
                             = (ewpfunc k,nonewpfunc k+tot p1*snd(swplist p2!!k)+tot p2*snd(swplist p1!!k))
                   ewpfunc k = sum [ e1*e2*ratToBigNum2(prob2 i1 i2 k fu) | i1<-[0..k], i2<-[k-i1..k], let e1=fst(swplist p1!!i1), let e2=fst(swplist p2!!i2) ]
                   nonewpfunc 0 = nonewp p1 * nonewp p2 +fst(head(swplist p1))*nontotewp p2 +fst(head(swplist p2))*nontotewp p1
                   nonewpfunc n = fst(swplist p1 !! n)*nontotewp p2 + fst(swplist p2!!n)*nontotewp p1

altCount p1 p2 fu = LangCount { tot=tot p1*tp2+tp1*tot p2-tot p1*tot p2+totp p1*nontotewp p2+nontotewp p1*totp p2,
                                totp=totp p1*nonewp p2+nonewp p1*totp p2 - totp p1*totp p2,
                                swplist = [ swpfunc (fromIntegral n-1) | n<- [1..length(swplist p1)]] }
                    where tp1=allexp p1
                          tp2=allexp p2
                          -- nn = length (swplist p1) - 1
                          swpfunc k = (ewpfunc k,nonewpfunc k)
                          ewpfunc k = sum [ e1*e2*ratToBigNum2(prob2 i1 i2 k fu) | i1<-[0..k], i2<-[k-i1..k], let e1=fst(swplist p1!!i1), let e2=uncurry (+)(swplist p2!!i2) ]
                                      +
                                      sum [ e1*e2*ratToBigNum2(prob2 i1 i2 k fu) | i1<-[0..k], i2<-[k-i1..k], let e1=snd(swplist p1!!i1), let e2=fst(swplist p2!!i2) ]
                          nonewpfunc k = sum [ e1*e2*ratToBigNum2(prob2 i1 i2 k fu) | i1<-[0..k], i2<-[k-i1..k], let e1=snd(swplist p1!!i1), let e2=snd(swplist p2!!i2) ]

ratToBigNum2 :: Ratio Int -> BigNum
ratToBigNum2 x = ratToBigNum (fromIntegral(numerator x) % fromIntegral(denominator x))



prob :: Int -> Int -> Int ->Int -> Ratio Int
prob na nb n target | na>n || nb >n || na<0 || nb<0 || target>n || target<0
                    = error "bad values in probability computation"
                    | na>target || nb>target || na+nb<target
                    = 0
                    | na<nb
                    = prob nb na n target
                    | nb==0 -- since na+nb>=target and na<=target
                    = 1
                    | otherwise
                    = (binom n target * binom target na * binom na (na+nb-target)) % (binom n na*binom n nb)

type Func = M.IntMap(M.IntMap(M.IntMap (Ratio Int)))
makeMap :: Int -> Func
makeMap n = M.fromList [ (na,l1 na)|na<-[1..n]]
            where
            l1 a = M.fromList [(nb,l2 nb)|nb<-[1..a]]
                   where
                   l2 b = M.fromList [(nt,prob a b n nt)|nt<-[a..min n (a+b)]]

prob2 :: Int -> Int -> Int-> Func -> Ratio Int
prob2 na nb target func | na<nb
                        = prob2 nb na target func
                        | nb==0
                        = 1
                        | otherwise
                        = func M.! na M.! nb M.! target

{-
binom :: Integral a=> a->a->a
binom n k | 2*k>n
          = ch n (n-k)
          | otherwise
          = ch n k
             where
             ch n 0 = 1
             ch n k = ch2 n 2 (n-1)
                      where
                      ch2 cur kk nn | kk>k
                                    = cur
                                    | otherwise
                                    = ch2 ((cur * nn) `div` kk) (kk+1)(nn-1)
-}
binomialCalc :: Int -> Int -> Int
binomialCalc n k
  | k == 0 || k == n = 1
  | k == 1           = n
  | otherwise        = binom (n-1) (k-1) + binom (n-1) k

binomialTab :: [[Int]]
binomialTab = [[ binomialCalc n k | k <- [0..n]] | n <- [0..]]

binom :: Int -> Int -> Int
binom n k = binomialTab!!n!!k
