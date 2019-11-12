module RegexpCount where

import BigNum
import Data.Ratio
import Test.QuickCheck
import Data.List (sort)

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
               


              
               



                         
                         






           
