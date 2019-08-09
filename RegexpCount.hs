module RegexpCount where

import BigNum
import Data.Ratio
import Test.QuickCheck

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






           
