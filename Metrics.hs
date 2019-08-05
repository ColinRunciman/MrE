module Metrics where

import Expression
import Context
import Fuse
import StarPromotion
--import Normalization
import Catalogue
import Comparison
import Pressing
--import Refactorization
import Shrinking
--import Stellation
--import Automization
import Data.List(nub,nubBy,minimumBy,union,partition,foldl1',sortBy,sort)
import Data.Maybe(isJust,fromJust,fromMaybe)
import qualified Data.Set as S
import List (segments,sublists,maximaBy,nubSort,itemRest,nubMerge)
import System.IO.Unsafe(unsafePerformIO)
import Control.Exception(catch,IOException)
import Data.Time.Clock
import Numeric
import Control.Monad
import Function
import GHC.Exts (groupWith, sortWith)
import Generator
--import TopologicalSearchTree
import PreOrderTrees

-- reCount m n gives the number of distinct regular
-- expressions of size m over an alphabet of size n:
-- crazy numbers!
reCount :: Integer -> Integer -> Integer
reCount 0 n  =  2 -- Emp, Lam
reCount 1 n  =  -- Syms and Opt/Rep/Cat/Alt applied to size 0
                n + 
                -- Alts and Cats
                2 * (reCount 0 n * reCount 0 n) +
                -- Reps and Opts
                2 * reCount 0 n
reCount m n  =  -- Alts and Cats
                2 * sum [reCount i n * reCount (m-i-1) n | i <- [0..(m-1)]] +
                -- Reps and Opts
                2 * reCount (m-1) n

-- Sane REs:
-- (1) Emp or Lam do not occur as components of other expressions
-- (2) Alt combines multisets of non-Alt, non-Opt components
--     (in Alt xs, xs is ordered to avoid repeating multisets)
-- (3) Cat combines non-Cat components
-- (4) Opt bodies are not opts (but may be Alts)
saneREs :: [Char] -> Int -> [RE]
saneREs ss n  |  n == 0
              =  []
              |  otherwise
              =  Emp : Lam : non01saneREs ss n

non01saneREs :: [Char] -> Int -> [RE]
non01saneREs ss n  |  n > 0
                   =  [Sym s     | s <- ss] ++
                      [alt [x,y] | n >= 3,
                        x <- memo !! (n-2), not $ (isAlt x || isOpt x),
                        y <- memo !! (n-(1+size x)), not $ isOpt y,
                        nonDecreasing x y ] ++
                      [cat [x,y] | n >= 3,
                        x <- memo !! (n-2), not $ isCat x,
                        y <- memo !! (n-(1+size x))] ++
                      [Rep x     | n >= 2,
                        x <- memo !! (n-1)] ++
                      [Opt x     | n >= 2,
                        x <- memo !! (n-1), not $ isOpt x]
                   |  otherwise
                   =  []              
  where
  memo = map (non01saneREs ss) [0..]

nonDecreasing x (Alt _ (y:_))  =  x <= y
nonDecreasing x y              =  x <= y

quotBy :: (a->a->Bool) -> [a] -> [[a]]
quotBy eq []      =  []
quotBy eq (x:xs)  =  (x:xs') : quotBy eq xs''
  where
  (xs',xs'') = partition (eq x) xs

simTest :: ((RE->RE)->[RE]->IO()) -> (RE->RE) -> Int -> IO()
simTest f s maxSize  =  mapM_ simTestSize [1..maxSize]
  where
  simTestSize n    =  do
                        putStr $ "size " ++ show n ++": "
                        f s $ saneREs sigma n

-- effectiveness of a simplification procedure: simplify a test-set
-- of REs; take quotient by exact equivalence; calculate max-size/min-size
-- for each equivalence class and report the average and max ratio
sizeCfMin :: (RE->RE) -> [RE] -> IO()
sizeCfMin s res =
  do 
    putStrLn $ "worst=" ++ show (maxratio) ++ "; " ++
               "mean=" ++ show (sum ratios / float (length ratios))
    ( if maxratio > 1.0 then
        do 
          putStrLn "worst-case examples:"
          mapM_ (worstCaseEg maxratio) (zip3 classes sizes ratios)
      else
        return () )
  where
  maxratio  = maximum ratios
  ratios    = map (\xs -> float (maximum xs) / float (minimum xs)) sizes
  sizes     = map (map size) classes
  classes   = groupOrder compRE $ map s res -- was: quotBy (===) instead of groupOrder compRE

float :: Int -> Float
float = fromInteger . toInteger

asPercentageOf :: Int -> Int -> Float
x `asPercentageOf` y  =  float (100 * x) / float y

worstCaseEg mr (xs,ss,r) =
  if r == mr then putStrLn (show xmax ++ " is equivalent to " ++ show xmin)
  else return ()
  where
  xmax = head [x | (x,s) <- zip xs ss, s == maximum ss]
  xmin = head [x | (x,s) <- zip xs ss, s == minimum ss]

minRate :: (RE->RE) -> [RE] -> IO ()
minRate sim res  =  do
    putStrLn "Simplification to minimum possible size was achieved for"
    putStrLn $ show (m `asPercentageOf` n) ++ " % of tested REs." 
  where
  m  =  sum [ fromEnum $ s == size (minimize re')
            | re <- res, let re' = sim re',
              let s = claim "small enough for catalogue look-up" (<= maxSize) $
                      size re' ]
  n  =  length res

-- a simplification speed measure for a list of test REs
-- computed as: sum of catalogue-lookup times / sum of sim times

{- TO DO:
simSpeed :: (RE->RE) -> [RE] -> IO ()
simSpeed sim res  =  do
  putStrLn "Simplification was "++ show s ++ " X faster than minimization by enumerative search."

subSpeed :: (RE->RE->Bool) -> [(RE,RE)] -> IO ()
-}

timingsName :: String
timingsName    =  "TIMINGS-"++sigma++"-"++show maxSize++".txt"

createTimings :: IO ()
createTimings  =  writeFile timingsName $ timingsText

timingsText :: String
timingsText  =  unlines $ (timingsName :) $ map timingItem $ 
                 [ ("kataGrade",      kataGrade),
                   ("fuse",           fuse),
                   ("promote",        promote),
                   ("press",          press),
                   --("refactorize",    refactorize), 
                   ("shrink",         shrink) {-
                   ("stellate",       stellate)  ,
                   ("stellate+tree",  stellateWithTreeLookup),
                   ("minimize",  minimize),
                   ("minimizeBMS", minimizeBMS) -} ]

timingItem :: (String, RE->RE) -> String
timingItem (s,f)  =  s++":"++pad (18 - length s)++
                     pad (6 - length (takeWhile (/= '.') t'))++t'++"s"
  where
  t'  =  showFFloat (Just 2) (timedSim f sanes) ""

timedSim :: (RE->RE) -> [RE] -> Float
timedSim sim res  =
  time $ (>= 0) $ foldl1' (+)  [ size $ sim x | x <- res ]

timedSub :: (FuseRE -> FuseRE -> Bool) -> [RE] -> Float
timedSub (<=<) res  =
  time $ (>= 0) $ foldl1' (+) [ fromEnum $ x <=< y | x <- res, y <- res ]

subYesRate :: (RE->RE->Bool) -> [RE] -> IO ()
subYesRate (<=<) res  |  n > 0
                      =  do
                           putStrLn "Positive results obtained for "
                           putStrLn $
                             show (m `asPercentageOf` n) ++
                             " % of tested RE pairs in sublanguage relation."
                      |  otherwise
                      =  do
                           putStrLn "No tested RE pairs in sublanguage relation."
  where
  m  =  sum [ fromEnum $ re1 <=< re2       | re1 <- res, re2 <- res ]
  n  =  sum [ fromEnum $ re1 `sublang` re2 | re1 <- res, re2 <- res ]

time :: Bool -> Float
time x  =  unsafePerformIO $ do
  t0  <-  getCurrentTime
  compute
  t1  <-  getCurrentTime
  return $ fromRational $ toRational $ utctDayTime t1 - utctDayTime t0
  where
  compute | x  =  return ()

mirrorAlphaEquiv :: RE -> RE -> Bool
mirrorAlphaEquiv x y  =  alphaEquiv x y || alphaEquiv x (mirrorRS y)

-- variation of mirror that preserves rolledness of cats and sortedness of alts
mirrorRS :: RE -> RE
mirrorRS  =  homTrans $ HomTrans { falt = mkAlt . sort,
                                   fcat = mkCat . rollList . reverse,
                                   frep = Rep,
                                   fopt = Opt }

sigma         =  "ab"
maxSize       =  10
maxTreeSize   =  maxSize-1 --size of largest elements in the tree
sanes         =  saneREs sigma maxSize
katas         =  filter isKata sanes
kataObt       =  nubSort $ map kataGrade sanes
--norms         =  filter isNormal katas
--normsObt      =  nubSort $ map normalize kataObt
fuses         =  filter isFused katas
fusesObt      =  nubSort $ map fuse kataObt
promotes      =  filter isPromoted fuses
promotesObt   =  nubSort $ map promote fusesObt
--presses       =  filter isPressed fuses
--pressesObt    =  nubSort $ map (press) fusesObt
--facts         =  filter isRefactorized presses
--factsObt      =  nubSort $ map refactorize pressesObt 
shrunks       =  filter isShrunk promotes
shrunksObt    =  nubSort $ map shrink promotesObt
--stars         =  filter (isStellar) shrunks
--starsObt      =  nubSort $ map stellate shrunksObt
--autos         =  filter isAutomized stars
--autosObt      =  nubSort $ map automize starsObt
hitlist       =  hitListFunc shrunksObt

-- yes, could be stored in a file to make it faster, but too vulnerable to changes of normal form
hitListFunc :: [RE] -> [RE]
hitListFunc xs = [ y | ys <- groupOrder compRE xs, let m=pickMinList ys, y<-ys, size y>size m]

ehl           =  essence hitlist

essence :: [RE] -> [RE]
essence     =  nubBy mirrorAlphaEquiv . maximaBy (flip subExpr')

minima      =  concat [ [x | x <- xs, size x == m]
                      | xs <- quotBy (===) shrunksObt,
                        let m = size $ minimumBy cmpSize xs ]
            where
               cmpSize a b  =  compare (size a) (size b)

minima2      = map snd $ sortBy keyOrder $
               [ (s,x) | x <- shrunksObt, let s=size x,
                         s' <- take 1 $
                               [ size a | Just a<-[lookupPT x compRE pickMinList theTree]] ++ [maxSize],
                         s'==s ]

minima3 :: S.Set RE
minima3 = S.fromList minima2

createTree :: IO ()
createTree = createTreeFile sigma maxTreeSize

theTree :: RB RE
theTree         = unsafePerformIO $
                  catch (readFile (treeFileName sigma maxTreeSize) >>= (return . read))
                        (planB $ let t=poTree sigma maxTreeSize in writeTree sigma maxTreeSize t >> return t)

planB :: IO a -> IOException -> IO a
planB x _ = x

setCatalogueName :: String
setCatalogueName = "SET-CATALOGUE-"++sigma++"-"++show maxSize++".txt"

createSetCatalogue :: IO ()
createSetCatalogue  =  writeFile setCatalogueName $ show minima3

correctnessTest :: (RE->RE) -> [RE] -> IO()
correctnessTest f xs | null cexs
                     = putStrLn ("passed all " ++ show n ++ " tests")
                     | otherwise
                     = putStrLn ("tested " ++ show n ++ " regexps") >>
                       putStrLn (show (length cexs) ++ " counterexamples") >>
                       print cexs
    where n=length xs
          cexs = [ (t,u) | t<- xs, let u=f t,not(t===u)]

setCatalogue :: S.Set RE
{- setCatalogue     =  unsafePerformIO $
                    readFile setCatalogueName >>= (return . read)
-}
setCatalogue =  unsafePerformIO $
                catch (readFile setCatalogueName >>= (return . read))
                      (planB $ createSetCatalogue >> return minima3)

elemSetCatalogue :: RE -> Bool
elemSetCatalogue x = x `S.member` setCatalogue

minimize :: RE -> RE
minimize x | isJust found
             = fromJust found
             | size x == maxSize
             = x
             | otherwise
             = error $ "no minimal equivalent of " ++ show x ++
                       " found in " ++ treeFileName sigma maxTreeSize
             where
             found = lookupPT (fuse x) compRE pickMinList theTree

isMinimal :: RE -> Bool
isMinimal x  |  size x <= maxSize
             =  elemSetCatalogue x
             |  otherwise
             =  error $ "isMinimal "++show x++
                        " invalid as maxSize = "++show maxSize

-- uses the tree instead
hasMinimalSize :: RE -> Bool
hasMinimalSize x 
    | sx' < sx = False
    | otherwise =
          case lookupPT x' compRE pickMinList theTree of
              Just y -> size y==sx'
              Nothing -> maxTreeSize + 1==sx' || error "not found in tree"
    where
    x'  = fuse x
    sx' = size x'
    sx  = size x

createEHLs :: IO ()
createEHLs  =  mapM_ createEHLfor $
               [("ALT",isAlt), ("CAT",isCat), ("REP",isRep), ("OPT",isOpt)]

createEHLfor :: (String, RE->Bool) -> IO ()
createEHLfor (s,p)  =  writeFile ("EHL"++sigma++show maxSize++"-"++s++"S.txt") $
                       unlines $ map item xs
                    where
                       item x  =  x'++pad (w - length x')++" --min-> "++show (minimize x)
                               where
                                  x'  =  show x
                       xs      =  filter p ehl
                       w       =  maximum $ map (length . show) xs

censusName :: String
censusName  =  "CENSUS-"++sigma++"-"++show maxSize++".txt"

createCensus :: IO ()
createCensus  =  writeFile censusName $ censusText

census :: IO ()
census  =  putStr censusText

censusText :: String
censusText  =   headings ++ items
  where
  headings  =  "REs                 #   % min\n"
  items     =  unlines $ map censusItem $
                 [ ("sane",         sanes),
                   ("katas",        kataObt),
                   --("normal",       normsObt),
                   ("fused",        fusesObt),
                   ("promoted",     promotesObt),
                   --("pressed",      pressesObt),
                   --("refactorized", factsObt), 
                   ("shrunk",       shrunksObt),
                   --("stellar",      starsObt),
                   --("automized",    autosObt),
                   --("min. stellar", minima2), -- instead of minima
                   ("hitlist",      hitlist),
                   ("EHL",          ehl) ]

censusItem :: (String,[RE]) -> String
censusItem (s, xs)  =  s ++ pad (15 - length s) ++
                       pad (6 - length n') ++ n' ++
                       pad (6 - length (takeWhile (/= '.') p')) ++ p'                
                    where
                       m  =  length $ filter isMinimal xs
                       n  =  length xs
                       n' =  show n
                       p  =  m `asPercentageOf` n 
                       p' =  showFFloat (Just 1) p ""

pad :: Int -> String
pad n  =  replicate n ' '

starHeight     =  heightBy isRep

optHeight      =  heightBy isOpt

starOptHeight  =  heightBy (\x -> isRep x || isOpt x)

heightBy :: (RE -> Bool) -> RE -> Int
heightBy p x  =  fromEnum (p x) + innerHeight x
  where
  innerHeight Emp         =  0
  innerHeight Lam         =  0
  innerHeight (Sym _)     =  0
  innerHeight (Alt _ xs)  =  maximum (map (heightBy p) xs)
  innerHeight (Cat _ xs)  =  maximum (map (heightBy p) xs)
  innerHeight (Rep x)     =  heightBy p x
  innerHeight (Opt x)     =  heightBy p x

