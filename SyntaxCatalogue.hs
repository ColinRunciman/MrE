module SyntaxCatalogue where

import Info
import Data.List
import Data.Maybe
import Context
import Expression
import Comparison
import Generator
import Fuse
--import TopologicalSearchTree
import PreOrderTrees
import qualified Data.Map.Strict as M
import System.IO.Unsafe(unsafePerformIO)
import Context
import List
import StarPromotion
import Alphabet

type Catalogue = M.Map RE RE

deBruijnify :: RE -> (RE, Renaming)
deBruijnify e | isCanonical cs
              = (e,re)
              | otherwise
              = (e'',[(x,z)|(x,y)<-re,(y',z)<-re', y==y'])
    where
    cs = alphaL e
    re = zip cs ['a'..]
    e' = rename re e
    (e'',re') = deBruijnify e'


-- for now, alternative would be to integrate a "readMinimal" when building the catalogue
gradeMinimal :: RE -> RE
gradeMinimal = gradeMinimalCxt NoCxt

gradeMinimalCxt :: Cxt -> RE -> RE
gradeMinimalCxt = katahomGeneral khgm
    where
    khgm = KatahomGeneral {
        kgemp = Emp, kglam = const Lam, kgsym = Sym,
        kgalt = \c i xs->Alt (i{gr=[(outerCxt (ew i) c,Minimal)]}) xs,
        kgcat = \c i xs->Cat (i{gr=[(outerCxt (ew i) c,Minimal)]}) xs,
        kgopt = \ _ x -> Opt x,
        kgrep = \ _ x -> Rep x}

-- slightly different, the size-out-by-1 argument does not apply here (really? second thoughts!)
-- compared to the semantic catalogue
-- therefore no Cxt argument
minimalEquiv :: RE -> Maybe RE
minimalEquiv re  |  n >= length theForest || size re>maxREsizeINtree
                 =  Nothing
                 |  otherwise
                 =  Just $ maybe (gradeMinimal re) (gradeMinimal.bwd) (M.lookup re' tree)
                    where
                      n = sizeSet alphabet
                      (maxREsizeINtree,tree) = theForest !! n
                      alphabet = charSet $ alpha re 
                      (re',ren) = deBruijnify re
                      bwd = rename [(x,y)|(y,x)<-ren]

-- theForest!!n is the size-bound and catalogue tree used for an alphabet of size n
-- small differences
theForest :: [(Int,Catalogue)]
theForest = [(sizeFor n,tree n) | n <- [0..maxSigmaSize]]
            where
            tree 0  =  M.empty
            tree n  =  unsafePerformIO $ fmap read $
                       readFile (mapFileName (sigmaFor n) (sizeFor n))

-- max size of REs in tree-files for alphabet of size n
sizeFor :: Int -> Int
sizeFor n  =  catalogueSizes!!n

catalogueSizes :: [Int]
catalogueSizes = [0,14,11,10]  -- 4-letter size 9 is not size reducing

-- alphabet of stored REs for alphabet of size n
sigmaFor :: Int -> [Char]
sigmaFor n  =  take n ['a'..]

maxSigmaSize :: Int
maxSigmaSize  =  length catalogueSizes - 1

-- slightly different to allow for both catalogues
mapFileName :: String -> Int -> String
mapFileName sigma n = "syncatalogue/MAP-"++sigma++"-"++show n++".txt"

createMapFile :: String -> Int -> IO()
createMapFile sigma n = writeMap sigma n $ poMap sigma n

writeMap :: String -> Int -> Catalogue -> IO()
writeMap sigma n t = writeFile (mapFileName sigma n) $ show t                        

poMap :: String -> Int -> Catalogue
poMap sigma n = buildMap $ filter ((==al').charSet.alpha) $ concat $ take (n+1) $ promoteA sigma
                where
                al' = fromList sigma

buildMap :: [RE] -> Catalogue
buildMap xs = M.fromList $ qmap $ groupOrder compRE xs

-- create a quotient map from a list of equivalence classes
-- the identity case is removed to keep the quotient map small
qmap :: [[RE]] -> [(RE,RE)]
qmap []         =  []
qmap ([_] : xs) =  qmap xs
qmap ([] :xs)   =  error "found empty quotient list"
qmap (xs: xss)  =  [ (x,y) | let y=pickMinList xs, x<-xs, size x>size y, canonicalRE x ] ++ qmap xss 

createForest :: IO ()
createForest  =  mapM_ (uncurry createMapFile) [(sigmaFor n,sizeFor n) | n <- [1..maxSigmaSize]]

{- obsolete
minimizeHom :: Hom (OK RE)
minimizeHom  =  Hom { hemp=(Emp,False), hlam=(Lam,False), hsym= \c -> (Sym c,False),
                      halt=malt, hcat=mcat, hrep=mrep, hopt=mopt }
-}
mbcA c i xs = altClosurePred (not . untreatable) minByCatalogueAltList c i xs
mbcC c i xs = catClosurePred (not . untreatable) minByCatalogueCatList c i xs

minByCatalogueAltList, minByCatalogueCatList :: RewRule
minByCatalogueAltList c i xs = minByList smartAlt c i xs
                               where smartAlt j ys = beforeTrans c (Alt j ys) -- smartAlt was Alt
minByCatalogueCatList c i xs = minByList smartCat c i xs
                               where smartCat j ys = beforeTrans c (Cat j ys) -- smartCat was Cat


-- idea: use untreatable for a cleverer altClosure/catClosure
untreatable :: RE -> Bool
untreatable x = n>= length theForest || size x>maxREsizeINtree
    where
    alphabet = alpha x
    n = alphaLength alphabet
    (maxREsizeINtree,tree) = theForest !! n

minByList :: (Info -> [RE] -> RE) -> Cxt -> Info -> [RE] -> OK [RE]
minByList constr c i xs =
    case minimalEquiv rec of
    Nothing  | c==NoCxt  -> unchanged xs
             | otherwise -> list2OK xs [ [re'''] | Just re'' <- [minimalEquiv re],
                                         size re''<si i, let red=contextFunction c re'',
                                         Just re''' <- [minimalEquiv red] ]                                                 
    Just re' -> changed [unwrap c re']  -- no need to upgrade re' as this is the syntactic catalogue
    where re  = constr i xs
          rec = contextFunction c re
          unwrap RepCxt x |  isRep x
                          =  unRep x
                          |  otherwise
                          =  error $ show x ++ " is a non-* minimal equivalent of " ++ show rec
          unwrap OptCxt x |  isOpt x
                          =  unOpt x
                          |  size x> si i
						  =  gradeMinimalCxt OptCxt re
                          -- was: =  upgradeRE OptCxt Minimal re
                          |  otherwise
                          =  x
          unwrap NoCxt x  =  x


minByCatalogueExtension :: Extension
minByCatalogueExtension = mkExtension mbcA mbcC beforeKP BottomCatalogued

minByCatalogueKP = target minByCatalogueExtension
minByCatalogueK  = khom minByCatalogueKP

syncat :: RE -> RE
syncat = mkTransform minByCatalogueK

-- new names to make changes easier
beforeKP :: KataPred
beforeKP = promoteKP

beforeK :: Katahom
beforeK = khom beforeKP

beforeTrans :: Cxt -> RE -> RE
beforeTrans c r = valOf $ katahom beforeK c r


-- minByCatalogueExtension = mkExtension minByCatalogueAltList minByCatalogueCatList fuseKP Catalogued

{- obsolete
mlist :: ([RE]->RE) -> ([RE]-> RE) -> [OK RE] -> OK RE
mlist plain fancy xs  =  case minimalEquiv re of
                         Nothing  -> (re,change)
                         Just re' -> (re', change || re'/=re)
                         where
                            change  =  any snd xs
                            xs'     =  map fst xs
                            re      =  if change then fancy xs' else plain xs'

msolo :: (RE->RE) -> (RE-> RE) -> OK RE -> OK RE
msolo plain fancy x  =  case minimalEquiv re of
                        Nothing  -> (re,change)
                        Just re' -> (re', change || re'/=re)
                        where
                           change  =  snd x
                           x'      =  fst x
                           re      =  if change then fancy x' else plain x'

malt :: [OK RE] -> OK RE
malt  =  mlist mkAlt fuseAlt

mcat :: [OK RE] -> OK RE
mcat  =  mlist mkCat fuseCat

mrep :: OK RE -> OK RE
mrep  =  msolo Rep fuseRep

mopt :: OK RE -> OK RE
mopt  =  msolo Opt fuseOpt
-}

minByCatalogue :: RE -> OK RE
minByCatalogue re  =  katahom minByCatalogueK NoCxt re

{-
try resFileName = do
  txt <- readFile resFileName
  let res = map read $ lines txt
  let res' = map wildCat res
  mapM_ display (zip res res')nonminimal11"

display :: (RE,RE) -> IO ()
display (re,re') | re == re'
                 = putStrLn $ show re ++ " (UNCHANGED)"
                 | otherwise
                 = putStrLn $ showWithSize re ++ " ---> " ++ showWithSize re'
  where
  showWithSize re = show re ++ " (" ++ show (size re) ++ ")"
-}

