module SyntaxCatalogue where

import Info
import Data.List
import Data.Maybe
import OK
import Context
import Expression
import Comparison
import Generator
import Fuse
import PreOrderTrees
import qualified Data.Map.Strict as M
import System.IO.Unsafe(unsafePerformIO)
import Context
import List
import StarPromotion
import Alphabet

-- As an optional extra, in combination with the algebra-based transformations, one
-- can look up subREs with small alphabets in a catalogue of known minimal expressions,
-- hoping to find an equivalent.  This module defines a catalogue based on syntactic
-- lookup of expressions as distinct from language-based lookup (for which see Catalogue).
-- It uses finite maps indexed by the derived ordering on expressions, with matching
-- modulo renaming.

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

-- Whereas the semantic catalogue represents all languages expressible by REs of size
-- <= n, the syntactic catalogue is a finite map for which any retrieved value is
-- strictly smaller than the key by which it is found.

minimalEquiv :: RE -> Maybe RE
minimalEquiv re  |  n >= length theForest || size re>maxREsizeINtree
                 =  Nothing
                 |  otherwise
                 =  Just $ maybe (gradeMinimal re) (gradeMinimal.bwd) (M.lookup re' tree)
                    where
                      n = alphaLength alphabet
                      (maxREsizeINtree,tree) = theForest !! n
                      alphabet = alpha re 
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
poMap sigma n = buildMap $ filter ((== string2Alpha sigma) . alpha) $ concat $
                take (n+1) $ createGradedCarrier sigma beforeKP

buildMap :: [RE] -> Catalogue
buildMap xs = M.fromList $ qmap $ groupOrder compRE xs

-- create a quotient map from a list of equivalence classes
-- the identity case is removed to keep the quotient map small
qmap :: [[RE]] -> [(RE,RE)]
qmap []         =  []
qmap ([_] : xs) =  qmap xs
qmap ([] :xs)   =  error "found empty quotient list"
qmap (xs: xss)  =  [ (x,y) | let y=pickMinList xs, x<-xs, size x>size y, canonicalRE x ] ++
                   qmap xss 

createForest :: IO ()
createForest  =  mapM_ (uncurry createMapFile) [(sigmaFor n,sizeFor n) | n <- [1..maxSigmaSize]]

mbcA c i xs = altClosurePred (not . untreatable) minByCatalogueAltList c i xs
mbcC c i xs = catClosurePred (not . untreatable) minByCatalogueCatList c i xs

minByCatalogueAltList, minByCatalogueCatList :: RewRule
minByCatalogueAltList c i xs = minByList smartAlt c i xs
                               where smartAlt _ ys = beforeTrans c (alt ys)
minByCatalogueCatList c i xs = minByList smartCat c i xs
                               where smartCat _ ys = beforeTrans c (cat ys)

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
                                         size re'' < si i, let red=contextFunction c re'',
                                         Just re''' <- [minimalEquiv red] ]                                                 
    Just re' -> changed [unwrap c re']
    where re  = constr i xs
          rec = contextFunction c re
          unwrap RepCxt x |  isRep x
                          =  unRep x
                          |  otherwise
                          =  error $ show x ++ " is a non-* minimal equivalent of " ++
                                     show rec
          unwrap OptCxt x |  isOpt x
                          =  unOpt x
                          |  size x> si i
                          =  gradeMinimalCxt OptCxt re
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

minByCatalogue :: RE -> OK RE
minByCatalogue re  =  katahom minByCatalogueK NoCxt re
