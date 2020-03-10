module Catalogue where

import Info
import Data.List
import List (nubSort)
import Data.Maybe
import OK
import Context
import Expression
import Comparison
import Generator
import Fuse
import StarPromotion
import PreOrderTrees
import qualified Data.Map.Strict as M
import System.IO.Unsafe(unsafePerformIO)
import Context
import Alphabet
import SyntaxCatalogue
-- import Debug.Trace

-- As an optional extra, in combination with the algebra-based transformations, one
-- can look up subREs with small alphabets in a catalogue of known minimal expressions,
-- hoping to find an equivalent.  This module defines a catalogue based on language
-- lookup as distinct from expression lookup (for which see SyntaxCatalogue).
-- It uses preorder-trees: they are indexed by a linear order on languages which
-- induces a corresponding pre-order on expressions.

minimalEquiv :: Cxt -> RE -> Maybe RE
minimalEquiv c re  |  -- trace (show re)
                      n >= length theForest     -- alphabet too large
                   =  Nothing
                   |  size re > 2 * sizeFor n   -- candidate key too large
                   =  Nothing
                   |  otherwise
                   =  case lookupPT cre compRE pickMinList tree of
                      Nothing -> if size re == maxREsizeINtree+1
                                 then Just $ gradeMinimalCxt c re
                                 else Nothing
                      Just u  -> Just $ bwd u
                   where
                      n = alphaLength alphabet
                      (maxREsizeINtree,tree) = theForest !! n
                      alphabet = alpha re
                      (cre,bwd) = canonicalIso re

-- maps a regexp to a an isomorphic canonical copy, and also return the inverse iso
-- properties:
-- let canonicalIso re = (re',f) then
-- (i) semcatNormal re'
-- (ii) forall re''. re'===re'' ===> re=== f re''
-- (iii) size re == size re'
-- (iv) forall re''. size re'' == size(f re'')
-- (v) if re==re' then f is the identity
-- note: one could include mirroring in case fir x and las x have different cardinality
-- however, that creates issues with size-preserving trafos
canonicalIso :: RE -> (RE, RE->RE)
canonicalIso x  |  isId
                =  (x,id)
                |  otherwise
                =  (fwd x,bwd)
              where
              isId     = isCanonical charList -- so that the iso is O(1)
              single   = swa x
              start    = fir x .\\. single
              finish   = las x .\\. fir x -- note: this will include single
              remain   = (alpha x .\\. fir x) .\\. las x
              charList = foldr1 (++) $ map alpha2String [single,start,finish,remain]
              fwd      = rename (zip charList ['a'..])
              bwd      = rename (zip ['a'..] charList)


-- theForest!!n is the size-bound and catalogue tree used for an alphabet of size n
theForest :: [(Int,RB RE)]
theForest = [(sizeFor n,tree n) | n <- [0..maxSigmaSize]]
            where
            tree 0  =  buildTree compRE [Emp,Lam]
            tree n  =  unsafePerformIO $
                       readFile (treeFileName (sigmaFor n) (sizeFor n)) >>= (return . (pruneTree (map gradeMinimal)). read)

-- max size of REs in tree-files for alphabet of size n
treeSizes :: [Int]
treeSizes = bigtreeSizes
-- treeSizes  =  [0,15,11,9,8]
bigtreeSizes = [0,16,12,10,9]

setSizes :: [Int]
setSizes = [ sizeT t | (_,t)<- theForest]

sizeFor :: Int -> Int
sizeFor n  =  treeSizes!!n

-- alphabet of stored REs for alphabet of size n
sigmaFor :: Int -> [Char]
sigmaFor n  =  take n ['a'..]

maxSigmaSize :: Int
maxSigmaSize  =  length treeSizes - 1

treeFileName :: String -> Int -> String
treeFileName sigma n = "semcatalogue/TREE-"++sigma++"-"++show n++".txt"

createTreeFile :: String -> Int -> IO()
createTreeFile sigma n = writeTree sigma n $
                         pruneTree ((:[]) . beforeTrans RootCxt . catalogueMinList) $
                         poTree sigma n

writeTree :: String -> Int -> RB RE -> IO()
writeTree sigma n t = writeFile (treeFileName sigma n) $ show t

poTree :: String -> Int -> RB RE
poTree sigma n = buildTree compRE $ filter semcatNormal $ filter ((== string2Alpha sigma) . alpha) $
                 concat $ take (n+1) $ createGradedCarrier sigma promoteKP

-- we can force a renaming that produces an RE satisfying semcatNormal
-- purpose: reduce the size of the catalogue when possible
semcatNormal :: RE -> Bool
semcatNormal x  =  tight (swa x) && tight (fir x) && tight (fir x .||. las x)

tight :: Alphabet -> Bool
tight a = 2^(alphaLength a)-1==a

createForest :: IO ()
createForest  =  mapM_ (uncurry createTreeFile)
                       [(sigmaFor n,sizeFor n) | n <- [1..maxSigmaSize]]

-- mbcA = altClosure minByCatalogueAltList
mbcA = minByCatalogueAltList
-- mbcC = catClosure minByCatalogueCatList
mbcC = minByCatalogueCatList
minByCatalogueAltList, minByCatalogueCatList :: RewRule
minByCatalogueAltList c i xs = minByList smartAlt c i xs
                               where smartAlt _ ys = beforeTrans c (alt ys)
minByCatalogueCatList c i xs = minByList smartCat c i xs
                               where smartCat _ ys = beforeTrans c (cat ys)

-- 2nd prize?  If r* is not in catalogue, but r is, with minimum equivalent r'
-- then (r')* is minimal too: otherwise, the minimum of (r')* is at most the size of r'
-- and must therefore be in the catalogue, but r*===(r')*, so we have a contradiction.

minByList :: (Info -> [RE] -> RE) -> Cxt -> Info -> [RE] -> OK [RE]
minByList constr c i xs =
    case minimalEquiv c rec of
    Nothing  -> list2OK xs [ [upgradeRE c Minimal rex]
                           | c>=OptCxt, Just rex<- [minimalEquiv NoCxt re], size rex<si i]
    Just re' -> changed [upgradeRE c SemCatMinimal $ unwrap c re']  -- termination?!
    where re  = constr i xs
          rec = contextFunction c re
          unwrap RepCxt x |  isRep x
                          =  unRep x
                          |  size x>si i
                          =  unOpt x
                          |  otherwise -- shrinks in size, so...
                          =  x -- no longer an error, but signalling x*===x?
          unwrap OptCxt x |  isOpt x
                          =  unOpt x
                          |  size x> si i
                          =  gradeMinimalCxt OptCxt re
                          |  otherwise
                          =  x
          unwrap NoCxt x  =  x

fakeIdExt :: Extension
fakeIdExt = mkExtension mbcA mbcC beforeKP SemCatMinimal

fakeId :: RE -> RE
fakeId = mkTransform $ khom $ target fakeIdExt

minByCatalogueExtension, mbcUnlimited :: Extension
mbcUnlimited = mkExtension mbcA mbcC beforeKP SemCatMinimal
minByCatalogueExtension = extensionCatalogue f $ mbcUnlimited
                          where
                          f n | n > maxSigmaSize
                              = 0
                              | otherwise
                              = 2 * sizeFor n

-- single place to change if previous level changes

beforeKP::KataPred
beforeKP = synCatalogueKP

beforeK :: Katahom
beforeK = khom beforeKP

beforeTrans :: Cxt -> RE -> RE
beforeTrans c r = valOf $ katahom beforeK c r

semCatalogueK :: Katahom
semCatalogueK = khom semCatalogueKP

semCatalogueKP :: KataPred
semCatalogueKP = target minByCatalogueExtension

semCatalogueP :: RecPred
semCatalogueP = kpred semCatalogueKP

Katahom { kalt = semCatalogueAltK, kcat = semCatalogueCatK } = semCatalogueK

semCatalogueH = mkHomTrans semCatalogueK

semcat  = extension2trafo minByCatalogueExtension
semcatU = extension2trafo mbcUnlimited

semCatalogueCxt :: Cxt -> RE -> OK RE
semCatalogueCxt = katahom semCatalogueK

minByCatalogue :: RE -> OK RE
minByCatalogue re  =  semCatalogueCxt NoCxt re
