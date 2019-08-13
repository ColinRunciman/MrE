module Catalogue where

-- This is a catalogue based on language lookup as distinct from expression lookup.
-- It uses preorder-trees indexed by compRE (or its refinements, e.g. compRE in a RepCxt)

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
     
minimalEquiv :: Cxt -> RE -> Maybe RE
minimalEquiv c re  |  n >= length theForest -- alphabet too large
                   =  Nothing
                   |  otherwise
                   =  case lookupPT (fwd re) compRE pickMinList tree of
                      Nothing -> if size re == maxREsizeINtree+1 then Just $ gradeMinimalCxt c re else Nothing
                      Just u  -> Just $ bwd u
                   where
                      n = alphaLength alphabet
                      (maxREsizeINtree,tree) = theForest !! n
                      alphabet = alpha re 
                      alphalist = alpha2String alphabet
                      fwd = rename $ zip alphalist ['a'..]
                      bwd = rename $ zip ['a'..] alphalist

-- theForest!!n is the size-bound and catalogue tree used for an alphabet of size n
theForest :: [(Int,RB RE)]
theForest = [(sizeFor n,tree n) | n <- [0..maxSigmaSize]]
            where
            tree 0  =  buildTree compRE [Emp,Lam]
            tree n  =  unsafePerformIO $
                       readFile (treeFileName (sigmaFor n) (sizeFor n)) >>= (return . (pruneTree (map gradeMinimal)). read)

-- max size of REs in tree-files for alphabet of size n
sizeFor :: Int -> Int
sizeFor n  =  [0,14,11,9,8]!!n

-- alphabet of stored REs for alphabet of size n
sigmaFor :: Int -> [Char]
sigmaFor n  =  take n ['a'..]

maxSigmaSize :: Int
maxSigmaSize  =  4

treeFileName :: String -> Int -> String
treeFileName sigma n = "semcatalogue/TREE-"++sigma++"-"++show n++".txt"

createTreeFile :: String -> Int -> IO()
createTreeFile sigma n = writeTree sigma n $ pruneTree ((:[]).pickMinList) $ poTree sigma n

writeTree :: String -> Int -> RB RE -> IO()
writeTree sigma n t = writeFile (treeFileName sigma n) $ show t                        

poTree :: String -> Int -> RB RE
poTree sigma n = buildTree compRE $ concat $ take (n+1) $ promoteA sigma

createForest :: IO ()
createForest  =  mapM_ (uncurry createTreeFile) [(sigmaFor n,sizeFor n) | n <- [1..maxSigmaSize]]

mbcA = altClosure minByCatalogueAltList
mbcC = catClosure minByCatalogueCatList
minByCatalogueAltList, minByCatalogueCatList :: RewRule
minByCatalogueAltList c i xs = minByList smartAlt c i xs
                               where smartAlt _ ys = beforeTrans c (alt ys)
minByCatalogueCatList c i xs = minByList smartCat c i xs
                               where smartCat _ ys = beforeTrans c (cat ys)

-- note: 2nd prize is: if r* is not in catalogue, but r is with minimum r'
-- then (r')* is minimal too [ otherwise, the minimum of (r')* is at most the size of r'
-- and must therefore be in the catalogue, but r*===(r')*, so we have a contradiction]
minByList :: (Info -> [RE] -> RE) -> Cxt -> Info -> [RE] -> OK [RE]
minByList constr c i xs =
    case minimalEquiv c rec of
    Nothing  -> list2OK xs [ [upgradeRE c Minimal rex] | c>=OptCxt, Just rex<- [minimalEquiv NoCxt re], size rex<si i]         
    Just re' -> changed [upgradeRE c Catalogued $ unwrap c re']  -- termination?!
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
minByCatalogueExtension = mkExtension mbcA mbcC beforeKP Catalogued

{- single place to change if previous level changes, though there's also promoteA -}
beforeKP::KataPred
beforeKP = promoteKP

beforeK :: Katahom
beforeK = khom beforeKP

beforeTrans :: Cxt -> RE -> RE
beforeTrans c r = valOf $ katahom beforeK c r

catalogueK :: Katahom
catalogueK = khom catalogueKP

catalogueKP :: KataPred
catalogueKP = target minByCatalogueExtension

catalogueP :: RecPred
catalogueP = kpred catalogueKP

Katahom { kalt = catalogueAltK, kcat = catalogueCatK } = catalogueK
-- pressK = Katahom { kalt = pressAltK, kcat = pressCatK, grade = Pressed }

catalogueH = mkHomTrans catalogueK
catalogue = mkTransform catalogueK

catalogueCxt :: Cxt -> RE -> OK RE
catalogueCxt = katahom catalogueK


-- minByCatalogueExtension = mkExtension minByCatalogueAltList minByCatalogueCatList fuseKP Catalogued


minByCatalogue :: RE -> OK RE
minByCatalogue re  =  catalogueCxt NoCxt re

