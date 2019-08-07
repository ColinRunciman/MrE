module Info (
  Info(..), ExpInfo(..), CSet, Grade(..), Cxt(..), CGMap,
  emptyInfo, lamInfo, charInfo, newInfo, newInfo5, extractInfo,
  nocxt, nullcxt, noCxtCG, noCxtCG2, outerCxt, ok, lookupCGMap, upgradeCGMap ) where

import Alphabet

data Info = Info {gr :: CGMap, ew :: Bool, 
                  al :: Alphabet,
                  fi,la,sw :: CharSet, si :: Int} deriving Show

data ExpInfo = ExpInfo { graded::Grade, nullable::Bool, alphabet,firsts,lasts,singles :: CSet, expressionSize :: Int }
               deriving Show
                 

newtype CSet = CSet CharSet

c0 :: CSet
c0 = CSet emptySet

instance Show CSet where show (CSet x) = showSet x

emptyInfo, lamInfo :: ExpInfo
emptyInfo = ExpInfo { graded = Minimal, nullable=False,alphabet=c0,firsts=c0,lasts=c0,singles=c0,expressionSize=0 }

lamInfo   = emptyInfo { nullable=True }

lamListInfo :: Info -- info of empty list in a cat, size is set to -1 so that x and [x] have the same size
lamListInfo = Info { gr=[], ew=True, al=emptyAlphabet, fi=emptySet, la=emptySet, sw=emptySet, si= -1}

emptyListInfo :: Info -- info of empty list in an alt, size is set to -1 so that x and [x] have the same size
emptyListInfo = Info { gr=[], ew=False, al=emptyAlphabet, fi=emptySet, la=emptySet, sw=emptySet, si= -1}


release :: Bool -> CharSet -> CharSet
release True s  = s
release False _ = emptySet

charInfo :: Char -> ExpInfo
charInfo c = ExpInfo { graded=Minimal, nullable=False,alphabet=cs,firsts=cs,lasts=cs,singles=cs,expressionSize=1 }
             where cs=CSet $ embed c



extractInfo :: Cxt -> Info -> ExpInfo
extractInfo c i =
    ExpInfo { graded = lookupCGMap c (gr i),
              nullable=ew i, alphabet=CSet $ charSet(al i),
              firsts = CSet $ fi i, lasts=CSet $ la i, singles=CSet $ sw i,
              expressionSize = si i }

nocxt NoCxt i = i
nocxt _     i = i { graded = NoGrade }

nullcxt NoCxt i = i
nullcxt c     i = i { nullable=True }

noInfo :: Info
noInfo = Info {gr = [], ew = error "undefined ew in info",
               fi = error "undefined fi in info",
               al = error "undefined al in info",
               la = error "undefined la in info",
               sw = error "undefined sw in info",
               si = error "undefined size in info"}

newInfo :: Bool -> Info
newInfo b = noInfo { ew = b }

newInfo5 :: Bool -> CharSet -> CharSet -> Alphabet -> CharSet -> Info
newInfo5 b cs1 cs2 cs3 cs4 = noInfo { ew=b, fi=cs1, la=cs2, al=cs3, sw=cs4 }


-- We do not wish to distinguish info values under
-- comparison operations as we want them to be
-- neutral in RE comparisons.

instance Eq Info where
  _ == _  =  True

instance Ord Info where
  compare _ _  =  EQ

-- at least, also useful: size, derivatives, firsts?

data Cxt = RootCxt | NoCxt | EwpCxt | OptCxt | RepCxt
  deriving (Eq,Ord,Show)

data Grade = NoGrade | Kata | Fused | Promoted | Recognised | BottomCatalogued |
             Topshrunk | Shrunk | Pressed | Refactorized | 
             Catalogued | Stellar | Auto | Minimal
  deriving (Eq, Ord, Show)

type CGMap = [(Cxt,Grade)]

-- A contextual grading is a finite map, an unordered set of ordered pairs representing
-- an antitone function f: c1 <= c2 ==> f c1 >= f c2
-- the *representation* is injective:
-- if both (c1,g1) & (c2,g2) are in gr then g1==g2 <=> c1==c2

ok :: Cxt -> Grade -> CGMap -> Bool
ok c g cgm  =  any (\(c',g') -> c' >= c && g' >= g) cgm

outerCxt :: Bool -> Cxt -> Cxt
outerCxt _ c      |  c>=OptCxt
                  =  c
outerCxt True _   =  OptCxt
outerCxt False _  =  NoCxt

lookupCGMap :: Cxt -> CGMap -> Grade
lookupCGMap c cgm = maximum (NoGrade : [ g | (c',g) <- cgm, c' >=c] )

okInfo :: Cxt -> Grade -> Info -> Bool
okInfo c g i = ok c g (gr i)

upgradeCGMap :: Cxt -> Grade -> CGMap -> CGMap
upgradeCGMap c g cgm  |  ok c g cgm
                      =  cgm
                      |  otherwise
                      =  (c,g): [(c',g')|(c',g')<-cgm, c'<c && g'>g || c'>c && g'<g]

noCxtCG :: CGMap -> CGMap
noCxtCG []  = []
noCxtCG cgm = [(NoCxt,lookupCGMap NoCxt cgm)]

-- arises when an expression is a common subexpression of two expressions
noCxtCG2 :: CGMap -> CGMap -> CGMap
noCxtCG2 [] x = noCxtCG x
noCxtCG2 x [] = noCxtCG x
noCxtCG2 x y  = [(NoCxt,max(lookupCGMap NoCxt x)(lookupCGMap NoCxt y))]

upgradeInfo :: Cxt -> Grade -> Info -> Info
upgradeInfo c g i = i { gr = upgradeCGMap c g (gr i)}

