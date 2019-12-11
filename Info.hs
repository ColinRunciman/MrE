module Info (
  Info(..), ExpInfo(..), Grade(..), Cxt(..), CGMap,
  emptyInfo, lamInfo, charInfo, newInfo, newInfo5, extractInfo,
  nocxt, nullcxt, outerCxt, ok, lookupCGMap, upgradeCGMap, subAltCGMap, subCatCGMap ) where

import Alphabet

-- This module defines the field of memoised information in Alt and Cat REs, and
-- various functions for extracting or maintaining this information.

data Info = Info {gr :: CGMap, ew :: Bool, 
                  al :: Alphabet,
                  fi,la,sw :: Alphabet, si :: Int} deriving Show

data ExpInfo = ExpInfo { graded::Grade, nullable::Bool,
                         alphabet,firsts,lasts,singles :: Alphabet, expressionSize :: Int }
               deriving Show
                 
emptyInfo, lamInfo :: ExpInfo
emptyInfo = ExpInfo {
              graded = Minimal, nullable=False,
              alphabet=emptyAlpha,firsts=emptyAlpha,lasts=emptyAlpha,singles=emptyAlpha,
              expressionSize=0 }

lamInfo   = emptyInfo { nullable=True }

lamListInfo :: Info -- info of empty list in a cat, size is set to -1 so that x and [x] have the same size
lamListInfo = Info { gr=[], ew=True, al=emptyAlpha, fi=emptyAlpha, la=emptyAlpha, sw=emptyAlpha, si= -1}

emptyListInfo :: Info -- info of empty list in an alt, size is set to -1 so that x and [x] have the same size
emptyListInfo = Info { gr=[], ew=False, al=emptyAlpha, fi=emptyAlpha, la=emptyAlpha, sw=emptyAlpha, si= -1}

release :: Bool -> Alphabet -> Alphabet
release True s  = s
release False _ = emptyAlpha

charInfo :: Char -> ExpInfo
charInfo c = ExpInfo { graded=Minimal, nullable=False,alphabet=cs,firsts=cs,lasts=cs,singles=cs,expressionSize=1 }
             where cs=char2Alpha c

extractInfo :: Cxt -> Info -> ExpInfo
extractInfo c i =
    ExpInfo { graded = lookupCGMap c (gr i),
              nullable=ew i, alphabet=al i,
              firsts = fi i, lasts=la i, singles=sw i,
              expressionSize = si i }

nocxt NoCxt i = i
nocxt _     i = i { graded = Normal }

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

newInfo5 :: Bool -> Alphabet -> Alphabet -> Alphabet -> Alphabet -> Info
newInfo5 b cs1 cs2 cs3 cs4 = noInfo { ew=b, fi=cs1, la=cs2, al=cs3, sw=cs4 }

-- We do not wish to distinguish info values under comparison operations as
-- we want them to be neutral in RE comparisons.

instance Eq Info where
  _ == _  =  True

instance Ord Info where
  compare _ _  =  EQ

-- at least, also useful: size, derivatives, firsts?

data Cxt = RootCxt | NoCxt | EwpCxt | OptCxt | RepCxt
  deriving (Eq,Ord,Show)

data Grade = GruberGulan |
             Normal | Fused | Promoted |
             Stellar | Pressed | 
             SynCatMinimal | SemCatMinimal | Minimal
  deriving (Eq, Ord, Show, Enum)

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
lookupCGMap c cgm = maximum (Normal : [ g | (c',g) <- cgm, c' >=c] )

okInfo :: Cxt -> Grade -> Info -> Bool
okInfo c g i = ok c g (gr i)

upgradeCGMap :: Cxt -> Grade -> CGMap -> CGMap
upgradeCGMap c g cgm  |  ok c g cgm
                      =  cgm
                      |  otherwise
                      =  (c,g): [(c',g')|(c',g')<-cgm, c'<c && g'>g || c'>c && g'<g]

upgradeInfo :: Cxt -> Grade -> Info -> Info
upgradeInfo c g i = i { gr = upgradeCGMap c g (gr i)}

-- Which grade maps can we give to subcats of graded cats, subalts of graded alts?
-- Both context and grade may be affected

subAltCGMap :: CGMap -> CGMap
subAltCGMap m = [(subAltCxt c, subGrade g) | (c,g)<-m]
  where
  subAltCxt RootCxt = NoCxt
  subAltCxt x       = x

subCatCGMap :: CGMap -> CGMap
subCatCGMap m = [(NoCxt, subGrade g)|(c,g)<-m]

-- At one stage subcats and subalts were not considered for catalogue look-up,
-- but now they are so this function has become the identity.
subGrade :: Grade -> Grade
subGrade  =  id

