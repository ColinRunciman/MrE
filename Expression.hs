module Expression where

import List
import Data.List
import Data.Char
import Data.Maybe
import Data.Bits
import Data.Monoid (mappend)
import Info
import Function ((===>),claim)
import Alphabet

-- A data type of regular expressions with: (1) construction predicates;
-- (2) a size measure; (3) smart constructors so == gives AC-equivalence;
-- (4) a parser; (5) a printer.

data RE = Emp
        | Lam
        | Sym Char
	| Alt Info [RE]
        | Cat Info [RE]
	| Rep RE
        | Opt RE
        deriving (Eq,Ord)

isEmp, isLam, isSym, isCat, isAlt, isRep, isOpt :: RE -> Bool

isEmp Emp        =  True
isEmp _          =  False

isLam Lam        =  True
isLam _          =  False

isSym (Sym _)    =  True
isSym _          =  False

isAlt (Alt _ _)  =  True
isAlt _          =  False

isCat (Cat _ _)  =  True
isCat _          =  False

isRep (Rep _)    =  True
isRep _          =  False

isOpt (Opt _)    =  True
isOpt _          =  False

isAtomic Emp     =  True
isAtomic Lam     =  True
isAtomic (Sym _) =  True
isAtomic _       =  False

unAlt :: RE -> [RE]
unAlt (Alt _ xs)  =  xs
unAlt x           =  error $ "unAlt "++show x

unCat :: RE -> [RE]
unCat (Cat _ xs)  =  xs
unCat x           =  error $ "unCat "++show x

unRep :: RE -> RE
unRep (Rep x)     =  x
unRep x           =  error $ "unRep "++show x

unOpt :: RE -> RE
unOpt (Opt x)     =  x
unOpt x           =  error $ "unOpt "++show x

(&&&) :: Ordering -> Ordering -> Ordering
(&&&) = mappend

sizeOrder :: RE -> RE  -> Ordering
sizeOrder x y = compare (size x)(size y) &&& compare x y

pickMin :: RE -> RE -> RE
pickMin x y = minimumBy sizeOrder [x,y]

pickMinList :: [RE] -> RE
pickMinList xs = minimumBy sizeOrder xs

-- RE homomorphisms are conveniently defined in terms of a family
-- of generalised constructors.

data Hom a = Hom { hemp,hlam :: a,
                   hsym      :: Char -> a,
                   halt,hcat :: [a]  -> a,
                   hrep,hopt :: a    -> a}

foldHom :: Hom a -> RE -> a
foldHom h Emp         =  hemp h
foldHom h Lam         =  hlam h
foldHom h (Sym s)     =  hsym h s
foldHom h (Alt _ xs)  =  halt h $ map (foldHom h) xs
foldHom h (Cat _ xs)  =  hcat h $ map (foldHom h) xs
foldHom h (Rep x)     =  hrep h $ foldHom h x
foldHom h (Opt x)     =  hopt h $ foldHom h x

data HomInfo a = HomInfo { hiemp, hilam :: a,
                           hisym        :: Char -> a,
                           hialt, hicat :: Info -> [a]  -> a,
                           hirep, hiopt :: a    -> a}

foldHomInfo :: HomInfo a -> RE -> a
foldHomInfo h Emp         =  hiemp h
foldHomInfo h Lam         =  hilam h
foldHomInfo h (Sym s)     =  hisym h s
foldHomInfo h (Alt i xs)  =  hialt h i $ map (foldHomInfo h) xs
foldHomInfo h (Cat i xs)  =  hicat h i $ map (foldHomInfo h) xs
foldHomInfo h (Rep x)     =  hirep h $ foldHomInfo h x
foldHomInfo h (Opt x)     =  hiopt h $ foldHomInfo h x

-- The size of an RE is the number of nodes in the expression tree obtained
-- when the Alts and Cats are expanded to binary chains of + and .
-- As the sizes of Emp and Lam are set to 0, expressions of the form
-- X? and 1+X have equal size.
oldSize :: RE -> Int
oldSize  =  foldHom $ Hom { hemp = 0, hlam = 0, hsym = const 1,
                         halt = \ss -> sum ss + (length ss - 1),
                         hcat = \ss -> sum ss + (length ss - 1),
                         hrep = (+ 1),
                         hopt = (+ 1) }

-- width of an expression: the number of its character occurrences
width :: RE -> Int
width = foldHom $ Hom { hemp =0, hlam = 0, hsym = const 1, halt = sum, hcat = sum, hrep = id, hopt = id }

-- The alphabet of symbols occurring in an RE.
alpha :: RE -> Alphabet
alpha Emp        =  emptyAlphabet
alpha Lam        =  emptyAlphabet
alpha (Sym c)    =  embedAlphabet c
alpha x@(Alt i xs) = al i
alpha x@(Cat i xs) = al i
alpha (Rep x)    = alpha x
alpha (Opt x)    = alpha x

expinfo :: RE -> ExpInfo
expinfo e = expinfoCxt NoCxt e

expinfoCxt c Emp = nocxt c emptyInfo
expinfoCxt c Lam = nocxt c lamInfo
expinfoCxt c (Sym d) = nullcxt c (charInfo d)
expinfoCxt c (Alt i _) = extractInfo c i
expinfoCxt c (Cat i _) = extractInfo c i
expinfoCxt c (Rep x) = nocxt c $ addEps (expinfoCxt RepCxt x)
expinfoCxt c (Opt x) = nocxt c $ addEps (expinfoCxt OptCxt x)

addEps :: ExpInfo -> ExpInfo
addEps i = i { nullable=True, expressionSize=expressionSize i+1 }

{-
alphaClaim i x = if al i /= oldalpha x then error ("bad boy: " ++ (show x) ++ "; old: " ++ oldalpha x ++ ", new: "++ al i) else True
-}

oldalpha  =  foldHom alphaHom 
alphaHom :: Hom [Char]
alphaHom = Hom { hemp = [], hlam = [], hsym = (: []),
                          halt = unions,
                          hcat = unions,
                          hrep = id,
                          hopt = id }

-- The alphabet of symbols occurring in an RE, in the order they occur first
alphaL :: RE -> [Char]
alphaL = foldHom $ alphaHom { halt = nub . concat, hcat = nub . concat }

-- homomorphic RE -> RE transformations.

data HomTrans  =  HomTrans { falt, fcat :: [RE] -> RE, frep, fopt :: RE -> RE }

homTrans :: HomTrans -> RE -> RE
homTrans ht  =  foldHom $ Hom { hemp = Emp, hlam = Lam, hsym = Sym,
                                halt = falt ht, hcat = fcat ht,
                                hrep = frep ht, hopt = fopt ht }

mirror :: RE -> RE
mirror  =  homTrans $ HomTrans { falt = alt,
                                 fcat = cat . reverse,
                                 frep = Rep,
                                 fopt = Opt }

 -- Recursive predicates RE -> Bool.  NB: not, in general, homomorphisms.

data RecPred =
    RecPred {
        empP :: Cxt -> Bool,
        lamP :: Cxt -> Bool,
        symP :: Cxt -> Char -> Bool,
        catP :: Cxt -> Info -> [RE] -> Bool,
        altP :: Cxt -> Info -> [RE] -> Bool,
        repP :: Cxt -> RE -> Bool,
        optP :: Cxt -> RE -> Bool
    }

acceptAll :: RecPred
acceptAll = RecPred {
    empP= const True,
    lamP= const True,
    symP= \_ _ ->     True,
    catP= \_ _ _ -> True,
    altP= \_ _ _ -> True,
    repP= \_ _ ->     True,
    optP= \_ _ ->     True
}



outerCxt :: Bool -> Cxt -> Cxt
outerCxt _ c      |  c>=OptCxt
                  =  c
outerCxt True _   =  OptCxt
outerCxt False _  =  NoCxt

-- NB the order of checking in && cases is important
-- so that *P predicates can assume checked components
-- more special predicates that check e.g. whether certain characters are present should use foldHomInfo
checkWith :: RecPred -> RE -> Bool
checkWith p = checkWith' RootCxt
    where
	checkWith' c Emp             =  empP p c
	checkWith' c Lam             =  lamP p c
	checkWith' c (Sym d)         =  symP p c d
	checkWith' c (Cat i xs)      =  all (checkWith' NoCxt) xs && catP p oc i xs
				        where oc = outerCxt (ew i) c 
	checkWith' c (Alt i xs)      =  all (checkWith' oc) xs && altP p oc i xs
				        where oc = outerCxt (ew i) c
	checkWith' c (Rep re)        =  checkWith' RepCxt re && repP p c re
        checkWith' c (Opt re)        =  checkWith' oc re && optP p c re
                                        where oc = max OptCxt c

-- the empty-word property ("" in L)
ewp :: RE -> Bool
ewp Emp        =  False
ewp Lam        =  True
ewp (Sym _)    =  False
ewp (Alt i _)  =  ew i
ewp (Cat i _)  =  ew i
ewp (Rep _)    =  True
ewp (Opt _)    =  True

-- allswps replacement
swa :: RE -> CharSet
swa Emp       = emptySet
swa Lam       = emptySet
swa (Sym c)   = embed c
swa (Alt i _) = sw i
swa (Cat i _) = sw i
swa (Rep x)   = swa x
swa (Opt x)   = swa x

-- the possible first characters of RE
fir :: RE -> CharSet
fir Emp       = emptySet
fir Lam       = emptySet
fir (Sym c)   = embed c
fir (Alt i _) = fi i
fir (Cat i _) = fi i
fir (Rep x)   = fir x
fir (Opt x)   = fir x

-- the possible last characters of RE
las :: RE -> CharSet
las Emp       = emptySet
las Lam       = emptySet
las (Sym c)   = embed c
las (Alt i _) = la i
las (Cat i _) = la i
las (Rep x)   = las x
las (Opt x)   = las x

grf :: RE -> CGMap
grf (Alt i _) = gr i
grf (Cat i _) = gr i
grf e         = error ("no CGMap for " ++ (show e))

-- memoized size
size :: RE -> Int
size Emp       = 0
size Lam       = 0
size (Sym _)   = 1
size (Alt i _) = si i
size (Cat i _) = si i
size (Rep x)   = 1 + size x
size (Opt x)   = 1 + size x

-- only for non-empty lists, really: plural lists
-- auxiliary routine for memoized size
listSize :: [RE] -> Int
listSize [x]    = size x
listSize (x:xs) = size x + 1 + listSize xs

-- the solo-word property ([s] in L)
swp :: Char -> RE -> Bool
swp s Emp         =  False
swp s Lam         =  False 
swp s (Sym t)     =  s==t
swp s (Alt _ xs)  =  any (swp s) xs
swp s (Cat i xs)  =  if ew i then any (swp s) xs else swpCat s xs
swp s (Rep x)     =  swp s x
swp s (Opt x)     =  swp s x

-- spec is executable, but not efficient
-- swpCat c xs == anyRest (swp s) ewp xs
-- we do assume here that list is not ewp, therefore no base case
swpCat :: Char -> [RE] -> Bool
swpCat c (x:xs)  =  if ewp x then swpCat c xs else swp c x && all ewp xs

-- computes the character set for which this RE has swp property,
-- needs only one RE traverse; useful for large alphabets
allswps :: RE -> CharSet
allswps Emp         =  emptySet
allswps Lam         =  emptySet 
allswps (Sym t)     =  embed t
allswps (Alt _ xs)  =  unionS (map allswps xs)
allswps (Cat i xs)  =  if ew i then unionS (map allswps xs) else allswpsCat xs
allswps (Rep x)     =  allswps x
allswps (Opt x)     =  allswps x

-- again, we do assume here that list is not ewp, therefore no base case
allswpsCat :: [RE] -> CharSet
allswpsCat (x:xs)  |  ewp x
                   =  allswpsCat xs
                   |  all ewp xs
                   =  swa x
                   |  otherwise
                   =  emptySet


anywhere :: (RE -> Bool) -> RE -> Bool
anywhere p x           |  p x
                       =  True
anywhere p (Alt _ xs)  =  any (anywhere p) xs
anywhere p (Cat _ xs)  =  any (anywhere p) xs
anywhere p (Rep x)     =  anywhere p x
anywhere p (Opt x)     =  anywhere p x
anywhere p _           =  False

{- OBSOLETE?
-- Using "smart constructors" cat and alt instead of Cat and Alt ensures
-- that as a minimum standard:
-- (1) Cat and Alt arguments must be plural lists;
-- (2) items in Cat arguments cannot be Cats;
-- (3) items in Alt arguments cannot be Alts.
-- (4) Alt arguments are sorted
-- (5) The empty-word property is memoized in a Boolean
--     first argument of Cat and Alt.

isStandard :: RE -> Bool
isStandard = checkWith standardP

standardP :: RecPred
standardP = acceptAll { altP=altStandardP, catP=catStandardP }

altStandardP _ i xs = plural xs && not (any isAlt xs) && ordered xs && ew i == any ewp xs

catStandardP _ i xs = plural xs && not (any isCat xs) && ew i == all ewp xs
-}

-- 'cat' and 'alt' do flattening and 'alt' orders components

cat :: [RE] -> RE
cat xs   |  any isEmp xs'
         =  Emp
         |  otherwise
         =  mkCat xs'
  where
  xs'                 =  concatMap catList xs
  catList (Cat _ ys)  =  ys
  catList Lam         =  []
  catList z           =  [z]

flatCat :: [RE] -> [RE]
flatCat []              = []
flatCat (Cat _ xs : ys) = flatCat (xs++ys)
flatCat (x: xs)         = x: flatCat xs

alt :: [RE] -> RE
alt xs = mkAlt $ unionsMulti $ map altList xs
  where
  altList (Alt _ ys)  =  ys
  altList z           =  [z]

-- flattening sequences one level down, preserving singletons (to preserve Grades)
concatCat :: [RE] -> [RE]
concatCat [x] = [x]
concatCat xs  = concCat xs id

concCat :: [RE] -> ([RE]->[RE]) -> [RE]
concCat (Emp:_) cont        =  [Emp]
concCat []  cont            =  cont []
concCat (Lam:xs) cont       =  concCat xs cont
concCat (Cat _ xs:ys) cont  =  concCat ys (cont . (xs++))
concCat (a:xs) cont         =  concCat xs (cont . (a:))

-- flattening alternatives one level down, preserving singletons, removing options
concatAlt :: [RE] -> [RE]
concatAlt [x] = [x]
concatAlt xs  = unions $ map altList xs
    where
    altList Emp        = []
    altList Lam        = []
    altList (Alt _ ys) = ys
    altList (Opt x)    = altList x
    altList y          = [y]

-- 'mkAlt' and 'mkCat' do NOT flatten and 'mkAlt' does NOT reorder components

mkAlt :: [RE] -> RE
mkAlt []   =  Emp
mkAlt [x]  =  x
mkAlt xs   =  Alt (altInfo xs) xs

altInfo :: [RE] -> Info
altInfo xs = (newInfo5 (any ewp xs)(firAlt xs)(lasAlt xs)(alp xs)(alsw xs)){si=listSize xs}

altGradedInfo :: CGMap -> [RE] -> Info
altGradedInfo cgm xs  =  (altInfo xs) { gr = cgm }

-- used only in one place in katahom machinery
mkAltCG :: CGMap -> [RE] -> RE
mkAltCG _ []   = Emp
mkAltCG _ [x]  = x
mkAltCG cgm xs = Alt (newInfo5 (any ewp xs) (firAlt xs) (lasAlt xs)(alp xs)(alsw xs)){gr=cgm, si=listSize xs} xs

alp :: [RE] -> Alphabet
alp xs = unionA $ map alpha xs

alsw :: [RE] -> CharSet
alsw xs = unionS $ map swa xs

-- Info is language-correct, but not re-correct
mkAltI :: Info -> [RE] -> RE
mkAltI _ []  = Emp
mkAltI _ [x] = x
mkAltI i xs  = Alt (newInfo5 (ew i) (fi i) (la i) (al i) (sw i)){ si=listSize xs} xs

altSubseq :: RE -> [RE] -> RE
altSubseq (Alt i xs) xs'  =  altSubseq' $
                             claim ("subsequence of "++show xs) (`isSublistOf` xs) xs'
  where
  altSubseq' []   =  Emp
  altSubseq' [x]  =  x
  altSubseq' xs'  =  Alt (altGradedInfo (gr i) xs') xs'
altSubseq _          _    =  error "altSegment of a noi?"

-- first characters of an alternative
firAlt, lasAlt :: [RE] -> CharSet
firAlt xs = unionS (map fir xs)
lasAlt xs = unionS (map las xs)

infoAlt :: RE -> RE -> Info
infoAlt x y = newInfo5 (ewp x || ewp y) (fir x .|. fir y) (las x .|. las y)
                       (alpha x .||. alpha y) (swa x .|. swa y)

-- assumption: neither x nor y is the empty language
infoCat :: RE -> RE -> Info
infoCat x y = newInfo5 (ewCat x y)(fiCat x y)(laCat x y)(alCat x y)(swCat x y)
{-
infoCat x y |  ewp x && ewp y
            =  newInfo4 True (nubMerge (fir x)(fir y)) (nubMerge (las x)(las y)) nalpha 
            |  ewp x
            =  newInfo4 False (nubMerge (fir x)(fir y)) (las y) nalpha
            |  ewp y
            =  newInfo4 False (fir x) (nubMerge (las x)(las y)) nalpha        
            |  otherwise
            =  newInfo4 False (fir x) (las y) nalpha
               where
               nalpha = nubMerge (alpha x)(alpha y)
               nsw    = swCat x y
-}

swCat :: RE -> RE -> CharSet
swCat x y = case (ewp x,ewp y) of
            (True,True)     -> swa x .|. swa y
            (True,False)    -> swa y
            (False,True)    -> swa x
            (False,False)   -> emptySet
fiCat :: RE -> RE -> CharSet
fiCat x y = case ewp x of
            True     -> fir x .|. fir y
            False    -> fir x

laCat x y = case ewp y of
            True     -> las x .|. las y
            False    -> las y

alCat x y = alpha x .||. alpha y
ewCat x y = ewp x && ewp y

mkCat :: [RE] -> RE
mkCat []  =  Lam
mkCat [x] =  x
mkCat xs  =  Cat (catInfo xs) xs

catInfo :: [RE] -> Info
catInfo xs = (foldr ctinf (newInfo5 True emptySet emptySet emptyAlphabet emptySet) xs) { si = listSize xs}
    where
    ctinf x i = newInfo5 (ewp x && ew i) nfi nla nal nsw
                where
                nfi = if ewp x then fir x .|. fi i else fir x
                nla = if ew i  then las x .|. la i else la i
                nal = alpha x .||. al i
                nsw = case (ewp x,ew i) of
                          (True,True)   -> swa x .|. sw i
                          (True,False)  -> sw i
                          (False,True)  -> swa x
                          (False,False) -> emptySet

catGradedInfo :: CGMap -> [RE] -> Info
catGradedInfo cgm xs  =  (catInfo xs) { gr = cgm }

-- used when cat is created binary, with unknown size
mkCatI :: Info -> [RE] -> RE
mkCatI _ []   =  Lam
mkCatI _ [x]  =  x
mkCatI i xs   =  Cat i{si=listSize xs} xs

{- Deprecated: use catSegment
-- used when this is a segment from a Cat which has this CGMap
mkCatFrom :: CGMap -> [RE] -> RE
mkCatFrom  _  [] = Lam
mkCatFrom _  [x] = x
mkCatFrom cgm xs = upgradeRE NoCxt (lookupCGMap NoCxt cgm) $ Cat (catInfo xs) xs
-}

catSegment :: RE -> [RE] -> RE
catSegment (Cat i xs) xs'  =  catSegment' $
                              claim ("segment of "++show xs) (`isInfixOf` xs) xs'
  where
  catSegment' []   =  Lam
  catSegment' [x]  =  x
  catSegment' xs'  =  Cat (catGradedInfo (noCxtCG $ gr i) xs') xs'
catSegment _          _    =  error "catSegment of a dog?"

-- we have a common segment of two REs
catSegment2 :: RE -> RE -> [RE] -> RE
catSegment2 (Cat j xs1) (Cat i xs2) xs'  =  catSegment' xs'
  where
  catSegment' []   =  Lam
  catSegment' [x]  =  x
  catSegment' xs'  =  Cat (catGradedInfo (noCxtCG2 (gr i)(gr j)) xs') xs'
catSegment2 _  _        _                =  error "catSegment of a dog?"

-- used only in one place in katahom machinery
mkCatCG :: CGMap -> [RE] -> RE
mkCatCG _ []   = Lam
mkCatCG _ [x]  = x
mkCatCG cgm xs = Cat (catInfo xs){gr=cgm} xs

-- Note: only correct if input list is Emp-free
firCat, lasCat :: [RE] -> CharSet
firCat = fi . catInfo
{-
firCat []      = []
firCat (x:xs)  |  ewp x
               =  nubMerge (fir x) (firCat xs)
               |  otherwise
               =  fir x
-}

lasCat = la . catInfo

-- REs are read and shown in a form as close to usual conventions
-- as ASCII permits.

instance Read RE where
  readsPrec _ s  = [rest s [[[]]]]

rest :: String -> [[[RE]]] -> (RE,String)
rest ""      (    a:as) = if null as then (a2re a,"")
                          else wrong
rest ('+':s) ((c:a):as) = if null c then wrong
			  else rest s (([]:c:a):as)
rest ('*':s) ((c:a):as) = case c of
                          []     -> wrong
                          (x:xs) -> rest s (((Rep x:xs):a):as)
rest ('?':s) ((c:a):as) = case c of
                          []     -> wrong
                          (x:xs) -> rest s (((Opt x:xs):a):as)
rest ('0':s) ((c:a):as) = rest s (((Emp:c):a):as)
rest ('1':s) ((c:a):as) = rest s (((Lam:c):a):as)
rest ('(':s) as         = rest s ([[]]:as)
rest (')':s) (a:as)     = case as of
                          [] -> if null as then (a2re a,')':s) else wrong -- smk changed from wrong to allow reading of tuples
			  ((c:a'):as') -> rest s (((a2re a:c):a'):as')
rest (' ':s) as         = rest s as
rest ('.':s) ((c:a):as) = rest s (((Sym '.':c):a):as) -- allow for '.' as special symbol
rest (v  :s) ((c:a):as) = if isAlpha v then rest s (((Sym v:c):a):as)
                          else if null as then (a2re (c:a),v:s)
			  else wrong
			      
a2re :: [[RE]] -> RE
a2re = alt . reverse . map (cat . reverse)

wrong = error "unreadable RE"

{-
instance Show RE where
  show Emp         =  "0"
  show Lam         =  "1"
  show (Sym c)     =  [c]
  show (Alt _ xs)  =  concat (intersperse "+" (map show xs))
  show (Cat _ xs)  =  concatMap (showBrackIf isAlt) xs
  show (Rep x)     =  showBrackIf (\x -> isCat x || isAlt x) x ++ "*"
  show (Opt x)     =  showBrackIf (\x -> isCat x || isAlt x) x ++ "?"

showBrackIf p x = ['(' | q] ++ show x ++ [')' | q] where q = p x
-}

altCxt,optCxt, catCxt :: Int
altCxt = 0
catCxt = 1
optCxt = 2

instance Show RE where
  showsPrec _ Emp          =  ('0' :)
  showsPrec _ Lam          =  ('1' :)
  showsPrec _ (Sym c)      =  (c:)
  showsPrec n a@(Alt _ xs) |  n>0
                           =  ('(' :) . showsPrec 0 a . (')':)
                           |  otherwise
                           =  foldr1 composeAlt (map (showsPrec altCxt) xs)
  showsPrec n c@(Cat _ xs) |  n>catCxt
                           =  ('(' :) . showsPrec 0 c . (')':)
                           |  otherwise
                           =  foldr1 (.) (map (showsPrec catCxt) xs)
  showsPrec _ (Rep x)      =  showsPrec optCxt x . ('*' :)
  showsPrec _ (Opt x)      =  showsPrec optCxt x . ('?' :)

composeAlt :: ShowS -> ShowS -> ShowS
composeAlt f g = f . ('+':) . g

-- canonical alphabets
isCanonical :: String -> Bool
isCanonical xs  =  isPrefixOf xs ['a'..]



canonicalRE :: RE -> Bool
canonicalRE = isCanonical . alphaL

-- alpha-equivalence over arbitrary alphabet
alphaEquiv :: RE -> RE -> Bool
alphaEquiv x y = not $ null $ alphaRename [] x y

-- renamings are lists xs of pairs such that
-- map fst xs and map snd xs have no duplicates
type Renaming = [(Char,Char)]

renameInfo :: Renaming -> Info -> Info
renameInfo ren i = i { fi= renameString (fi i), la=renameString (la i), al=renameAlpha(al i),
                       sw= renameString (sw i) }
    where
    renameString cs = fromList $  map (fromJust . flip lookup ren) $ enumerateSet cs
    renameAlpha  cs = embedSet $ fromList $  map (fromJust . flip lookup ren) $ enumerateSet (charSet cs)



----- ******** various renaming operations *********
-- charListMatch is used to match lists of first/last/etc characters
-- although charListMatch could enumerate renamings
-- it is limited to those we know must match anyway to avoid combinatorial explosion
-- so it produces a list of at most length 1
charListMatch :: Renaming -> [Char] -> [Char] -> [Renaming]
charListMatch r cs ds = clm r cs ds
    where
    -- remove already matched chars from both sets, if singletons remain then extend match
    clm _ [] []   = [r]
    clm _ [] _    = []
    clm _ _  []   = []
    clm _ [c] [d] = charMatch r c d
    clm [] cs ds  = [ r | compareLength cs ds==EQ]
    clm ((x,y):r') cs ds =
        case (removeFromSet x cs,removeFromSet y ds) of
            (Nothing,Nothing)   -> clm r' cs ds   -- neither character in its respective set, ignore binding
            (Just cs',Just ds') -> clm r' cs' ds' -- both characters in their sets, continue with reduced sets
            _                   -> []             -- one character is in its set, the other is not: fail

-- currently no assumption is made about ordering in the renaming itself
charMatch :: Renaming -> Char -> Char -> [Renaming]
charMatch r c d = cm r
    where
    cm [] = [ (c,d): r ] -- both chars were free, so we extend renaming r accordingly
    cm ((x,y):r') =
       case (x==c,y==d) of
           (True,True)   -> [r]   -- both chars are already matched, keep r
           (False,False) -> cm r' -- (x,y) binding irrelevant for (c,d), continue without it
           _             -> []    -- conflicting binding, fail!


-- this matches info parts that _must_ be matched
-- the result is at most a singleton, but:
-- (i) it could be empty, i.e. we know a match is impossible
-- (ii) the returned renaming could extend r, by including new must-match bindings
infoMatch :: Renaming -> Info -> Info -> [Renaming]
infoMatch r i1 i2  =
       [ r2 | ew i1==ew i2 && si i1==si i2,
              r0 <- charListMatch r (intersectSet (fif i1)(laf i1))(intersectSet (fif i2)(laf i2)),
              r1 <- charListMatch r (fif i1) (fif i2),
              r2 <- charListMatch r1 (laf i1) (laf i2)
       ]
       where
       fif i = enumerateSet $ fi i
       laf i = enumerateSet $ la i
        

-- essentially: are the terms alpha-equivalent w.r.t.
-- a renaming that extends the given renaming
alphaRename :: Renaming -> RE -> RE -> [Renaming]
alphaRename r Emp Emp = [r]
alphaRename r Lam Lam = [r]
alphaRename r (Sym c) (Sym d)  =  charMatch r c d
alphaRename r (Alt i1 xs) (Alt i2 ys)  =  [ r2 | r1 <- infoMatch r i1 i2, compareLength xs ys==EQ, r2<-multisetMatch r1 xs ys]
alphaRename r (Cat i1 xs) (Cat i2 ys)  =  [ r2 | r1 <- infoMatch r i1 i2, compareLength xs ys==EQ, r2<-sequenceMatch r1 xs ys]
alphaRename r (Rep x) (Rep y) = alphaRename r x y
alphaRename r (Opt x) (Opt y) = alphaRename r x y
alphaRename _ _ _             = []

multisetMatch :: Renaming -> [RE] -> [RE] -> [Renaming]
multisetMatch r (x:xs) ys = [ r2 | (y,ys')<-itemRest ys,
                              r1 <- alphaRename r x y,
                              r2 <- multisetMatch r1 xs ys']
multisetMatch r []     [] = [r]
multisetMatch r _      _  = []

sequenceMatch :: Renaming -> [RE] -> [RE] -> [Renaming]
sequenceMatch r (x:xs) (y:ys) =  [ r2 | r1<-alphaRename r x y,
                                        r2<-sequenceMatch r1 xs ys ]
sequenceMatch r []     []     =  [r]
sequenceMatch r _      _      =  [] 
--- ************* end of renaming operations *****************


upgradeRE :: Cxt -> Grade -> RE -> RE
upgradeRE c g (Alt i xs) =  Alt i{ gr = upgradeCGMap c g (gr i)} xs
upgradeRE c g (Cat i xs) =  Cat i{ gr = upgradeCGMap c g (gr i)} xs
upgradeRE _ _ x          =  x

-- makes the assertion that the top of the term is Minimal
-- assuming the subterms are labelled anyway
-- has to go below Rep/Opt as this is an asserion with a stronger context
minimalAssert :: RE -> RE
minimalAssert (Rep x) = Rep (upgradeRE RepCxt Minimal x)
minimalAssert (Opt x) = Opt (upgradeRE OptCxt Minimal x)
minimalAssert x       = upgradeRE NoCxt Minimal x

gradeOfCxt :: Cxt -> RE -> Grade
gradeOfCxt _ Emp        =  NoGrade -- not supposed to occur in subexpressions
gradeOfCxt _ Lam        =  NoGrade -- ditto
gradeOfCxt _ (Sym _)    =  Minimal
gradeOfCxt c (Alt i _)  =  lookupCGMap c (gr i)
gradeOfCxt c (Cat i _)  =  lookupCGMap c (gr i)
gradeOfCxt c (Rep x)    =  minimum $ [ NoGrade | c==RepCxt] ++ [gradeOfCxt RepCxt x]
gradeOfCxt c (Opt x)    =  minimum $ [ NoGrade | c>=OptCxt || ewp x] ++ [gradeOfCxt OptCxt x]

-- note: (lastPair re == (False,[]))==(re===Emp)
-- and:  (lastPair re == (True,[]))==(re===Lam)
lastPair :: RE -> (Bool,[Char]) -- the Bool is True iff the RE has ewp
lastPair = foldHom $ Hom {
    hemp = (False,[]),
    hlam = (True,[]),
    hsym = \c->(False,[c]),
    halt = \xs->(or (map fst xs),unions $ map snd xs),
    hcat = foldr addPair (True,[]),
    hrep = mkTrue,
    hopt = mkTrue }

mkTrue :: (Bool,a) -> (Bool,a)
mkTrue (_,x) = (True,x)

addPair :: (Bool,[Char]) -> (Bool,[Char]) -> (Bool,[Char])
addPair (False,[]) _       = (False,[])
addPair _ (False,xs)       = (False,xs)
addPair (tag,xs) (True,ys) = (tag, nubMerge xs ys)

lasts :: RE -> [Char]
lasts = snd . lastPair

-- set of two-letter substrings of words of the language
-- with linearised alphabet this is used for creating the Glushkov-automaton
-- here, we can take it as an invariant of a language
follow :: RE -> [[Char]]
follow Emp     = []
follow Lam     = []
follow (Sym _) = []
follow (Alt i xs) = unions $ map follow xs
follow (Cat i xs) = followS xs
                    where
                    followS [] = []
                    followS [x] = follow x
                    followS (x:y:ys) = follow x `nubMerge` [[v,w]|v<-enumerateSet(las x), w<-enumerateSet(fir y)] `nubMerge`
                                       followS (y:ys)
follow (Rep x)    = follow x `nubMerge` [[v,w]|v<-enumerateSet(las x), w<-enumerateSet(fir x)]
follow (Opt x)    = follow x


-- removes all grading from an RE; useful for testing purposes
degrade :: RE -> RE
degrade = foldHomInfo $ HomInfo {
    hiemp = Emp, hilam = Lam, hisym = Sym,
    hialt = \i xs -> Alt i{gr=[]} xs,
    hicat = \i xs -> Cat i{gr=[]} xs,
    hirep=Rep, hiopt=Opt }

-- KatahomGeneral: not currently used
data KatahomGeneral a =  KatahomGeneral {
    kgemp :: a, kglam :: Cxt -> a, kgsym :: Char -> a,
    kgalt, kgcat :: Cxt -> Info -> [a] -> a,
    kgopt, kgrep :: Cxt -> a -> a }

-- note: always goes deep, so not good for ping-ponging
katahomGeneral :: KatahomGeneral a -> Cxt -> RE -> a
katahomGeneral kh _ Emp        = kgemp kh
katahomGeneral kh c Lam        = kglam kh c
katahomGeneral kh c (Sym d)    = kgsym kh d
katahomGeneral kh c (Alt i xs) = kgalt kh c i (map (katahomGeneral kh c) xs)
                                 where nc = if ew i then max c OptCxt else c
katahomGeneral kh c (Cat i xs) = kgcat kh c i (map (katahomGeneral kh NoCxt) xs)
katahomGeneral kh c (Rep x)    = kgrep kh c $ katahomGeneral kh RepCxt x
katahomGeneral kh c (Opt x)    = kgopt kh c $ katahomGeneral kh (max c OptCxt) x

-- renaming function, for active alpha conversion
-- important: this is only sound for injective renamings
rename :: Renaming -> RE -> RE
rename ren re  =  katahomGeneral
                  (KatahomGeneral {kgemp=Emp, kglam=const Lam, kgsym= \c -> Sym $ fromJust $lookup c ren,
                                   kgalt= \_ i xs->Alt (renameInfo ren i)(sort xs),
                                   kgcat= \_ i xs->Cat (renameInfo ren i) xs, kgrep= const Rep, kgopt= const Opt}) NoCxt re

grading :: RE -> String
grading = katahomGeneral
                  (KatahomGeneral {kgemp="", kglam=const "", kgsym= const "",
                                   kgalt= altOrCatGrading, kgcat= altOrCatGrading,
                                   kgrep= const id, kgopt= const id}) NoCxt
  where
  altOrCatGrading c i xs = gradeChar (lookupCGMap c (gr i)):
                           if any (not . null) xs then "("++concat (intersperse "," $ filter (not . null) xs)++")"
                           else ""

gradeChar :: Grade -> Char
gradeChar g = case g of
              {NoGrade -> 'n'; Kata -> 'k'; Fused -> 'f' ; Catalogued -> 'c'; Pressed -> 'p' ; Refactorized -> 'r';
               Shrunk -> 's'; Stellar -> '*'; Auto -> 'a' ; Minimal -> 'm'; Promoted -> 'o'; BottomCatalogued -> 'b';
               Topshrunk -> 't' }


subalts, subcats :: [RE]->[([RE],[RE]->[RE])]
subcats os = [(ys,\ys'->xs++ys'++zs)| m<-[2..n-1], (xs,ys,zs)<-segPreSuf m os] where n=length os

subalts os = [ (xs,\xs'->nubMerge (nubSort xs') ys) | (xs,ys)<-powerSplits os, plural xs ]

subaltsPred, subcatsPred :: (RE->Bool) -> [RE]->[([RE],[RE]->[RE])]
subcatsPred p os = [(ys,\ys'->xs++ys'++zs)| (xs,ys,zs)<-segmentsPred p os, plural ys, not(null xs && null ys)]

subaltsPred p os = [ (xs,\xs'->nubMerge (nubSort xs') ys) | (xs,ys)<-powerSplitsPred p os, plural xs ]

subaltsLPred, subcatsLPred :: ([RE]->Bool) -> [RE]->[([RE],[RE]->[RE])]
subcatsLPred p os = [(ys,\ys'->xs++ys'++zs)| (xs,ys,zs)<-segmentsLPred p os, plural ys, not(null xs && null ys)]

subaltsLPred p os = [ (xs,\xs'->nubMerge (nubSort xs') ys) | (xs,ys)<-powerSplitsLPred p os, plural xs ]



