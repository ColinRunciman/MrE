module Expression (
  RE(..), HomTrans(..), HomInfo(..), KatahomGeneral(..), Renaming,
  isEmp, isLam, isSym, isCat, isAlt, isRep, isOpt, unAlt, unCat, unOpt, unRep,
  alt, cat, opt, rep, mkAlt, mkCat,
  nubMergeAltItems, concatCatItems,
  altSubseq, catSegment,
  ewp, alpha, alphaL, alphaEquiv, canonicalRE, isCanonical,
  swa, fir, las, firAlt, firCat, lasAlt, lasCat, altInfo, catInfo,
  size, listSize,
  mirror, rename,
  homTrans, foldHomInfo, katahomGeneral,
  validate ) where

import List
import Data.List
import Data.Char
import Data.Maybe
import Data.Bits
import Info
import Function ((===>),claim)
import Alphabet

-- A data type of regular expressions with:
-- (1) smart constructors enforcing an invariant;
-- (2) construction predicates and selectors;
-- (3) various attributes for which memoised values are held;
-- (4) homomorphisms over expressions, and instances such as size; 
-- (5) a parser and a printer.

data RE = Emp
        | Lam
        | Sym Char
        | Alt Info [RE]
        | Cat Info [RE]
        | Rep RE
        | Opt RE
        deriving (Eq,Ord)

-- RE Invariant: (1) no Cat item occurs in a Cat argument list; (2) no Alt or Opt
-- item occurs in an Alt argument list; (3) Alt argument lists are strictly ordered
-- using the derived RE ordering (4) no Opt argment satisfies ewp (5) no Rep argument is
-- a Rep or an Opt (6) no Emp or Lam occurs anywhere as a strict subexpression.
-- The following smart constructors establish this invariant.
-- TO DO: and that the Info is correct!

alt :: [RE] -> RE
alt xs  |  any ewp xs && not (any ewp xs')
        =  opt (mkAlt xs')
        |  otherwise
        =  mkAlt xs'
  where
  xs'                 =  nubMergeMap altList xs
  altList (Alt _ ys)  =  ys
  altList Emp         =  []
  altList Lam         =  []
  altList (Opt x)     =  altList x
  altList z           =  [z]

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

rep :: RE -> RE
rep Emp      =  Lam
rep Lam      =  Lam
rep (Opt x)  =  Rep x
rep (Rep x)  =  Rep x
rep x        =  Rep x

opt :: RE -> RE
opt Emp  =  Lam
opt x    |  ewp x
         =  x
         |  otherwise
         =  Opt x

-- The actual construction of Alts and Cats is deferred to 'mkAlt' and 'mkCat'
-- which also compute values for memoised attributes in their Info fields.
-- These functions may be applied directly with the precondition that list
-- arguments are "flat" (no nested Alt or Cat) and for mkAlt strictly ordered.

mkAlt :: [RE] -> RE
mkAlt []   =  Emp
mkAlt [x]  =  x
mkAlt xs   =  Alt (altInfo xs) xs

altInfo :: [RE] -> Info
altInfo xs =  Info { gr = [], ew = any ewp xs, al = listAlpha xs,
                     fi = firAlt xs, la = lasAlt xs, sw = swAlt xs,
                     si = listSize xs }

-- First characters, last characters and single-word alphabets for alternatives.
firAlt, lasAlt, swAlt :: [RE] -> Alphabet
firAlt xs = unionA $ map fir xs
lasAlt xs = unionA $ map las xs
swAlt  xs = unionA $ map swa xs

-- Alphabets for both alternatives and concatenations.
listAlpha :: [RE] -> Alphabet
listAlpha xs = unionA $ map alpha xs

-- Sizes for both alternatives and concatenations.
listSize :: [RE] -> Int
listSize [x]    = size x
listSize (x:xs) = size x + 1 + listSize xs

mkCat :: [RE] -> RE
mkCat []  =  Lam
mkCat [x] =  x
mkCat xs  =  Cat (catInfo xs) xs

catInfo :: [RE] -> Info
catInfo xs =  Info { gr = [], ew = all ewp xs, al = listAlpha xs,
                     fi = firCat xs, la = lasCat xs, sw = swCat xs,
                     si = listSize xs } 

-- First characters, last characters and single-word alphabets for concatenations.
firCat, lasCat, swCat :: [RE] -> Alphabet      
firCat xs  =  foldr ficons emptyAlpha xs
              where
              ficons x a = if ewp x then fir x .|. a else fir x
lasCat xs  =  foldl lasnoc emptyAlpha xs
              where
              lasnoc a x = if ewp x then a .|. las x else las x
swCat  xs  =  fst $ foldr swcons (emptyAlpha, False) xs
              where
              -- Bool values in swcons pairs indicate whether
              -- a non-ewp item occurs in a recursive tail of xs
              swcons x (a,True)   =  if ewp x then (a,True)
                                     else (emptyAlpha, True)
              swcons x (a,False)  =  if ewp x then (swa x .|. a, False)
                                     else (swa x, True)

-- Take any freely constructed RE and give an invariant-respecting equivalent.
validate :: RE -> RE
validate  =  homTrans $ HomTrans {falt = alt, fcat = cat, frep = rep, fopt = opt}

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

-- The RE attributes with memoised values in the Info fields of Alts and Cats.

-- The possible first characters of RE.
fir :: RE -> Alphabet
fir Emp       = emptyAlpha
fir Lam       = emptyAlpha
fir (Sym c)   = char2Alpha c
fir (Alt i _) = fi i
fir (Cat i _) = fi i
fir (Rep x)   = fir x
fir (Opt x)   = fir x

-- The possible last characters of RE.
las :: RE -> Alphabet
las Emp       = emptyAlpha
las Lam       = emptyAlpha
las (Sym c)   = char2Alpha c
las (Alt i _) = la i
las (Cat i _) = la i
las (Rep x)   = las x
las (Opt x)   = las x

-- The empty-word property ("" in L)
ewp :: RE -> Bool
ewp Emp        =  False
ewp Lam        =  True
ewp (Sym _)    =  False
ewp (Alt i _)  =  ew i
ewp (Cat i _)  =  ew i
ewp (Rep _)    =  True
ewp (Opt _)    =  True

-- The characters c of the alphabet for which [c] in L.
swa :: RE -> Alphabet
swa Emp       = emptyAlpha
swa Lam       = emptyAlpha
swa (Sym c)   = char2Alpha c
swa (Alt i _) = sw i
swa (Cat i _) = sw i
swa (Rep x)   = swa x
swa (Opt x)   = swa x

-- The alphabet of symbols occurring in an RE.
alpha :: RE -> Alphabet
alpha Emp           =  emptyAlpha
alpha Lam           =  emptyAlpha
alpha (Sym c)       =  char2Alpha c
alpha x@(Alt i xs)  =  al i
alpha x@(Cat i xs)  =  al i
alpha (Rep x)       =  alpha x
alpha (Opt x)       =  alpha x

-- The size of an RE is the number of nodes in the expression tree obtained
-- when the Alts and Cats are expanded to binary chains of + and .
-- As the sizes of Emp and Lam are set to 0, expressions of the form
-- X? and 1+X have equal size.

size :: RE -> Int
size Emp       = 0
size Lam       = 0
size (Sym _)   = 1
size (Alt i _) = si i
size (Cat i _) = si i
size (Rep x)   = 1 + size x
size (Opt x)   = 1 + size x

grf :: RE -> CGMap
grf (Alt i _) = gr i
grf (Cat i _) = gr i
grf e         = error ("no CGMap for " ++ (show e))

-- RE homomorphisms are conveniently defined in terms of a family
-- of generalised constructors.

{-
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
-}

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

-- The alphabet of symbols occurring in an RE, in the order they occur first.
alphaL :: RE -> [Char]
alphaL = foldHomInfo $ HomInfo { hiemp = [], hilam = [], hisym = (:[]),
                                 hialt = const (nub . concat),
                                 hicat = const (nub . concat),
                                 hirep = id, hiopt = id }

-- Homomorphic RE -> RE transformations: always the identity for Emp, Lam and Sym
-- but with specific behaviours for Alt, Cat, Rep and Opt.

data HomTrans  =  HomTrans { falt, fcat :: [RE] -> RE, frep, fopt :: RE -> RE }

homTrans :: HomTrans -> RE -> RE
homTrans ht  =  foldHomInfo $ HomInfo { hiemp = Emp, hilam = Lam, hisym = Sym,
                                        hialt = const (falt ht), hicat = const (fcat ht),
                                        hirep = frep ht, hiopt = fopt ht }

mirror :: RE -> RE
mirror  =  homTrans $ HomTrans { falt = alt,
                                 fcat = cat . reverse,
                                 frep = Rep,
                                 fopt = Opt }

-- Flatten sequences one level down, but preserve singletons.
concatCatItems :: [RE] -> [RE]
concatCatItems [x] = [x]
concatCatItems xs  = conc xs id
  where
  conc (Emp:_) cont        =  [Emp]
  conc []  cont            =  cont []
  conc (Lam:xs) cont       =  conc xs cont
  conc (Cat _ xs:ys) cont  =  conc ys (cont . (xs++))
  conc (a:xs) cont         =  conc xs (cont . (a:))

-- Flatten alternatives one level down, but preserve singletons, removing options.
nubMergeAltItems :: [RE] -> [RE]
nubMergeAltItems [x] = [x]
nubMergeAltItems xs  = unions $ map altList xs
  where
  altList Emp        = []
  altList Lam        = []
  altList (Alt _ ys) = ys
  altList (Opt x)    = altList x
  altList y          = [y]

-- Info is language-correct, but not re-correct
-- mkAltI :: Info -> [RE] -> RE
-- mkAltI _ []  = Emp
-- mkAltI _ [x] = x
-- mkAltI i xs  = Alt (newInfo5 (ew i) (fi i) (la i) (al i) (sw i)){ si=listSize xs} xs

altGradedInfo :: CGMap -> [RE] -> Info
altGradedInfo cgm xs  =  (altInfo xs) { gr = cgm }

altSubseq :: RE -> [RE] -> RE
altSubseq (Alt i xs) xs'  =  altSubseq' $
                             claim ("subsequence of "++show xs) (`isSublistOf` xs) xs'
  where
  altSubseq' []   =  Emp
  altSubseq' [x]  =  x
  altSubseq' xs'  =  Alt (altGradedInfo (subAltCGMap $ gr i) xs') xs'
altSubseq _          _    =  error "altSegment of a noi?"


-- used when cat is created binary, with unknown size
-- mkCatI :: Info -> [RE] -> RE
-- mkCatI _ []   =  Lam
-- mkCatI _ [x]  =  x
-- mkCatI i xs   =  Cat i{si=listSize xs} xs

catGradedInfo :: CGMap -> [RE] -> Info
catGradedInfo cgm xs  =  (catInfo xs) { gr = cgm }

catSegment :: RE -> [RE] -> RE
catSegment (Cat i xs) xs'  =  catSegment' $
                              claim ("segment of "++show xs) (`isInfixOf` xs) xs'
  where
  catSegment' []   =  Lam
  catSegment' [x]  =  x
  catSegment' xs'  =  Cat (catGradedInfo (subCatCGMap $ gr i) xs') xs'
catSegment _          _    =  error "catSegment of a dog?"


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
                          (x:xs) -> rest s (((rep x:xs):a):as)
rest ('?':s) ((c:a):as) = case c of
                          []     -> wrong
                          (x:xs) -> rest s (((opt x:xs):a):as)
rest ('0':s) ((c:a):as) = rest s (((Emp:c):a):as)
rest ('1':s) ((c:a):as) = rest s (((Lam:c):a):as)
rest ('(':s) as         = rest s ([[]]:as)
rest (')':s) (a:as)     = case as of
                          [] -> if null as then (a2re a,')':s) else wrong
                                -- convenient to allow reading of tuples of REs
                          ((c:a'):as') -> rest s (((a2re a:c):a'):as')
rest (' ':s) as         = rest s as
rest (v  :s) ((c:a):as) = if isAlpha v then rest s (((Sym v:c):a):as)
                          else if null as then (a2re (c:a),v:s)
			 else wrong
			      
a2re :: [[RE]] -> RE
a2re = alt . reverse . map (cat . reverse)

wrong = error "unreadable RE"

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
                              where
                              composeAlt f g = f . ('+':) . g
  showsPrec n c@(Cat _ xs) |  n>catCxt
                           =  ('(' :) . showsPrec 0 c . (')':)
                           |  otherwise
                           =  foldr1 (.) (map (showsPrec catCxt) xs)
  showsPrec _ (Rep x)      =  showsPrec optCxt x . ('*' :)
  showsPrec _ (Opt x)      =  showsPrec optCxt x . ('?' :)

-- Canonical alphabets, alpha-equivalence and renaming.

isCanonical :: String -> Bool
isCanonical xs  =  isPrefixOf xs ['a'..]

canonicalRE :: RE -> Bool
canonicalRE = isCanonical . alphaL

alphaEquiv :: RE -> RE -> Bool
alphaEquiv x y = not $ null $ alphaRename [] x y

-- Renaming invariant:
-- In any Renaming xs, both map fst xs and map snd xs have no duplicates

type Renaming = [(Char,Char)]

-- Are two REs alpha-equivalent w.r.t. some extension of a given renaming?
-- N.B. There may be more than one such extension, hence the list result.

alphaRename :: Renaming -> RE -> RE -> [Renaming]
alphaRename r Emp         Emp          =  [r]
alphaRename r Lam         Lam          =  [r]
alphaRename r (Sym c)     (Sym d)      =  charMatch r c d
alphaRename r (Alt i1 xs) (Alt i2 ys)  =  [ r2
                                          | r1 <- infoMatch r i1 i2, compareLength xs ys==EQ,
                                            r2 <- multisetMatch r1 xs ys]
alphaRename r (Cat i1 xs) (Cat i2 ys)  =  [ r2
                                          | r1 <- infoMatch r i1 i2, compareLength xs ys==EQ,
                                            r2 <- sequenceMatch r1 xs ys]
alphaRename r (Rep x)     (Rep y)      =  alphaRename r x y
alphaRename r (Opt x)     (Opt y)      =  alphaRename r x y
alphaRename _ _ _                      =  []

-- Matching Info fields is a cheap pre-requisite for matching expressions.
-- Here the result is at most a singleton, but it could extend r, by including
-- new must-match bindings.

infoMatch :: Renaming -> Info -> Info -> [Renaming]
infoMatch r i1 i2  =
  [ r3
  | ew i1==ew i2 && si i1==si i2,
    r0 <- charListMatch r (alpha2String (fi i1 .&. la i1)) (alpha2String (fi i2 .&. la i2)),
    r1 <- charListMatch r0 (fif i1) (fif i2),
    r2 <- charListMatch r1 (laf i1) (laf i2),
    r3 <- charListMatch r2 (swf i1) (swf i2) ]
  where
  fif i = alpha2String $ fi i
  laf i = alpha2String $ la i
  swf i = alpha2String $ sw i
        
-- charListMatch is used to match lists of first/last/etc characters
-- To avoid combinatorial explosion it produces a list of at most one renaming.

charListMatch :: Renaming -> [Char] -> [Char] -> [Renaming]
charListMatch r cs ds = clm r cs ds
    where
    -- remove already matched chars from both sets, if singletons remain then extend match
    clm _          []  []   =  [r]
    clm _          []  _    =  []
    clm _          _   []   =  []
    clm _          [c] [d]  =  charMatch r c d
    clm []         cs  ds   =  [ r | compareLength cs ds==EQ]
    clm ((x,y):r') cs  ds   = 
      case (removeFromSet x cs, removeFromSet y ds) of
      (Nothing,Nothing)   -> clm r' cs ds   -- neither char in its respective set, ignore binding
      (Just cs',Just ds') -> clm r' cs' ds' -- both char in their sets, continue with reduced sets
      _                   -> []             -- one char is in its set, the other is not: fail

-- currently no assumption is made about ordering in the renaming itself
charMatch :: Renaming -> Char -> Char -> [Renaming]
charMatch r c d = cm r
    where
    cm []          =  [ (c,d): r ] -- both chars free, so we can extend renaming
    cm ((x,y):r')  =
       case (x==c,y==d) of
       (True,True)   -> [r]   -- both chars are already matched, keep r
       (False,False) -> cm r' -- (x,y) binding irrelevant for (c,d), continue without it
       _             -> []    -- conflicting binding, fail!

multisetMatch :: Renaming -> [RE] -> [RE] -> [Renaming]
multisetMatch r (x:xs) ys  =  [ r2 | (y,ys')<-itemRest ys,
                                r1 <- alphaRename r x y,
                                r2 <- multisetMatch r1 xs ys' ]
multisetMatch r []     []  =  [r]
multisetMatch r _      _   =  []

sequenceMatch :: Renaming -> [RE] -> [RE] -> [Renaming]
sequenceMatch r (x:xs) (y:ys)  =  [ r2 | r1<-alphaRename r x y,
                                         r2<-sequenceMatch r1 xs ys ]
sequenceMatch r []     []      =  [r]
sequenceMatch r _      _       =  [] 

renameInfo :: Renaming -> Info -> Info
renameInfo ren i = i { fi= rename (fi i), la=rename (la i), al=rename (al i),
                       sw= rename (sw i) }
    where
    rename  =  string2Alpha . map (fromJust . flip lookup ren) . alpha2String

--- ************* end of renaming operations *****************

-- KatahomGeneral: not currently used other than in Catalogue?
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



