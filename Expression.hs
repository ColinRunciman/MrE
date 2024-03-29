-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module Expression (
  RE(..), HomTrans(..), HomInfo(..), KatahomGeneral(..), Renaming,
  isEmp, isLam, isSym, isCat, isAlt, isRep, isOpt, unAlt, unCat, unOpt, unRep,
  alt, cat, opt, rep, mkAlt, mkCat, singleChar,
  nubMergeAltItems, concatCatItems,
  altSubseq, catSegment,
  ewp, alpha, alphaL, canonicalRE, isCanonical, eraseSigma,
  swa, fir, las, firAlt, firCat, lasAlt, lasCat, altInfo, catInfo,
  size, listSize, listAlpha,
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

-- RE Invariant:
-- (1) every Cat argument is plural and has no Cat items;
-- (2) every Alt argument is plural, and has no Alt or Opt items;
-- (3) every Alt argument is strictly ordered (by the derived RE ordering);
-- (4) no Opt argument satisfies ewp;
-- (5) no Rep argument is an Opt or Rep;
-- (6) no Emp or Lam occurs anywhere as a strict subexpression.
-- The following smart constructors establish this invariant.
-- TO DO: and that the Info is correct!
-- The invariant is formalised in Fuse: see Fuse.isNorm predicate

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
-- rep x        =  Rep (repbody x) -- for the alternative smart construction
rep (Rep x)  =  Rep x
rep (Opt x)  =  Rep x
rep x        =  Rep x

{- alternative smart construction, would do much of the heavy lifting
repbody :: RE -> RE
repbody x          | normalRepBody x -- to keep certificates, and avoid non-termination
                   = x
                   | swa x == alpha x
                   = alt (map Sym (alpha2String (alpha x)))
repbody (Alt i xs) = alt (map repbody xs)
repbody (Cat i xs) | ew i
                   = alt (map repbody xs)
repbody (Rep x) = x
repbody (Opt x) = repbody x
repbody x       = x

normalRepBody :: RE -> Bool
normalRepBody (Sym x)    = True
normalRepBody (Alt i xs) = ok RepCxt Normal (gr i)
normalRepBody (Cat i xs) = ok RepCxt Normal (gr i)
normalRepBody _          = False
-}

opt :: RE -> RE
opt Emp      =  Lam
opt x        |  ewp x
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
altInfo xs =  Info { gr = [(RepCxt,Minimal) | all isSym xs],
                     ew = any ewp xs, al = listAlpha xs,
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
catInfo xs =  Info { gr = [(RepCxt,Minimal) | all singleChar xs],
                     ew = all ewp xs, al = listAlpha xs,
                     fi = firCat xs, la = lasCat xs, sw = swCat xs,
                     si = listSize xs }

singleChar :: RE -> Bool
singleChar (Sym _)    = True
singleChar (Alt _ xs) = all isSym xs
singleChar _          = False

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

-- RE homomorphisms are conveniently defined in terms of a family
-- of generalised constructors.

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

-- erase all characters of a subalphabet
-- useful for sublang comparisons
eraseSigma :: Alphabet -> RE -> RE
eraseSigma sigma = es1 where
                   es1 x = if isEmptyAlpha(alpha x .&. sigma) then x
                           else es2 x
                   es2 (Sym _)    = Emp
                   es2 (Alt i xs) = alt $ map es1 xs
                   es2 (Cat i xs) = cat $ map es1 xs
                   es2 (Rep x)    = rep $ es2 x
                   es2 (Opt x)    = opt $ es2 x

-- A more general class of homomorphisms is applied with information about
-- context (type Cxt).

data KatahomGeneral a =  KatahomGeneral {
    kgemp :: a, kglam :: Cxt -> a, kgsym :: Char -> a,
    kgalt, kgcat :: Cxt -> Info -> [a] -> a,
    kgopt, kgrep :: Cxt -> a -> a }

katahomGeneral :: KatahomGeneral a -> Cxt -> RE -> a
katahomGeneral kh _ Emp        = kgemp kh
katahomGeneral kh c Lam        = kglam kh c
katahomGeneral kh c (Sym d)    = kgsym kh d
katahomGeneral kh c (Alt i xs) = kgalt kh c i (map (katahomGeneral kh nc) xs)
                                 where nc = if ew i then max c OptCxt else c
katahomGeneral kh c (Cat i xs) = kgcat kh c i (map (katahomGeneral kh NoCxt) xs)
katahomGeneral kh c (Rep x)    = kgrep kh c $ katahomGeneral kh RepCxt x
katahomGeneral kh c (Opt x)    = kgopt kh c $ katahomGeneral kh (max c OptCxt) x

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

-- In some transformations it is convenient to work directly with the lists of
-- Cat or Alt item REs.  These may or may not end up being re-assembled into
-- a Cat or Alt final result.  Typically a singleton result indicates the end
-- of the list-processing transformation.

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

-- Precondition: xs' is a subsequence of xs.
altSubseq :: RE -> [RE] -> RE
altSubseq (Alt i xs) xs'  =  altSubseq' $
                             claim ("subsequence of "++show xs) (`isSublistOf` xs) xs'
  where
  altSubseq' []   =  Emp
  altSubseq' [x]  =  x
  altSubseq' xs'  =  Alt (altGradedInfo (subAltCGMap $ gr i) xs') xs'
altSubseq _          _    =  error "altSegment of a noi?"

altGradedInfo :: CGMap -> [RE] -> Info
altGradedInfo cgm xs  |  null (gr info)
                      =  info { gr = cgm }
                      |  otherwise
                      =  info -- minimal attribute of a subalt is preserved
                         where
                         info = altInfo xs
-- Precondition: xs' is a segment of xs.
catSegment :: RE -> [RE] -> RE
catSegment (Cat i xs) xs'  =  catSegment' $
                              claim ("segment of "++show xs) (`isInfixOf` xs) xs'
  where
  catSegment' []   =  Lam
  catSegment' [x]  =  x
  catSegment' xs'  =  Cat (catGradedInfo (subCatCGMap $ gr i) xs') xs'
catSegment _          _    =  error "catSegment of a dog?"

catGradedInfo :: CGMap -> [RE] -> Info
catGradedInfo cgm xs  |  null (gr info)
                      =  info { gr = cgm }
                      |  otherwise
                      =  info
                         where
                         info = catInfo xs

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

-- Renaming invariant:
-- In any Renaming xs, both map fst xs and map snd xs have no duplicates

type Renaming = [(Char,Char)]

renameInfo :: Renaming -> Info -> Info
renameInfo ren i = i { fi= rename (fi i), la=rename (la i), al=rename (al i),
                       sw= rename (sw i) }
    where
    rename  =  string2Alpha . map (fromJust . flip lookup ren) . alpha2String

-- Alpha conversion.

rename :: Renaming -> RE -> RE
rename ren re  =  katahomGeneral
                    (KatahomGeneral {kgemp=Emp, kglam=const Lam,
                                     kgsym= \c -> Sym $ fromJust $lookup c ren,
                                     kgalt= \_ i xs->Alt (renameInfo ren i)(sort xs),
                                     kgcat= \_ i xs->Cat (renameInfo ren i) xs,
                                     kgrep= const Rep, kgopt= const Opt})
                    NoCxt re
