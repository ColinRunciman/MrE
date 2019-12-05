module Context (Extension(..), KataRE, Katahom(..), KataPred(..), RecPred(..), RewRule,
  okGradeCxt, gradeMinimal, gradeMinimalCxt, minimalAssert, upgradeRE, contextFunction,
  mkExtension, mkHomTrans, mkTransform,
  altClosure, catClosure, altClosurePred, catClosurePred,
  kataAlt, kataCat, kataOpt, kataliftAlt, kataGrade, kataGradeH, kataGradeKP,
  isKata, katahom, tpr, trg, altSizeBound, catSizeBound, checkWith, degradeTop,
  extensionLtd, extensionCatalogue) where

import Alphabet
import List
import Info
import Expression
import Function
import OK
import Data.Maybe
import Data.List

-- Assumes *any* transformation can improve a Rep-body that
-- is a Rep or an Opt, or an Opt-body that is an Opt
-- NB there is an issue of division of responsibilities
-- between child and parent --- eg in Rep (Rep e) which
-- Rep vanishes?!
-- only used in Generator at the moment
okGradeCxt :: Grade -> Cxt -> RE -> Bool
okGradeCxt g c Emp        =  c==NoCxt   -- || g==Standard
okGradeCxt g c Lam        =  c==NoCxt   -- || g==Standard
okGradeCxt _ _ (Sym _)    =  True
okGradeCxt g c (Alt i _)  =  ok c g (gr i)
okGradeCxt g c (Cat i _)  =  ok c g (gr i) && (not (ew i) || c/= RepCxt)
okGradeCxt g c (Rep e)    =  c < RepCxt && okGradeCxt g RepCxt e && not (ewp e)
okGradeCxt g c (Opt e)    =  c < OptCxt && okGradeCxt g OptCxt e && not (ewp e)

type RewRule = Cxt -> Info -> [RE] -> OK [RE]
data Katahom = Katahom { kalt, kcat  :: RewRule, grade :: Grade }

-- modifies the alt-rule of a Katahom by evaluating the elements in the list first
-- then flattening the results, then applying the rule, then flatten the result
altRule :: Katahom -> RewRule
altRule kh c i xs  |  not (plural xs')
                   =  xso
                   |  otherwise
                   =  okmap nubMergeAltItems $ kalt kh c ni `app` xso
                      where
                      xso = kataliftAltSafe (katahom kh c) xs
                      xs' = valOf xso
                      ni  = if hasChanged xso then altInfo xs' else i

kataliftAltSafe :: (RE->OK RE) -> [RE] -> OK [RE]
kataliftAltSafe f xs = potentialChange (/=xs) $ (okmap nubMergeAltItems $ katalift f xs)

altRuleOK :: RewRule -> RewRule
altRuleOK r c i xs = okmapIf nubMergeAltItems (r c i xs)

-- dual to altRule
catRule :: Katahom -> RewRule
catRule kh c i xs  |  not (plural xs')
                   =  xso 
                   |  otherwise
                   =  okmap concatCatItems $ kcat kh c ni `app` xso
                      where
                      xso = kataliftCatSafe (katahom kh NoCxt) xs
                      xs' = valOf xso
                      ni  = if hasChanged xso then catInfo xs' else i

kataliftCatSafe :: (RE->OK RE) -> [RE] -> OK [RE]
kataliftCatSafe f xs = potentialChange (/=xs) $ (okmap concatCatItems $ katalift f xs)

catRuleOK :: RewRule -> RewRule
catRuleOK r c i xs = okmapIf concatCatItems $ r c i xs

-- untrusting katahom, i.e. it does not assume that the rules preserve standardness
-- or that the original RE was standard
-- it does trust existing grading though

katahom :: Katahom -> Cxt -> RE -> OK RE
katahom kh RootCxt x       =  katahom kh NoCxt x -- to avoid confusing trafos with unfamiliar context
katahom kh c Emp           =  unchanged Emp
katahom kh c Lam           =  guardOK (c>=OptCxt) (changed Emp) (unchanged Lam)
katahom kh c (Sym d)       =  unchanged (Sym d)
katahom kh c x@(Alt i xs)  =  okmap (reOpt c x) $ eitherAltCat mkAltCG nc (grade kh) (gr i) x (altRule kh nc i xs)
                              where nc  = if ew i then max c OptCxt else c
katahom kh c x@(Cat i xs)  =  okmap (reOpt c x) $ eitherAltCat mkCatCG nc (grade kh) (gr i) x (catRule kh nc i xs)
                              where nc  = if ew i then max c OptCxt else c
katahom kh c (Rep x)       =  eitherRepOpt (c==RepCxt) True (katahom kh RepCxt x)
katahom kh c (Opt x)       =  eitherRepOpt (c>=OptCxt) False (katahom kh (max OptCxt c) x)

reOpt ::  Cxt -> RE -> RE -> RE
reOpt c old new  |  c>=OptCxt
                 =  new
                 |  ewp old && not(ewp new)
                 =  if isEmp new then Lam else Opt new
                 |  otherwise
                 =  new

eitherAltCat :: (CGMap->[RE]->RE) -> Cxt -> Grade -> CGMap -> RE -> OK [RE] -> OK RE
eitherAltCat cstr c g m xold xso  |  ok c g m
                                  =  unchanged xold  -- without ever evaluating xso
                                  |  not (plural xs)
                                  =  okmap (cstr m) xso
                                  |  all isSym xs    -- all subs are symbols, so minimal
                                  =  okmap (cstr [(RepCxt,Minimal)]) xso
                                  |  hasChanged xso  -- we build a new expression
                                  =  okmap (cstr [(c,g)]) xso
                                  |  otherwise
                                  =  okmap (cstr (upgradeCGMap c g m)) xso
                                     where
                                     xs    =  valOf xso

eitherRepOpt :: Bool -> Bool -> OK RE -> OK RE
eitherRepOpt redundant inRep body  |  redundant
                                   =  changed x
                                   |  isEmp x
                                   =  changed Lam
                                   |  inRep
                                   =  okmap Rep body
                                   |  ewp x
                                   =  changed x
                                   |  otherwise
                                   =  okmap Opt body
                                      where
                                      x = valOf body

mkAltCG :: CGMap -> [RE] -> RE
mkAltCG _ []   = Emp
mkAltCG _ [x]  = x
mkAltCG cgm xs = Alt (altInfo xs){gr=cgm} xs

mkCatCG :: CGMap -> [RE] -> RE
mkCatCG _ []   = Lam
mkCatCG _ [x]  = x
mkCatCG cgm xs = Cat (catInfo xs){gr=cgm} xs

-- input is set-like 
total :: [Char] -> RE
total xs = upgradeRE RepCxt Minimal (mkAlt (map Sym xs))

-- specific katalifts for Cats and Alts
kataliftAlt, kataliftCat, katalift1Alt :: (RE -> OK RE) -> [RE] -> OK [RE]
kataliftAlt f xs  = okmapIf nubMergeAltItems $ katalift f xs
kataliftCat f xs  = okmapIf concatCatItems   $ katalift f xs
katalift1Alt f xs = okmapIf nubMergeAltItems $ katalift1 f xs

-- generic creation of a HomTrans
mkHomTrans :: Katahom -> HomTrans
mkHomTrans kh = HomTrans { falt = foralt, fcat = forcat, frep = forrep, fopt = foropt }
    where
    foralt xs = valOf $ katahom kh NoCxt $ alt xs
    forcat xs = valOf $ katahom kh NoCxt $ cat xs
    forrep x  = valOf $ katahom kh NoCxt (Rep x)
    foropt x  = valOf $ katahom kh NoCxt (Opt x)

-- Bootstrapping Katahoms -------------------------------------------------------------
-- for documentary purposes
type FromRE = RE -- source of boilerplate
type ToRE   = RE -- target of boilplate
type KataRE = RE -- REs that are of Kata grade

data KataPred = KataPred { khom :: Katahom, kpred :: RecPred }

data Extension = Extension { source, target   :: KataPred,
                             altStep, catStep :: RewRule }
    
grd :: KataPred -> Grade
grd = grade . khom

-- add rewrite rules on top of a katahom
-- the trafos that are part of the boilerplate code need to be checked in the predicate
-- to avoid checking them repeatedly at every extension this is only done when the bottom layer is Kata
mkExtension :: RewRule -> RewRule -> KataPred -> Grade -> Extension
mkExtension ar cr bottomKP gradeMarker =
    ext where
    ext = Extension {
              source = bottomKP,
              target = topKP,
              altStep = ar,
              catStep = cr }
    topKP = KataPred { khom = topK, kpred = predK }
    topK  = Katahom { kalt = genericAltK ext, kcat = genericCatK ext, grade = gradeMarker }
    predK = (kpred bottomKP) { altP = topAltP, catP = topCatP }
    topAltP c i xs = altP (kpred bottomKP) nc i xs && not (hasChanged(ar nc i xs))
                     where nc = max c (if ew i then OptCxt else NoCxt)
    topCatP c i xs = catP (kpred bottomKP) c i xs && not (hasChanged(cr nc i xs))
                     where nc = max c (if ew i then OptCxt else NoCxt)

src :: Extension -> Katahom
src = khom . source

trg :: Extension -> Katahom
trg = khom . target

tpr :: Extension -> RecPred
tpr = kpred . target

type ListMap = Info -> [RE] -> OK [RE]

listComp :: ([RE]->Info) -> ListMap -> ListMap -> ListMap
listComp listInfo f g i xs = f ni `app` xso
                   where
                   xso = g i xs
                   ni = if hasChanged xso then listInfo (valOf xso) else i

genericRepeatAlt :: Extension -> Cxt -> OK [RE] -> OK [RE]
genericRepeatAlt rs c xso  |  hasChanged xso || hasChanged yso
                           =  genericAltK rs c (altInfo (valOf yso)) `app` yso
                           |  otherwise
                           =  yso
                              where
                              yso=kataliftAlt (katahom (trg rs) c) `app` xso

-- Alt part of generic boilerplate
genericAltK :: Extension -> Cxt -> Info -> [RE] -> OK [ToRE]
genericAltK rs c i xs =
  listComp altInfo (genericFromAltK rs c) (altRuleOK(kalt(src rs)) c) i xs

-- generic! only applied on lists that are not only pointwise FromRE, but also as a whole
genericFromAltK :: Extension -> Cxt -> Info -> [FromRE] -> OK [ToRE]
genericFromAltK rs c i []          =  unchanged []
genericFromAltK rs c i [x]         =  single $ katahom (trg rs) c x
genericFromAltK rs c i (Lam:xs)    |  any ewp (valOf xso)
                                   =  xso
                                   |  otherwise
                                   =  okmap (Lam:) xso
                                      where
                                      xso = genericFromAltK rs OptCxt i{ew=False} xs
genericFromAltK rs c i xs          =  genericRepeatAlt rs c (altRuleOK(altStep rs) c i xs)

supplyCatInfo :: ListMap -> [RE] -> OK [RE]
supplyCatInfo f xs = f (catInfo xs) xs

genericRepeatCat :: Extension -> Cxt -> OK [RE] -> OK [RE]
genericRepeatCat rs c xso  |  hasChanged xso || hasChanged yso
                           =  genericCatK rs c (catInfo (valOf yso)) `app` yso
                           |  otherwise
                           =  yso
                              where
                              yso = kataliftCat (katahom (trg rs) NoCxt) `app` xso

-- inputs have been evaluated
genericCatK :: Extension -> Cxt -> Info -> [ToRE] -> OK [ToRE]
genericCatK rs c i xs =
  listComp catInfo (genericFromCatK rs c) (catRuleOK(kcat(src rs)) c) i xs

genericFromCatK :: Extension -> Cxt -> Info -> [FromRE] -> OK [ToRE]
genericFromCatK _  c _ []       =  unchanged []
genericFromCatK rs c _ [x]      =  single $ katahom (trg rs) c x
genericFromCatK rs OptCxt i xs  |  all ewp xs && not (ew i)
                                =  genericFromCatK rs OptCxt i{ew=True} xs
genericFromCatK rs c i xs       =  genericRepeatCat rs c $ catRuleOK(catStep rs) c i xs           

noChangeRule :: RewRule
noChangeRule c i xs = unchanged xs

kataGradeKatahom = Katahom { kalt = noChangeRule, kcat = noChangeRule, grade = Kata }

kataGradeH :: HomTrans
kataGradeH = mkHomTrans kataGradeKatahom
HomTrans { falt = kataAlt, fcat = kataCat, frep = kataRep, fopt = kataOpt } = kataGradeH

kataGrade :: RE -> RE
--kataGrade = valOf . katahom kataGradeKatahom NoCxt
kataGrade = mkTransform kataGradeKatahom

mkTransform :: Katahom -> RE -> RE
mkTransform kh = valOf . katahom kh RootCxt

kataGradeKP = KataPred { khom = kataGradeKatahom, kpred = kataP }

isKata :: RE -> Bool
isKata = checkWith kataP

-- predicate for bottom-line system, grade Kata
-- besides checking structural constraints also the info is tested for correctness, except for grading
kataP :: RecPred
kataP = RecPred { empP = empKataP, lamP = lamKataP, symP = symKataP,
                  altP = altKataP, catP = catKataP, repP = repKataP, optP = optKataP }

-- 0 and 1 are only allowed at the root
empKataP, lamKataP :: Cxt -> Bool
empKataP c = c==RootCxt
lamKataP c = c==RootCxt

-- Symbols are allowed everywhere
symKataP :: Cxt -> Char -> Bool
symKataP _ _ = True

altElem :: Cxt -> RE -> Bool
altElem _ (Sym _)   = True
altElem _ (Cat _ _) = True
altElem c (Rep _)   = c/=RepCxt
altElem _ _         = False

altKataP c i xs = plural xs && all (altElem c) xs && strictlyOrdered xs &&
                  ew i == any ewp xs && si i == listSize xs &&
                  la i == lasAlt xs&& fi i == firAlt xs 

catElem :: RE -> Bool
catElem (Sym _)   = True
catElem (Alt _ _) = True
catElem (Rep _)   = True
catElem (Opt _)   = True
catElem _         = False

catKataP c i xs =  plural xs && all catElem xs &&
                   ew i == all ewp xs && si i == listSize xs &&
                   la i == lasCat xs && fi i == firCat xs 
                   
repKataP :: Cxt -> RE -> Bool
repKataP RepCxt _     =  False
repKataP _ (Sym _)    =  True
repKataP _ (Cat _ _)  =  True
repKataP c (Alt _ xs) =  all (repKataP c) xs
repKataP _ _          =  False

optKataP :: Cxt -> RE -> Bool
optKataP RepCxt _    =  False
optKataP _ (Sym _)   =  True
optKataP _ (Alt i _) =  not (ew i)
optKataP _ (Cat i _) =  not (ew i)
optKataP _  _        =  False

subalts, subcats :: [RE]->[([RE],[RE]->[RE])]
subcats os = [ (ys,\ys'->xs++ys'++zs)
             | m<-[2 .. length os - 1], (xs,ys,zs)<-segPreSuf m os ]

subalts os = [ (xs,\xs'->nubMerge (nubSort xs') ys)
             | (xs,ys)<-powerSplits os, plural xs ]

subaltsPred, subcatsPred :: (RE->Bool) -> [RE]->[([RE],[RE]->[RE])]
subcatsPred p os = [ (ys,\ys'->xs++ys'++zs)
                   | (xs,ys,zs)<-segmentsPred p os, plural ys, not(null xs && null zs)]

subaltsPred p os = [ (xs,\xs'->nubMerge (nubSort xs') ys)
                   | (xs,ys)<-powerSplitsPred p os, plural xs ]

subaltsLPred, subcatsLPred :: ([RE]->Bool) -> [RE]->[([RE],[RE]->[RE])]
subcatsLPred p os = [ (ys,\ys'->xs++ys'++zs)
                    | (xs,ys,zs)<-segmentsLPred p os, plural ys, not(null xs && null zs)]

subaltsLPred p os = [ (xs,\xs'->nubMerge (nubSort xs') ys)
                    | (xs,ys)<-powerSplitsLPred p os, plural xs ]

subaltsLtd, subcatsLtd :: Int -> [RE]->[([RE],[RE]->[RE])]
subcatsLtd m os  =  [ (ys,\ys'->xs++ys'++zs)
                    | (xs,ys,zs)<- maxSegsLtd size m os,
                      plural ys, not (null xs && null zs) ]

subaltsLtd m os  =  [ (xs,\xs'->nubMerge (claim "ordered alts" strictlyOrdered xs') ys)
                    | (xs,ys)<- maxSubsLtd size m os,
                      plural xs, not (null ys) ]

subaltsCatalogue, subcatsCatalogue :: (Int->Int) -> [RE]->[([RE],[RE]->[RE])]
subcatsCatalogue f os  =  [ (ys,\ys'->xs++ys'++zs)
                          | (xs,ys,zs)<- segsLtd size (f 1) os,
                             plural ys, not (null xs && null zs),
                             f (alphaLength $ listAlpha ys) >= listSize ys ]

subaltsCatalogue f os  =  [ (xs,\xs'->nubMerge (claim "ordered alts" strictlyOrdered xs') ys)
                          | (xs,ys)<- subsLtd size (f 1) os,
                             plural xs, not (null ys),
                             f (alphaLength $ listAlpha xs) >= listSize xs ]

-- brutal closure operators,
-- rearranging trafos on subexpressions not recognised because of termination worries
altClosure :: RewRule -> RewRule
altClosure r c i xs = foldr orOK (r c i xs) [ changed $ f ys' | (ys,f)<-subalts xs,
                                              let Alt j _ = altSubseq (Alt i xs) ys,
                                              yso <- [r c j ys],
                                              hasChanged yso, let ys'=valOf yso,
                                              listSize ys' < si j ]

catClosure :: RewRule -> RewRule
catClosure r c i xs = foldr orOK (r c i xs) [changed $ f ys' | (ys,f)<-subcats xs,
                                              let Cat j _ = catSegment (Cat i xs) ys,
					      yso <- [r NoCxt j ys],
					      hasChanged yso, let ys'=valOf yso,
					      listSize ys' < si j]

altClosurePred :: (RE->Bool) -> RewRule -> RewRule
altClosurePred p r c i xs = foldr orOK (r c i xs) [ changed $ f ys' | (ys,f)<-subaltsPred p xs,
                                                    let Alt j _ = altSubseq (Alt i xs) ys,
                                                    yso <- [r c j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j ]
altClosureLtd :: Int -> RewRule -> RewRule
altClosureLtd n r c i xs = list2OK xs [ f ys' | (ys,f)<-subaltsLtd n xs,
                                                    let Alt j _ = altSubseq (Alt i xs) ys,
                                                    yso <- [r c j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j ]

altClosureCatalogue :: (Int->Int) -> RewRule -> RewRule
altClosureCatalogue g r c i xs = list2OK xs [ f ys' | (ys,f)<-subaltsCatalogue g xs,
                                                    let Alt j _ = altSubseq (Alt i xs) ys,
                                                    yso <- [r c j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j ]

altSizeBound :: Int -> RewRule -> RewRule
altSizeBound n r c i xs | si i <= n
                        = r c i xs
                        | otherwise
                        = altClosureLtd n r c i xs

catSizeBound :: Int -> RewRule -> RewRule
catSizeBound n r c i xs | si i <= n
                        = r c i xs
                        | otherwise
                        = catClosureLtd n r c i xs

altSizeBoundCatalogue :: (Int->Int) -> RewRule -> RewRule
altSizeBoundCatalogue f r c i xs | si i <= f (alphaLength $ al i)
                                 = r c i xs
                                 | otherwise
                                 = altClosureCatalogue f r c i xs

catSizeBoundCatalogue :: (Int->Int) -> RewRule -> RewRule
catSizeBoundCatalogue f r c i xs | si i <= f (alphaLength $ al i)
                                 = r c i xs
                                 | otherwise
                                 = catClosureCatalogue f r c i xs

catClosurePred :: (RE->Bool) -> RewRule -> RewRule
catClosurePred p r c i xs = foldr orOK (r c i xs) [ changed $ f ys' | (ys,f)<-subcatsPred p xs,
                                                    let Cat j _ = catSegment (Cat i xs) ys,
					            yso <- [r NoCxt j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j]

catClosureLtd :: Int -> RewRule -> RewRule
catClosureLtd n r _ i xs = list2OK xs [ f ys' | (ys,f)<-subcatsLtd n xs,
                                                    let Cat j _ = catSegment (Cat i xs) ys,
					            yso <- [r NoCxt j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j]

catClosureCatalogue :: (Int->Int) -> RewRule -> RewRule
catClosureCatalogue g r _ i xs = list2OK xs [ f ys' | (ys,f)<-subcatsCatalogue g xs,
                                                    let Cat j _ = catSegment (Cat i xs) ys,
					            yso <- [r NoCxt j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j]

extensionLtd :: Int -> Int -> Extension -> Extension
extensionLtd m n ext = mkExtension altR catR (source ext) (grd $ target ext)
                       where
                       altR = altSizeBound m (altStep ext)
                       catR = catSizeBound n (catStep ext)

extensionCatalogue :: (Int->Int) -> Extension -> Extension
extensionCatalogue  f ext = mkExtension altR catR (source ext) (grd $ target ext)
                               where
                               altR = altSizeBoundCatalogue f (altStep ext)
                               catR = catSizeBoundCatalogue f (catStep ext)

-- REs stored in either of the catalogues are just strings; for use they must be
-- marked throughout as of Minimal grade.

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

contextFunction :: Cxt -> RE -> RE
contextFunction RepCxt  =  rep
contextFunction OptCxt  =  opt
contextFunction _       =  id

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

-- for testing purpose (Generator) we lose the topmost grade of an expression
degradeTop :: RE -> RE
degradeTop (Alt i xs) = Alt i{gr=[]} xs
degradeTop (Cat i xs) = Cat i{gr=[]} xs
degradeTop (Rep x)    = Rep $ degradeTop x
degradeTop (Opt x)    = Opt $ degradeTop x
degradeTop x          = x -- symbols, Lam, Emp
