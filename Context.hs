module Context where

import List
import Info
import Expression
import Function ((===>))
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

type OK t = (t,Bool)
-- TO DO: meaning of Bool values

-- projection functions and constructor, to make a change of representation less painful
valOf :: OK t -> t
valOf = fst

hasChanged :: OK t -> Bool
hasChanged = snd

mkOK :: t -> Bool -> OK t
mkOK t x = (t,x)

type RewRule = Cxt -> Info -> [RE] -> OK [RE]
data Katahom = Katahom { kalt, kcat  :: RewRule, grade :: Grade }

{-
altRule :: RewRule -> RewRule
altRule r c i xs = okmap concatAlt ( r c i xs)
-}
-- modifies the alt-rule of a Katahom by evaluating the elements in the list first
-- then flattening the results, then applying the rule, then flatten the result
altRule :: Katahom -> RewRule
altRule kh c i xs  |  not (plural xs')
                   =  xso
                   |  otherwise
                   =  okmap concatAlt $ kalt kh c ni `app` xso
                      where
                      xso = kataliftAltSafe (katahom kh c) xs
                      xs' = valOf xso
                      ni  = if hasChanged xso then altInfo xs' else i

kataliftAltSafe :: (RE->OK RE) -> [RE] -> OK [RE]
kataliftAltSafe f xs = potentialChange (/=xs) $ (okmap concatAlt $ katalift f xs)

altRuleOK :: RewRule -> RewRule
altRuleOK r c i xs = okmapIf concatAlt (r c i xs)

{-
catRule :: RewRule -> RewRule
catRule r c i xs = okmap concatCat (r c i xs)
-}
-- dual to altRule
catRule :: Katahom -> RewRule
catRule kh c i xs  |  not (plural xs')
                   =  xso 
                   |  otherwise
                   =  okmap concatCat $ kcat kh c ni `app` xso
                      where
                      xso = kataliftCatSafe (katahom kh NoCxt) xs
                      xs' = valOf xso
                      ni  = if hasChanged xso then catInfo xs' else i

kataliftCatSafe :: (RE->OK RE) -> [RE] -> OK [RE]
kataliftCatSafe f xs = potentialChange (/=xs) $ (okmap concatCat $ katalift f xs)


catRuleOK :: RewRule -> RewRule
catRuleOK r c i xs = okmapIf concatCat $ r c i xs

-- unchanged is the unit of the Kleisli composition of the OK monad
unchanged :: a -> OK a
unchanged x = (x,False)

changed :: a-> OK a
changed x = (x,True)

updateEQ :: Eq a => a -> a -> OK a
updateEQ x y = (y,x/=y)

-- >>=, but with args swapped
app :: (a -> OK b) -> OK a -> OK b
app f (x,tag) = (b,tag || ntag) where (b,ntag)=f x

ifchanged :: OK a -> (a -> OK b) -> (a -> OK b) -> OK b
ifchanged (x,b) f g = app (if b then f else g) (x,b)

appch :: (a -> OK a) -> (OK a -> OK a)
appch f x = ifchanged x f unchanged

-- Kleisli-composition, in function application order
aft :: (b -> OK c) -> (a -> OK b) -> a -> OK c
aft f g  =  \x -> f `app` g x

aftch :: (a -> OK a) -> (a -> OK a) -> a -> OK a
aftch f g  =  \x -> f `appch` g x

-- abandon calls not satisfying the relation
chapp :: (a->a-> Bool) -> (a -> OK a) -> (a -> OK a)
chapp p f x = if p x (valOf call) then call else unchanged x where call = f x

okmap :: (a->b) -> (OK a ->OK b)
okmap f (x,tag) = (f x,tag)

okmap2 :: (a->b->c) -> (OK a -> OK b -> OK c)
okmap2 bin o1 o2 = mkOK (bin (valOf o1) (valOf o2)) (hasChanged o1 || hasChanged o2)

okmapIf :: (a->a) -> (OK a -> OK a)
okmapIf f (x,tag) = if tag then (f x,tag) else (x,tag)

single :: OK a -> OK [a]
single = okmap (:[])

unsafeChanged :: OK a -> OK a
unsafeChanged v = changed(valOf v)


-- mplus for OK type
orOK :: OK a -> OK a -> OK a
orOK a b = if hasChanged a then a else b

guardOK :: Bool -> OK a -> OK a -> OK a
guardOK False _ x  = x
guardOK True th el = orOK th el

guardApply :: Bool -> (a->a) -> a -> OK a
guardApply b f x = if b then changed (f x) else unchanged x

guardMap :: Bool -> (a->a) -> OK a -> OK a
guardMap b f x = if b then okmap f x else x

-- if predicate is True, flag a change regardless; no need to evaluate it if change has been flagged anyway
potentialChange :: (a->Bool) -> OK a -> OK a
potentialChange p x = mkOK vx (hasChanged x || p vx) where vx=valOf x

{-
not used any more
concatMapOK :: (a -> OK [b]) -> [a] -> OK [b]
concatMapOK f []     = unchanged []
concatMapOK f (x:xs) = (ys++zs,b1||b2)
    where
    (ys,b1) = f x
    (zs,b2) = concatMapOK f xs
-}

list2OK :: a -> [a] -> OK a
list2OK x []    = unchanged x
list2OK _ (x:_) = changed x

{-
maybe2OK :: a -> Maybe a -> OK a
maybe2OK x Nothing  = unchanged x
maybe2OK _ (Just x) = changed x
-}

katalift :: (a -> OK b) -> [a] -> OK [b]
katalift k xs  =  (xs', or bs') where (xs',bs')  =  unzip $ map k xs

-- use the first that applies, no-change may still re-attribute x to x'
-- not obsolete? single remaining use, indirectly in Pressing
katalift1 :: (a -> OK a) -> [a] -> OK [a]
katalift1 f [] = unchanged []
katalift1 f (x:xs) |  b
                   =  changed (x' : xs)
                   |  otherwise
                   =  okmap (x' :) $ katalift1 f xs
                      where
                      (x',b) = f x

-- keep applying the function as long as there is a change
fixOK :: (a-> OK a) -> a -> OK a
fixOK f a  = appch (fixOK f) (f a)

-- untrusting katahom, i.e. it does not assume that the rules preserve standardness
-- or that the original RE was standard
-- it does trust existing grading though
-- TO DO: the RootCxt code could be switched on, to permit trafos not to do their own mirror
--   best to leave it till mirroring is memoized
katahom :: Katahom -> Cxt -> RE -> OK RE
{- switched off for now
katahom kh RootCxt  x      |  size(valOf run2)<size(valOf run1)
                           =  app (katahom kh RootCxt) run2
                           |  otherwise
                           =  run1
                              where
                              run1 = katahom kh NoCxt x
                              -- run2 is not used directly to avoid strange expression order
                              run2 = okmap mirror $ app (katahom kh NoCxt) (okmap mirror run1)
-}
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
reOpt c old new  | c>=OptCxt =  new
                 | ewp old && not(ewp new) = if isEmp new then Lam else Opt new
                 | otherwise = new

eitherAltCat :: (CGMap->[RE]->RE) -> Cxt -> Grade -> CGMap -> RE -> OK [RE] -> OK RE
eitherAltCat cstr c g m xold xso  |  ok c g m
                                  =  unchanged xold
                                  |  not (plural xs) -- first look at xso, so this triggers the katahom
                                  =  okmap (cstr m) xso
                                  |  all isSym xs -- all subs are symbols, thus minimal in any context
                                  =  okmap (cstr [(RepCxt,Minimal)]) xso
                                  |  hasChanged xso -- we build a new expression
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
{-
OBSOLETE
-- check whether this Rep-body gives the total language of its alphabet
-- only applied to Alts and Cats that are not already of minimal form
totalCheck :: RE -> OK RE
totalCheck x  |  all (\d->swp d x) al
              =  updateEQ x (total (fir x))
              |  otherwise
              =  unchanged x
                 where
                 al = alpha x
-}

-- input is set-like 
total :: [Char] -> RE
total xs = upgradeRE RepCxt Minimal (mkAlt (map Sym xs))

-- specific katalifts for Cats and Alts
kataliftAlt, kataliftCat, katalift1Alt :: (RE -> OK RE) -> [RE] -> OK [RE]
kataliftAlt f xs  = okmapIf concatAlt $ katalift f xs
kataliftCat f xs  = okmapIf concatCat $ katalift f xs
katalift1Alt f xs = okmapIf concatAlt $ katalift1 f xs

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
-- would be nice to eliminate need for this
altComp :: ListMap -> ListMap -> ListMap
altComp f g i xs = f ni `app` xso
                   where
                   xso = g i xs
                   ni = if (hasChanged xso) then altInfo (valOf xso) else i

genericRepeatAlt :: Extension -> Cxt -> OK [RE] -> OK [RE]
genericRepeatAlt rs c xso  |  hasChanged xso || hasChanged yso
                           =  genericAltK rs c (altInfo (valOf yso)) `app` yso
                           |  otherwise
                           =  yso
                              where
                              yso=kataliftAlt (katahom (trg rs) c) `app` xso

-- Alt part of generic boilerplate
genericAltK :: Extension -> Cxt -> Info -> [RE] -> OK [ToRE]
-- genericAltK rs c i xs = genericFromAltK rs c i `app` altRuleOK(kalt(src rs)) c i xs
genericAltK rs c i xs = (genericFromAltK rs c `altComp` altRuleOK(kalt(src rs)) c) i xs

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
--genericFromAltK rs OptCxt i xs     |  any ewp xs
--                                   =  genericFromAltList rs EwpCxt i xs
genericFromAltK rs c i xs          =  genericRepeatAlt rs c (altRuleOK(altStep rs) c i xs)

-- Cat Part of boilerplate
-- altComp :: ListMap -> ListMap -> ListMap
catComp f g i xs = f ni `app` xso
                   where
                   xso = g i xs
                   ni = if (hasChanged xso) then catInfo (valOf xso) else i

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
genericCatK rs c i xs = (genericFromCatK rs c `catComp` catRuleOK(kcat(src rs)) c) i xs
--genericCatK rs c i xs = genericFromCatK rs c i `app` catRuleOK(kcat(src rs)) c i xs

genericFromCatK :: Extension -> Cxt -> Info -> [FromRE] -> OK [ToRE]
genericFromCatK _  c _ []       =  unchanged []
genericFromCatK rs c _ [x]      =  single $ katahom (trg rs) c x
genericFromCatK rs OptCxt i xs  |  all ewp xs && not (ew i)
                                =  genericFromCatK rs OptCxt i{ew=True} xs
{- incorrect - symbols can roll! and therefore trigger fusions, e.g. aa*(ba?)?
genericFromCatK rs NoCxt i xs   |  isSym (head xs) -- no lMostCom', this is generic; no last/init because of rolling
                                =  okmap addsyms xsotail
                                   where
                                   (syms,others) = span isSym xs
                                   newew         = all ewp others
                                   xsotail       = genericFromCatK rs NoCxt i{ew=newew, fi=firCat others} others
                                   addsyms [x]   = [upgradeRE OptCxt (gradeOfCxt NoCxt x) (mkCat (reapp syms x))]
                                   addsyms xs    = syms ++ xs
                                   reapp ys (Cat _ zs) = ys ++ zs
                                   reapp ys x          = ys ++ [x] -}
genericFromCatK rs c i xs       =  --ifchanged (kataliftCat (katahom (trg rs) NoCxt) xs)
                                   --    (supplyCatInfo $ genericCatK rs c)
                                   --    (genericRepeatCat rs c . catRuleOK(catStep rs) c i)
                                       genericRepeatCat rs c $ catRuleOK(catStep rs) c i xs           

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
altClosureLPred :: ([RE]->Bool) -> RewRule -> RewRule
altClosureLPred p r c i xs = list2OK xs [ f ys' | (ys,f)<-subaltsLPred p xs,
                                                    let Alt j _ = altSubseq (Alt i xs) ys,
                                                    yso <- [r c j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j ]

altSizeBound :: Int -> RewRule -> RewRule
altSizeBound n r c i xs | si i <= n
                        = r c i xs
                        | otherwise
                        = altClosureLPred (\t->listSize t<=n) r c i xs
catSizeBound :: Int -> RewRule -> RewRule
catSizeBound n r c i xs | si i <= n
                        = r c i xs
                        | otherwise
                        = catClosureLPred (\t->listSize t<=n) r c i xs


catClosurePred :: (RE->Bool) -> RewRule -> RewRule
catClosurePred p r c i xs = foldr orOK (r c i xs) [ changed $ f ys' | (ys,f)<-subcatsPred p xs,
                                                    let Cat j _ = catSegment (Cat i xs) ys,
					            yso <- [r NoCxt j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j]
catClosureLPred :: ([RE]->Bool) -> RewRule -> RewRule
catClosureLPred p r _ i xs = list2OK xs [ f ys' | (ys,f)<-subcatsLPred p xs,
                                                    let Cat j _ = catSegment (Cat i xs) ys,
					            yso <- [r NoCxt j ys],
					            hasChanged yso, let ys'=valOf yso,
					            listSize ys' < si j]

limitExtension :: Int -> Extension -> Extension
limitExtension n ext = mkExtension altR catR (source ext) (grd $ target ext)
                       where
                       altR = altSizeBound n (altStep ext)
                       catR = altSizeBound n (catStep ext)
