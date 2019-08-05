module Refactorization where

import Data.List (minimumBy)
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing, listToMaybe)
import Function (claim, justIf)
import List (allSplits, itemRest, mergeBy, plural, powerSplits, sublistPairsOf, subsetRest,segPreSuf)
import Expression
import Comparison
import Normalization
import Pressing
import Info
import Context


-- boilerplate: pollute the name space!

type RefactRE = RE

isRefactorized :: RE -> Bool
isRefactorized = checkWith refactP

refactEX :: Extension
refactEX = mkExtension repressAltList refactCatList pressKP Refactorized

refactK :: Katahom
refactK = khom refactKP

refactKP :: KataPred
refactKP = target refactEX

refactP :: RecPred
refactP = kpred refactKP

Katahom { kalt = repressAltK, kcat = refactCatK } = refactK

refactH = mkHomTrans refactK
HomTrans { falt = refactAlt, fcat = refactCat, frep = refactRep, fopt = refactOpt } = refactH

refactorize = fst . katahom refactK NoCxt 

refactCxt :: Cxt -> RE -> OK RE
refactCxt = katahom refactK

-- end  of boilerplate                       

{-
altRefactP pa b xs = altP factP pa b xs &&
                     all null [ 
                              map snd (lOptFactors False x1L x2L old) ++  -- REFAC
                              map snd (lAltFactors False x1L x2L old) ++  -- REFAC
                              map snd (rOptFactors False x1R x2R old) ++  -- REFAC
                              map snd (rAltFactors False x1R x2R old)     -- REFAC
                            | (x1,x2) <- sublistPairsOf xs,
                              let x1L = lMostCom b' x1,
                              let x1R = rMostCom b' x1,
                              let x2L = lMostCom b' x2,
                              let x2R = rMostCom b' x2,
                              let old = normAlt [x1,x2] ]
                      where
                      b' = b || maybe False (\x -> isOpt x || isRep x) pa


-- TO DO: further generalisations may be possible
-- (1) factors from deeper nesting of alts and cats
-- (2) exploit any Rep or Opt context
-}

-- if x *\\* y = Just z
-- then z's language is between y\x and y
-- but z is smaller in size than y
(*\\*) :: RE -> RE -> Maybe RE
x        *\\* x'       |  x `eqv` x'  
                       =  Just Emp
x        *\\* Opt x'   |  x `eqv` x'
                       =  Just Lam
x        *\\* Alt _ xs |  not $ null cands
                       =  listToMaybe cands
                          where cands = [ mkAlt ys | (x',ys) <- itemRest xs, eqv x x']
Opt x    *\\* Opt y    =  listToMaybe $ [ z | Just z <- [x *\\* y]] ++ [y]
Alt _ xs *\\* Alt _ ys |  not $ null cands
                       =  listToMaybe cands
                          where cands = [ res |
                                          (x,xs')<-itemRest xs, (y,ys')<-itemRest ys, eqv x y,
                                          let tys' = mkAlt ys',
                                          Just res <- [ mkAlt xs' *\\* tys', Just tys' ]]
x        *\\* Opt y    =  fmap pressOpt $ x *\\* y
x        *\\* Alt _ ys |  not $ null cands
                       =  listToMaybe cands
                          where cands = [ pressAlt [ res, y ] |
                                          (y,ys') <-itemRest ys, let y'=mkAlt ys', x `sub` claim "normal y' in *\\*" isNormal y',
                                          Just res <- [ x *\\* y' ] ]
Opt x    *\\* y        |  ewp y
                       =  x *\\* y
Alt _ xs *\\* y        =  listToMaybe cands
                           where cands = [ res |
                                          (w,xs') <- itemRest xs, w `sub` claim "normal y in *\\*" isNormal y,
                                          Just res <- [ mkAlt xs' *\\* y]]
_        *\\* _        = Nothing



-- factorisation predicate with residual
-- spec: x *@-* y = Just (s,t) implies
-- that y=s+xt, and that some commonality was exploited
-- no Alt-Alt rule, as this would require a tricky sub-sidecondition
-- the remaining alternatives s are given as a list, which can be subjected to further factorizations
-- TO DO: one could factorize derivative-style, factorizing beyond nullable prefixes
(*@-*) :: RE -> RE -> Maybe ([RE],RE)
x *@-* x'        |  sub x x' && not (null c0)
                 =  listToMaybe c0
                 |  isCat x'
                 =  listToMaybe (c1++c2)
                    where
                    c0 = [ (z,pressOpt z') |
                           Just y <- [x *\\* x'],
                           Just (z,z')<- [x *@-* y,Just(altList y,Emp)]]
                    c1 = [ ([],mkCat tl) | (hd,tl)<-prefixCom x', eqv x hd ]
                    c2 = [ (altList a1,a2) |
                                 (hd,tl)<-lMostCom' x', Just (z,z') <- [x *@-* hd],
                                 let a1=pressCat(pressAlt z:tl), let a2=pressCat(z':tl)]
x *@-* Alt _ ys  |  null cands
                 =  Nothing
                 |  otherwise
                 =  Just bestcand
                    where
                    cands = [ (k,(altList nz,z')) | (y,ys')<-itemRest ys, Just(z,z')<-[ x *@-* y ],
                                let nz=pressAlt(z++ys'), let k=size nz+size z']
                    bestcand = snd $ minimumBy keyOrder cands
x *@-* Opt x'    =  x *@-* x' >>= \(z,z')-> Just(Lam:z,z')
x *@-* Rep x'    =  x *@-* x' >>= \(z,z')->
                        let nr=pressCat[z',Rep x'] in justIf (null z && size nr<=size x') ([Lam],nr)
_ *@-* _         =  Nothing

-- mirror version of *@-*            
(*-@*) :: RE -> RE -> Maybe ([RE],RE)
x' *-@* x        |  sub x x' {- (claim "normal x' in *-@*" isNormal x') -} && not (null c0)
                 =  listToMaybe c0
                 |  isCat x'
                 =  listToMaybe (c1++c2)
                    where
                    c0 = [ (z,pressOpt z') |
                           Just y <- [x *\\* x'],
                           Just (z,z')<- [y *-@* x,Just(altList y,Emp)]]
                    c1 = [ ([],mkCat lt) | (lt,dh)<-suffixCom x', eqv x dh ]
                    c2 = [ (altList a1,a2) |
                                 (lt,dh)<-rMostCom' x', Just (z,z')<- [dh *-@* x],
                                 let a1=pressCat(lt++[pressAlt z]), let a2=pressCat(lt++[z']) ]
Alt _ ys *-@* x  |  null cands
                 =  Nothing
                 |  otherwise
                 =  Just bestcand
                    where
                    cands = [ (k,(altList nz,z')) | (y,ys')<-itemRest ys, Just(z,z')<-[ y *-@* x ],
                                let nz=pressAlt(z++ys'), let k=size nz+size z'-size y]
                    bestcand = snd $ minimumBy keyOrder cands
Rep x' *-@* x    =  x' *-@* x >>= \(z,z')->
                        let nr=pressCat[Rep x',z'] in justIf (null z && size nr<=size x') ([Lam],nr)
Opt x' *-@* x    =  x' *-@* x >>= \(z,z')-> Just(Lam:z,z')
_      *-@* _    =  Nothing  


-- just one iteration now
repressAltList :: RewRule -- Cxt -> Info -> [RE]-> OK[RE]
repressAltList c i xs  =  {- refactPairs c i xs `orOK` -} refactElem c i xs

{-
refactOptPref c i xs = list2OK xs
                     [ [refactorize cand] | (y,ys)<-itemRest xs, isCat y,
                       cand <- [ ca | (Opt p,suf) <- lMostCom' y, let suft=mkCat suf,
                                      not(ewp suft), p `sublang` lang, let newalt=fst $ pressCxt c $ normCat[p,Opt suft],
                                      Just ns <- [newalt *///* (suft:ys)],
                                      let ca=fst $ pressCxt c $ normAlt (newalt:ns),
                                      size ca<si i]
                     ]
                       where
                       cf = contextFunction c
                       lang = cf (Alt i xs)
-}
                             
-- refactPair refactors 2 elements against one another; superseded by refactElem
{-
refactPairs :: Cxt -> Info -> [RefactRE] -> OK [PressRE]
refactPairs c i xs = list2OK xs [ [refactorize cand]
                                | ([x1,x2],xs') <- subsetRest 2 xs,
                                  [x,y]<-[[x1,x2],[x2,x1]],
                                  cand <- [ ca | (pre,suf) <- prefixCom x,
                                                 Just (zs,z')<- [ pre *@-* y],
                                                 let residual=valOf $ refactCxt c (mkAlt(zs++xs')),
                                                 -- recursive calls: "smaller" list
                                                 let ca=valOf $ pressCxt c (mkAlt[residual,normCat[pre,refactAlt[normCat suf,z']]]),
                                                 size ca < si i ] ++            
                                          [ ca | (pre,suf) <- suffixCom x,
                                                 Just (zs,z')<- [ y *-@* suf ],
                                                 let residual=valOf $ refactCxt c (mkAlt(zs++xs')),
                                                 let ca=valOf $ pressCxt c (mkAlt[residual,normCat[refactAlt[normCat pre,z'],suf]]),
                                                 size ca < si i ] ]   
-}
better :: RE -> Info -> Bool
better x i = size x < si i || size x==si i && (ewp x && not (ew i))

refactElem c i xs = list2OK xs [ [refactorize cand]
                                 | (y,ys) <- powerSplits xs, let yst=mkAlt ys, let yt=mkAlt y,
                                   d <- [ d | d<-[RepCxt,OptCxt,NoCxt], c>=d], -- awkward trick to restore monotonicity
                                   cand <- [ ca | (pre,suf)<-prefixCom yt, not(null suf), let suft=normCat suf,
                                                  ca <- [ capre | Just (zs,z')<-[pre *@-* yst],
                                                          let resid=valOf $ refactCxt d $ mkAlt zs, -- refactor this smaller list
                                                          let newsuf = refactAlt[suft,z'],          -- another smaller list that can be refactored
                                                          let capre= valOf $ pressCxt d $ mkAlt [resid,mkCat[pre,newsuf]], -- bigger!
                                                          better capre i] ++
                                                          -- size capre < si i] ++
                                                        [ casuf | Just (zs,z')<-[yst *-@* suft],
                                                          let resid=valOf $ refactCxt d $ mkAlt zs, -- refactor this smaller list
                                                          let newpre = refactAlt[pre,z'],           -- another smaller list that can be refactored
                                                          let casuf= valOf $ pressCxt d $ mkAlt [resid,mkCat[newpre,suft]], -- bigger!
                                                          better casuf i] ] ++
                                                          -- size casuf < si i] ] ++
                                           [ ca | v<-full yt, w<-full yst, ca <- fact2 v w d]
                                           {-[ ca | Just (zs,z')<-[yt *-@* yst], 
                                                  let resid = valOf $ refactCxt d $ mkAlt zs,
                                                  let ca=valOf $ pressCxt d $ mkAlt[resid,mkCat[Opt z',yst]],
                                                  size ca < si i] ++
                                           [ ca | Just (zs,z')<-[yt *@-* yst], 
                                                  let resid = valOf $ refactCxt d $ mkAlt zs,
                                                  let ca=valOf $ pressCxt d $ mkAlt[resid,mkCat[yt,Opt z']],
                                                  size ca < si i] -}
                               ]                                        
                     where
                     cf= contextFunction c
                     xlang=cf(normCat xs) 
                     pf t = prefixCom t ++ [(pressOpt t,[])| c>=OptCxt && not(ewp t)] ++ [(pressRep t,[])| c==RepCxt, not(isRep t)]
                     sf t = suffixCom t ++ [([],pressOpt t)| c>=OptCxt && not(ewp t)] ++ [([],pressRep t)| c==RepCxt, not(isRep t)]
                     full t = [ t ] ++ [ Opt t | c>=OptCxt && not(ewp t)] ++ [ pressRep t | c==RepCxt, not(isRep t) ]
                     fact2 v w d = [ ca | Just (zs,z')<-[v *-@* w], 
                                          let resid = valOf $ refactCxt d $ mkAlt zs,
                                          let ca=valOf $ pressCxt d $ mkAlt[resid,mkCat[Opt z',w]],
                                          better ca i] ++
                                          -- size ca < si i] ++ 
                                   [ ca | Just (zs,z')<-[v *@-* w], 
                                          let resid = valOf $ refactCxt d $ mkAlt zs,
                                          let ca=valOf $ pressCxt d $ mkAlt[resid,mkCat[v,Opt z']],
                                          better ca i]
                                          -- size ca < si i] 

-- are these used at all anymore?
-- newAlts results are never plural
-- TO DO: pass on the Bool parameter of the outer Alt
-- also pass on eBit and exploit
newAltsL :: RE -> [RE] -> RE -> [RE] -> RE -> [RE]
newAltsL x xs y ys old = [ res | sub x y, Just z<-[x *\\* y],
                                      let rs  = pressAlt[mkCat ys,mkCat xs],
                                      let ns  = [pressCat[x,rs],pressCat(z:ys)],
                                      let pb  = pressCat[y,rs], -- only for bestcase
                                      let bestcase = isLam z && mkCat xs `sub` (claim "normal old in newAltsL" isNormal old),
                                      let ms  = pressAlt ns,
                                      let res = if bestcase then pb else ms,
                                      bestcase || size res<size old]

newAltsR :: [RE] -> RE -> [RE] -> RE -> RE -> [RE]
newAltsR xs x ys y old = [ res | sub x y, Just z<-[x *\\* y],
                                      let rs  = pressAlt[mkCat ys,mkCat xs],
                                      let ns  = [pressCat[rs,x],pressCat(ys++[z])],
                                      let pb  = pressCat[rs,y], -- only for bestcase
                                      let bestcase = isLam z && mkCat xs `sub` (claim "normal old in newAltsR" isNormal old),
                                      let ms  = pressAlt ns,
                                      let res = if bestcase then pb else ms,
                                      bestcase || size res<size old]

-- TO DO: improve efficiency, some refactorings appear as candidates more than once
-- SMK 18/9/2015 replaced calls to lMostCom'/rMostCom' by prefixCom/suffixCom, as cases were lost
(*-+->*) :: RE -> RE -> [RE] -- list result is a list of alternative results
c1 *-+->* c2           | isCat c1 || isCat c2
                       = foldr (mergeBy cmpSize) [] $
                         [ mergeBy cmpSize (newAltsL x xs y ys old) (newAltsL y ys x xs old)  
                         | (x,xs)<-prefixCom c1, (y,ys)<-prefixCom c2] ++ --snd prefixCom was lMostCom'
                         [ mergeBy cmpSize (newAltsR xs x ys y old) (newAltsR ys y xs x old)  
                         | (xs,x)<-suffixCom c1, (ys,y)<-suffixCom c2]   -- snd suffixCom was rMostCom'
                       | otherwise
                       = []
                         where old       = normAlt [c1,c2]

(*-+?->*) :: RE -> RE -> [RE]
c1 *-+?->* c2  =  mergeBy cmpSize
                          [ x | not $ ewp c1, x <- (Opt c1 *-+->* c2)]
                          [ x | not $ ewp c2, x <- (c1 *-+->* Opt c2)]
                             
-- plain factorizations, no re-factorings
(*-=->*) :: RE -> RE -> [RE] -- list result is a list of alternative results
c1 *-=->* c2           | isCat c1 || isCat c2
                       = mergeBy cmpSize
                         [ pressCat[xy,pressAlt[mkCat xs,mkCat ys]]
                         | (x,xs)<-prefixCom c1, (y,ys)<-prefixCom c2, Just xy<-[eqr x y]]
                         [ pressCat[pressAlt[mkCat xs,mkCat ys],xy]  
                         | (xs,x)<-suffixCom c1, (ys,y)<-suffixCom c2, Just xy<-[eqr x y]]   
                       | otherwise
                       = []
                        
(*-=?->*) :: RE -> RE -> [RE]
c1 *-=?->* c2  =  mergeBy cmpSize
                          [ x | not $ ewp c1, x <- (Opt c1 *-=->* c2)]
                          [ x | not $ ewp c2, x <- (c1 *-=->* Opt c2)]


altArity :: RE -> Maybe Int
altArity (Alt _ xs) = Just (length xs)
altArity (Opt x)    = altArity x
altArity _          = Nothing

cmpSize :: RE -> RE -> Ordering
cmpSize x y  =  compare (size x) (size y)

altList (Alt _ xs)        =  xs
altList (Opt x)           =  Lam : altList x
altList x                 =  [x]

refactCatList :: RewRule
refactCatList c i zs | not $ plural zs = unchanged zs
refactCatList c i zs =   list2OK zs cands
                         where
                         x     =  Cat i zs
                         cands = [ [refactorize res] | (pre,y,suf)<-rollSplit x, ewp y,
                                      res <- [ nt | (py,sy)<-prefixComOpt y, let tsy=mkCat sy,
                                               Just(as,fa)<-[py *@-* suf],
                                               let xs=[pressCat[tsy,suf],fa], 
                                               let axs=pressAlt xs, 
                                               let s1=pressCat[py,axs],
                                               let ys=s1:as,
                                               let ays =pressAlt ys,
                                               let nt=valOf $ pressCxt c $ mkCat[pre,ays],
                                               better nt i] ++
                                               -- size nt<si i] ++
                                             [ nt | (py,sy)<-suffixComOpt y, let tpy=mkCat py,
                                               Just(as,fa)<-[pre *-@* sy],
                                               let xs=[pressCat[pre,tpy],fa],
                                               let axs=pressAlt xs,
                                               let s1=pressCat[axs,sy],
                                               let ys= s1 : as,
                                               let ays=pressAlt ys,
                                               let nt=valOf $ pressCxt c $ mkCat[ays,suf],
                                               better nt i]]
                                               -- size nt<si i]]
                                 ++ 
                                 [ [refactorize nt] | c>=OptCxt, (Rep y,ys)<-lMostComList zs,
                                               let nys=valOf $ pressCxt c $ mkCat (Rep y:y:ys), 
                                               let nt=valOf $ pressCxt c $ mkAlt[mkCat ys,nys], 
                                               better nt i ]
                                               -- size nt<si i ]
                                 ++
                                 [ [refactorize nt] | c>=OptCxt, (ys,Rep y)<-rMostComList zs,
                                               let nys=valOf $ pressCxt c $ mkCat (ys++[y,Rep y]), 
                                               let nt=valOf $ pressCxt c $ mkAlt[mkCat ys,nys],
                                               better nt i]
                                               -- size nt<si i ]
                                 ++
                                 [ [refactorize a3] | (pre,[x],suf) <- segPreSuf 1 zs, 
                                     (x1,x2)<-splitElem x,
                                     let a1=valOf $ refactCxt c (mkCat(pre++[x1]++suf)), -- projections are smaller, can use refact
                                     let a2=valOf $ refactCxt c (mkCat(pre++[x2]++suf)),
                                     let a3=valOf $ pressCxt c (mkAlt[a1,a2]), better a3 i]

splitElem :: RE -> [(RE,RE)]
splitElem (Alt _ xs) = [ (mkAlt xs1,mkAlt xs2) | (xs1,xs2)<-powerSplits xs ]
splitElem (Opt x) = [(x,Lam)]
splitElem _       = []

prefixComOpt :: RE -> [(RE,[RE])]
prefixComOpt (Opt x)  =  prefixCom x
prefixComOpt (Rep x)  =  [ (p,s++[Rep x]) | (p,s)<- prefixCom x]
prefixComOpt _        =  []

suffixComOpt :: RE -> [([RE],RE)]
suffixComOpt (Opt x)  =  suffixCom x
suffixComOpt (Rep x)  =  [ (Rep x:p,s) | (p,s)<- suffixCom x]
suffixComOpt _        =  []

rollSplit :: RE -> [(RE,RE,RE)]
rollSplit x | isCat x 
            = [(mkCat pre2,last,mkCat suf) | (pre,suf)<-prefixCom x, (pre2,last)<-rMostCom' pre]
            | otherwise
            = []


