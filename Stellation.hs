module Stellation where

import List
import Info
import Expression
import Context
import Comparison
import Pressing
import Shrinking

type StelRE = RE

isStellar :: RE -> Bool
isStellar = checkWith stelP

stelEX :: Extension
stelEX = mkExtension altTrans catTrans shrinkKP Stellar

stelK :: Katahom
stelK = khom stelKP

stelKP :: KataPred
stelKP = target stelEX

stelP :: RecPred
stelP = kpred stelKP

Katahom { kalt = stelAltK, kcat = stelCatK } = stelK

stelH = mkHomTrans stelK
HomTrans { falt = stelAlt, fcat = stelCat, frep = stelRep, fopt = stelOpt } = stelH

stellate = mkTransform stelK

stelCxt :: Cxt -> RE -> OK RE
stelCxt = katahom stelK

-- end of boilerplate section

altTrans :: Cxt -> Info -> [StelRE] -> OK [ShrunkRE]
altTrans c i xs =  list2OK xs [ Rep body' : zs | c>=OptCxt, (ys,zs)<-allPowerSplits xs, not(null ys),
                                let body=altSubseq (Alt i xs) ys, istransitive body,
                                let body'=valOf $ shrinkCxt RepCxt body, -- may or may not have an impact
                                size body'+1<size body || size body'<size body && (not $ ew i)]

catTrans :: Cxt -> Info -> [StelRE] -> OK [ShrunkRE]
catTrans c i xs =  list2OK xs (normalcands ++ repcxtcands ++ optcxtcands)
                   where
                   me = Cat i xs
                   normalcands = [ pre++[Rep newmidb]++suf |
                                   (le,suf)<-prefixCom me, (pre,mid)<-suffixCom le,
                                   not(isRep mid) && ewp mid && istransitive mid, --possible issue if mid part is x?, and x* does not shrink
                                   let newmidb=valOf $ shrinkCxt RepCxt mid]
                   {- normalcands = [ pref++[candrep]++suf |
                                   n<- [2..length xs], (pref,cand,suf)<- segPreSuf n xs, all ewp cand,
                                   let cgm = if null pref && null suf then gr i else noCxtCG (gr i),
                                   let body=mkCatCG cgm cand, let candrep=shrinkRep body, body === candrep ] -}
                   repcxtcands = [ [unRep brep] | c==RepCxt, brep <- bodyreps ]
                   optcxtcands = [ [brep] | c==OptCxt, not(ew i), istransitive me, brep <- bodyreps ]
                   bodyreps    = [ brep | not (ew i), (pre,suf)<-prefixCom me, not(null suf), let suft=mkCat suf, ewp pre || ewp suft,
                                   let body=mkAlt[pre,suft],
                                   let brep=shrinkRep body, brep===Rep me ]
                      
    

