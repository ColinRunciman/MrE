module Stellation (stellate, altTrans, catTrans) where

import List
import Info
import Expression
import OK
import Context
import Comparison
-- import Shrinking
import StarPromotion

-- The motivating observation for the transformation here: if any expression x has
-- the empty-word property, and is also transitive, so L(1) <= L(xx) <= L(x), then
-- x === Rep x, enabling simplification of x because of the Rep context.

type StelRE = RE

isStellar :: RE -> Bool
isStellar = checkWith stelP

previousKP :: KataPred
previousKP = promoteKP

previousCxt :: Cxt -> RE -> OK RE
previousCxt = katahom $ khom previousKP

previousRep :: RE -> RE
previousRep = frep $ mkHomTrans $ khom previousKP

stelEX :: Extension
stelEX = extensionLtd 15 20 $
         mkExtension altTrans catTrans previousKP Stellar

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

altTrans :: Cxt -> Info -> [StelRE] -> OK [RE]
altTrans c i xs =  list2OK xs [ Rep body' : zs
                              | c>=OptCxt, (ys,zs)<-allPowerSplits xs, not(null ys),
                                let body=altSubseq (Alt i xs) ys, istransitive body,
                                let body'=valOf $ previousCxt RepCxt body,
                                size body'+1 < size body ||
                                     size body' < size body && (not $ ew i) ]

catTrans :: Cxt -> Info -> [StelRE] -> OK [RE]
catTrans c i xs =  list2OK xs (normalcands ++ repcxtcands ++ optcxtcands)
                   where
                   me = Cat i xs
                   normalcands = [ pre++[Rep newmidBody]++suf
                                 | (le,suf)<-prefixCom me, (pre,mid)<-suffixCom le,
                                   not(isRep mid) && ewp mid && istransitive mid,
                                   let newmidBody=valOf $ previousCxt RepCxt mid,
                                   size newmidBody+1 < size mid ]
                   repcxtcands = [ [unRep brep] | c==RepCxt, brep <- bodyreps ]
                   optcxtcands = [ [brep]
                                 | c==OptCxt, not(ew i), istransitive me, brep <- bodyreps ]
                   bodyreps    = [ brep
                                 | not (ew i), (pre,suf)<-prefixCom me, not(null suf),
                                   let suft=mkCat suf, ewp pre || ewp suft,
                                   let body=alt[pre,suft],
                                   let brep=previousRep body, brep===Rep me ]

-- cheap version of pressing's prefixCom
prefixCom :: RE -> [(RE,[RE])]
prefixCom e@(Cat _ xs) = (e,[]) : [ (cat as,bs) | (as,bs)<- splits xs ]
prefixCom e            = [(e,[])]

suffixCom :: RE -> [([RE],RE)]
suffixCom e@(Cat _ xs) = ([],e) : [ (as,cat bs) | (as,bs) <- splits xs]
suffixCom e            = [([],e)]

