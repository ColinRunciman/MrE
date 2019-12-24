module Stellation (stellate, altTrans, catTrans, stelKP)
where

import List
import Info
import Expression
import OK
import Context
import Comparison
import StarPromotion

-- The motivating observation for the transformation here: if any expression x has
-- the empty-word property, and is also transitive, so L(1) <= L(xx) <= L(x), then
-- x === Rep x, enabling simplification of x because of the Rep context.

isStellar :: RE -> Bool
isStellar = checkWith stelP

previousKP :: KataPred
previousKP = promoteKP

previousCxt :: Cxt -> RE -> OK RE
previousCxt = katahom $ khom previousKP

previousRep :: RE -> RE
previousRep = thisfun previousKP . rep

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

stellate = extension2trafo stelEX

stelCxt :: Cxt -> RE -> OK RE
stelCxt = katahom stelK

-- end of boilerplate section

altTrans :: Cxt -> Info -> [RE] -> OK [RE]
altTrans OptCxt i xs = list2OK xs $ [ rep body' : zs
                                    | (ys,zs)<-allPowerSplits xs, plural ys,
                                      let body=altSubseq (Alt i xs) ys, istransitive body,
                                      let body'=valOf $ previousCxt RepCxt body,
                                      size body'+1 < size body ||
                                         size body' < size body && (not $ ew i) ] ++
                                    [ opt body : zs
                                    | (Rep body,zs) <- itemRest xs,
                                      istransitive body ]
altTrans _ i xs  =  unchanged xs -- cannot fire in a NoCxt/RepCxt

catTrans :: Cxt -> Info -> [RE] -> OK [RE]
catTrans c i xs =  list2OK xs (normalcands ++ repcxtcands ++ optcxtcands)
                   where
                   me = Cat i xs
                   normalcands = [ lcontext++[previousRep mid]++rcontext --note: pre/suf may both be empty
                                 | (lcontext,mids,rcontext) <- threesplit xs,
                                   let mid = catSegment me mids,
                                   ewp mid && istransitive mid ]
                   repcxtcands = [ [deRep brep]   | c==RepCxt, brep <- bodyreps ]
                   optcxtcands = [ [brep]
                                 | c==OptCxt, not(ew i), istransitive me, brep <- bodyreps, size brep<=size me]
                   bodyreps    = [ brep | (pres,sufs) <- splits xs,
                                   let suft = catSegment me sufs, let pret = catSegment me pres,
                                   ewp pret || ewp suft,
                                   let brep = previousRep (alt [pret,suft]), brep===rep me ]
                   deRep (Rep x) = x
                   deRep (Opt x) = x -- possible: a rep can simplify to an optP
                   deRep _       = error "illegal rep simplification"


-- splits a list into 3 segments, the middle one of which is plural, the others are allowed to be empty
threesplit :: [a] -> [([a],[a],[a])]
threesplit xs = [(lcontext,mid,rcontext) | (le,rcontext) <- allSplits xs, plural le,
                                           (lcontext,mid) <- allSplits le, plural mid]
