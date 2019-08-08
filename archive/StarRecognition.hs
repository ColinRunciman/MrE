module StarRecognition () where

import Expression
import Alphabet
import qualified Data.Set as S
import Comparison
import StarPromotion
import Info
import Context
import List
import Derivative

-- checks whether an RE is Sigma*, for its alphabet Sigma
sigmaStarCheck :: RE -> Bool
sigmaStarCheck re = ewp re && alp == (charSet (alpha re)) &&
                    checkAlpha2 (S.singleton re) alp (allDerives (enumerateSet alp) re [])
                    where
                    alp = swa re

checkAlpha2 :: S.Set RE -> CharSet -> [RE] -> Bool
checkAlpha2 _ _ [] = True -- all checks have been passed
checkAlpha2 doneSet alp (r:rs)
    | S.member r doneSet -- we have seen this re before during this test, skip it
    = checkAlpha2 doneSet alp rs
    | ewp r && swa r == alp -- re passes the invariant, we still need to deal with its derivatives
    = checkAlpha2 (S.insert r doneSet) alp (allDerives (enumerateSet alp) r rs)
    | otherwise
    = False

totalLang :: CharSet -> RE
totalLang cset = kataRep $ mkAlt [ Sym c | c <- enumerateSet cset ]

recogniseExtension :: Extension
recogniseExtension = mkExtension altRecognition catRecognition promoteKP Recognised

recognise :: RE -> RE
recognise = valOf . recogniseCxt NoCxt

recogniseCxt = katahom recogniseK

recogniseK = trg recogniseExtension
recogniseH = mkHomTrans recogniseK
HomTrans { falt=recogniseAlt,  fcat=recogniseCat, frep= recogniseRep, fopt=recogniseOpt} = recogniseH

recogniseKP = target recogniseExtension

recogniseP = tpr recogniseExtension
isRecognised = checkWith recogniseP

altRecognition, catRecognition :: RewRule
altRecognition c i xs        | sigmaStarCheck old
                             = changed [totalLang (sw i)]
                               where old = Alt i xs
altRecognition OptCxt i xs   | not(ew i) && sigmaStarCheck old2 && si i>=size new
                             = changed [new]
                             | binary xs || not(pluralCS alc)
                             = unchanged xs
                             | otherwise
                             = list2OK xs [ knew:resid | (redal,resid)<- powerSplitsPred pred xs,
                                            plural redal, not(null resid), let k=kataAlt redal,
                                            pred k, sigmaStarCheck (kataOpt k), let knew=promoteRep k,
                                            size knew <= size k]
                               where
                               alc = charSet (al i)
                               pred x = charSet (alpha x) /= alc
                               old = Alt i xs
                               old2 = Opt old
                               new  = promoteRep old
altRecognition _ i xs        = unchanged xs

binary [_,_] = True
binary _     = False

isSingleton [_] = True
isSingleton _   = False

catRecognition c i xs        | sigmaStarCheck old
                             = changed [totalLang (sw i)]
                               where old = Cat i xs
catRecognition OptCxt i xs   | not(ew i) && sigmaStarCheck old2 && si i>=size new -- sizecheck, because this can increase
                             = changed [new]
                               where old  = Cat i xs
                                     old2 = Opt old
                                     new  = promoteRep old
catRecognition _ i xs        = list2OK xs [ (li++[totalLang (swa mid)] ++ re) | (li,mi,re) <- segmentsPred ewp xs,
                                            plural mi, not(null li && null re),
                                            let mid = kataCat mi, sigmaStarCheck mid ]

