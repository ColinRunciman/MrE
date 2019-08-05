module Automization where
import Info
import Context
import Expression
import Pressing
import AutIntersect
import Stellation

isAutomized :: RE -> Bool
isAutomized = checkWith autoP

autoEX :: Extension
autoEX = mkExtension altAuto catAuto stelKP Auto

autoK :: Katahom
autoK = khom autoKP

autoKP :: KataPred
autoKP = target autoEX

autoP :: RecPred
autoP = kpred autoKP

Katahom { kalt = autoAltK, kcat = autoCatK } = autoK

autoH = mkHomTrans autoK
HomTrans { falt = autoAlt, fcat = autoCat, frep = autoRep, fopt = autoOpt } = autoH

automize = fst . autoCxt NoCxt

autoCxt :: Cxt -> RE -> OK RE
autoCxt = katahom autoK

-- end of boilerplate section

altAuto, catAuto :: RewRule
altAuto c i xs = process c xs (Alt i xs)
catAuto c i xs = process c xs (Cat i xs)

process :: Cxt -> [RE] -> RE -> OK [RE]
process c xs me = list2OK xs
   [ [ se3 ] | e <- [aut1r, aut2r], size e<=2*size mex, -- avoid excesses
               e/=mex, let se2=stellate e, let se3=decontext c se2, size se3<size me ] 
    where
    mex = contextFunction c me
    mex2 = mirror mex
    aut1r = extractRE $ stateMin2 $ createDFA mex
    aut2r = mirror $ extractRE $ stateMin2 $ createDFA mex2

decontext :: Cxt -> RE -> RE
decontext RepCxt (Rep x) = x
decontext c      (Opt x) | c>=OptCxt
                         = x
decontext _      x       = x


