module Museum where
import Alphabet
import Comparison
import Expression
import Context
import Generator
import StarPromotion

-- same as x===y, but the attribute test throws out some later fails early
-- note that swa/fir/ewp are tested early in === anyway
equiv :: RE -> RE -> Bool
equiv x y = alpha x == alpha y && las x == las y && x === y
           

-- IO return type, so we can report stage of progress
britishMuseumMethod :: RE -> KataPred -> IO RE
britishMuseumMethod re kp =
    bmm (createGradedCarrier (alpha2String $ alpha re) kp)
    where
    nre = mkTransform (khom kp) re
    bmm car = putStrLn ("transforming " ++ show nre) >> stage 0 car
    give result = do  putStrLn $ "found " ++ show result
                      return result
    stage n car = do
                     putStrLn $ "trying REs of size " ++ show n
                     let equis = filter (equiv nre) (head car)
                     if null equis then stage (n+1)(tail car)
                     else give (head equis)

-- same as britishMuseumMethod, but does not report on progress
silentMuseumMethod :: RE -> KataPred -> RE
silentMuseumMethod re kp =
    bmm (createGradedCarrier (alpha2String $ alpha re) kp)
    where
    nre          =  mkTransform (khom kp) re
    bmm car      =  stage 0 car
    stage n car  |  null equis 
                 =  stage (n+1)(tail car)
                 |  otherwise
                 =  head equis
                    where
                    equis = filter (equiv nre) (head car)

museum :: RE -> RE
museum x = silentMuseumMethod x promoteKP

