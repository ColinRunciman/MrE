module Derivative where
import Expression
import Context
import Alphabet
import Info
-- import StarPromotion
import List

smartCat :: [RE] -> RE
smartCat = kataCat

smartAlt :: [RE] -> RE
smartAlt = kataAlt

smartOpt = kataOpt

derive :: Char -> RE -> RE
derive c e = smartAlt $ map smartCat $ deriveAlts c e []

deriveAlts :: Char -> RE -> [RE] -> [[RE]]
deriveAlts c (Sym d)    cont   =  [cont | c==d]
deriveAlts c (Alt i xs) cont   |  elemSet c (fi i)
                               =  unions [ deriveAlts c x cont | x<-xs ]
deriveAlts c (Cat i xs) cont   |  elemSet c (fi i)
                               =  deriveCatList c xs cont
deriveAlts c (Opt x) cont      =  deriveAlts c x cont
deriveAlts c (Rep x) cont      =  deriveAlts c x (Rep x:cont)
deriveAlts c _ _               =  [] -- Lam or Emp, or bad (fi i)

-- can assume: char can be first character
deriveCatList :: Char -> [RE] -> [RE] -> [[RE]]
deriveCatList c (x:xs) cont   |  not (elemSet c (fir x)) -- x must be optional
                              =  tailDerive
                              |  not (ewp x) || not (firstCharList c xs)
                              =  headDerive
                              |  otherwise -- c can be knocked off either way
                              =  tailDerive `nubMerge` headDerive
                                 where
                                 headDerive = deriveAlts c x (xs++cont)
                                 tailDerive = deriveCatList c xs cont

-- derivation tree for one letter, as a list: is it finite?
allDers :: Char -> RE -> [RE]
allDers c x = process x []
              where
              process x xs | elem x xs
                           = xs
                           | otherwise
                           = x : process (derive c x) (x:xs)


firstCharList :: Char -> [RE] -> Bool
firstCharList c []     = False
firstCharList c (x:xs) = elemSet c (fir x) || ewp x && firstCharList c xs

-- derivation from the end
evired :: RE -> Char -> RE
evired Lam c            =  Emp
evired Emp c            =  Emp
evired (Sym d) c        =  if c==d then Lam else Emp
evired (Rep re) c       =  smartCat [Rep re, evired re c]
evired (Opt re) c       =  evired re c
evired (Alt _ xs) c     =  smartAlt [evired x c | x<-xs]
evired (Cat _ xs) c     =  unsnocF aux xs
                           where  
                           aux ys y | ewp y
                                    = smartAlt [dy,dys]
                                    | otherwise
                                    = dy
                                      where
                                      dy  = smartCat (ys ++ [evired y c])
                                      dys = evired (mkCat ys) c

unsnocF :: ([a]->a->b) -> [a] -> b
unsnocF cont [x] = cont [] x
unsnocF cont (x:xs) = unsnocF (\ys y->cont (x:ys) y) xs

