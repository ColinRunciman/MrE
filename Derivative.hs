module Derivative where
import Expression
import Context

smartCat :: [RE] -> RE
smartCat = kataCat -- was fuseCat

smartAlt :: [RE] -> RE
smartAlt = kataAlt -- was fuseAlt

derive :: Char -> RE -> RE
derive c Lam             =  Emp
derive c Emp             =  Emp
derive c (Sym d)         =  if c==d then Lam else Emp
derive c (Rep re)        =  smartCat [derive c re, Rep re]
derive c (Opt re)        =  derive c re
derive c (Alt _ xs)      =  smartAlt [derive c x | x<-xs]
derive c (Cat _ (x:xs))  |  ewp x
                         =  smartAlt [dx,dxs]
                         |  otherwise
                         =  dx
                         where  dx   =  smartCat (derive c x : xs)
                                dxs  =  derive c (mkCat xs)

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

