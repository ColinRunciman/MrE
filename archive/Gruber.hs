module Gruber where
import Data.Char
import Expression
import Info -- to memoize ewp
newtype GG = GG { re :: RE }

instance Read GG where
  readsPrec _ s  = [restGG s [[[]]]]

ggrep = GG . Rep . re
ggopt = GG . Opt . re
ggsym = GG . Sym

restGG :: String -> [[[GG]]] -> (GG,String)
restGG ""      (    a:as) = if null as then (a2reGG a,"")
                            else ggwrong
restGG ('+':s) ((c:a):as) = if null c then ggwrong
			    else restGG s (([]:c:a):as)
restGG ('*':s) ((c:a):as)   = case c of
                              []     -> ggwrong
                              (x:xs) -> restGG s (((ggrep x:xs):a):as)
restGG ('?':s) ((c:a):as) = case c of
                            []     -> ggwrong
                            (x:xs) -> restGG s (((ggopt x:xs):a):as)
restGG ('0':s) ((c:a):as) = restGG s (((GG Emp:c):a):as)
restGG ('1':s) ((c:a):as) = restGG s (((GG Lam:c):a):as)
restGG ('(':s) as         = restGG s ([[]]:as)
restGG (')':s) (a:as)     = case as of
                            [] -> if null as then (a2reGG a,')':s) else ggwrong 
			    ((c:a'):as') -> restGG s (((a2reGG a:c):a'):as')
restGG (' ':s) as         = restGG s as
restGG ('.':s) ((c:a):as) = restGG s (((ggsym '.':c):a):as) -- allow for '.' as special symbol
restGG (v  :s) ((c:a):as) = if isAlpha v then restGG s (((ggsym v:c):a):as)
                            else if null as then (a2reGG (c:a),v:s)
			    else ggwrong
			      
a2reGG :: [[GG]] -> GG
a2reGG = ggalt . reverse . map (ggcat . reverse)

ggwrong = error "unreadable RE"

ggcat :: [GG] -> GG
ggcat xs |  any (isEmp.re) xs'
         =  GG Emp
         |  otherwise
         =  GG $ Cat undefined (map re xs')
  where
  xs' = filter (not.isLam.re) xs

ggalt :: [GG] -> GG
ggalt xs = mkGGalt (filter(not.isEmp.re) xs)

mkGGalt []  = GG Emp
mkGGalt [x] = x
mkGGalt xs  = GG $ Alt undefined (map re xs)

ggewp = nullable . re
nullable = foldHom ewpHom

ewpHom :: Hom Bool
ewpHom = Hom { hemp=False, hlam=True, hsym=const False, halt=or, hcat=and, hrep=const True, hopt=const True }

blop, blopEWP :: GG -> RE
blop = foldHom blopHom . re
blopEWP = foldHom blopHomEWP . re

blopHom = Hom { hemp=Emp, hlam=Lam, hsym=Sym, halt=blopAlt, hcat=blopCat, hrep=blopRep, hopt=blopOpt }

blopHomEWP = Hom { hemp=Emp, hlam=Lam, hsym=Sym,
                   halt=blopAltEWP, hcat=blopCatEWP, hrep=blopRepEWP, hopt=blopOptEWP }

blopAlt xs |  any isLam xs
           =  blopOpt $ ba (filter (not . isLam) xs)
           |  otherwise
           =  ba xs
              where
              ba []  = Emp
              ba [x] = x
              ba xs  = Alt undefined xs

-- blopAltEWP xs = Alt (newInfo $ any ewp xs) xs
blopAltEWP xs = ba xs [] False False
                where
                ba (Opt x:zs) ys lamRem otherOpt = ba zs (x:ys) True otherOpt
                ba (x    :zs) ys lamRem otherOpt = ba zs (x:ys) lamRem (otherOpt || ewp x)
                ba []         ys lamRem otherOpt | otherOpt
                                                 = Alt (newInfo True) ys
                                                 | lamRem
                                                 = Opt (Alt (newInfo False) ys)
                                                 | otherwise
                                                 = Alt (newInfo False) ys

blopCatEWP xs = Cat (newInfo $ all ewp xs) xs

blopCat xs = bc (filter (not . isLam) xs)
             where
             bc []  = Lam
             bc [x] = x
             bc xs  = Cat undefined xs

blopRepEWP x = brep (bwhiteEWP x)
blopRep x = brep (bwhite x)

brep Emp = Lam
brep x   = Rep x

blopOpt x | nullable x
          = x
          | otherwise
          = Opt x

blopOptEWP x = if ewp x then x else Opt x
             
bwhiteEWP x   | not(ewp x)
              = x
bwhiteEWP Lam = Emp
bwhiteEWP (Alt i xs) = Alt i (map bwhiteEWP xs)
bwhiteEWP (Cat i xs) = Cat i (map bwhiteEWP xs)
bwhiteEWP (Rep x)    = bwhiteEWP x
bwhiteEWP (Opt x)    = bwhiteEWP x

bwhite x   | not(nullable x)
           = x
bwhite Lam = Emp
bwhite (Alt _ xs) = Alt undefined (map bwhite xs)
bwhite (Cat _ xs) = Cat undefined (map bwhite xs)
bwhite (Rep x)    = bwhite x
bwhite (Opt x)    = bwhite x

ggtrans :: String -> RE
ggtrans s = blop $ read s

ggtransEWP s = blopEWP $ read s

ggsize x = oldSize (re x)



