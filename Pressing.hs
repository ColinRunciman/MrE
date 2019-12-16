
module Pressing (
  press, pressAltListOne, pressCatListOne, pressP,
  rollList, prefixCom, suffixCom, pressKP ) where

import Data.List (minimumBy, nubBy, partition)
import Data.Maybe (fromJust, fromMaybe, isNothing, isJust, listToMaybe, catMaybes)
import Data.Ord (comparing)
import Function (claim, justIf, kernel, (===>))
import List (snoc, unsnoc, splits, allSplits, itemRest, subsetRest, lift2SeqAll, plural,
       unions, segPreSuf)
import Expression
import OK
import Comparison
import Context
import Fuse
import Info
import Stellation
import Alphabet
import Debug.Trace

-- Transformations in this module apply rules with conditions of language
-- equivalence or inclusion between REs.  These conditions are tested using
-- Comparison.(===) or Comparison.sublang.

isPressed :: RE -> Bool
isPressed = checkWith pressP

HomTrans { falt = pressAlt, fcat = pressCat, frep = pressRep, fopt = pressOpt } = pressH

(*///*) :: RE -> [RE] -> Maybe [RE]
x *///* xs = fmap (filter (not . isEmp)) $ lift2SeqAll (x *//*) xs

-- x *//* y tries to press y to become a smaller expression in
-- a context where it is an alternative to x.
-- If the result is Just w then x+w === x+y and size w < size y.

(*//*) :: RE -> RE -> Maybe RE
x        *//* x'         |  x' `sublang` x 
                         =  Just Emp
Opt x    *//* y          |  not $ ewp y
                         =  x *//* y
a@(Alt i (x:xs)) *//* y  |  isNothing y'
                         =  a' *//* y
                         |  isNothing y''
                         =  y'
                         |  otherwise
                         =  y''
                            where
                            y'  = x *//* y
                            y'' = a' *//* fromJust y'
                            a'  = altSubseq a xs
x        *//* Opt x'     |  ewp x && isNothing x''
                         =  Just x'
                         |  ewp x
                         =  x''
                         |  otherwise
                         =  fmap pressOpt x''
                            where x''= x *//* x'
x        *//* Rep y      |  istransitive y
                         =  x *//* Opt y
x        *//* Alt _ xs   =  fmap pressAlt $ x *///* xs
Rep x    *//* y          |  isJust y'
                         =  y'
                         |  otherwise
                         =  listToMaybe $
                            [ pressCat[b,re] | (b,bs)<-prefixCom y, not(null bs),
                                b `sublang` Rep x, Just re<-[Rep x *//* pressCat bs]] ++
                            [ pressCat[re,b] | (bs,b)<-suffixCom y, not(null bs),
                                b `sublang` Rep x, Just re<-[Rep x *//* pressCat bs]]
                            where
                            y' = x *//* y 
Sym d    *//* y          |  not (ewp y) && (d `elemAlpha` swa y) && isCat y
                         =  listToMaybe $ [ pressCat[Sym d, ntl] | (Sym d,tl) <- lMostCom' y,
                                            Just ntl <- [ Lam *//* mkCat tl] ]   ++
                                          [ pressCat[nlt, Sym d] | (lt,Sym d) <- rMostCom' y,
                                            Just nlt <- [ Lam *//* mkCat lt] ]                    
x        *//* y          |  isCat x && isCat y
                         =  listToMaybe $
                            [ pressCat[b,re] | (a,as)<-prefixCom x, (b,bs)<-prefixCom y,
                                b `sublang` a, Just re<-[pressCat as *//* pressCat bs]] ++
                            [ pressCat[re,b] | (as,a)<-suffixCom x, (bs,b)<-suffixCom y,
                                b `sublang` a, Just re<-[pressCat as *//* pressCat bs]]
_        *//* _          =  Nothing

-- This function supports the implementation of fusion rules for
-- Cat bodies of Opts, such as:
-- (XX*)? = X* and mirror
-- (X*(X+Y))? = X*Y? and mirror
-- (X(X?Y)?)? = X?(XY)? and mirror
-- (X(YX?)?)? = (XY)?X?
-- (X(X*+Y))? = X*+XY and mirror
-- (XY?)? = (XY)? if X `sublang` (XY)? and mirror

pressOptCatList :: RE -> [RE]
pressOptCatList x = case pressOpt x of
                    Cat _ xs -> xs
                    y        -> [y]

-- The (*?>*) function implements absorption from the left for successive items
-- in a Cat, where the Cat is in an optional context.
-- (X* X)? == X*
-- (X* Y)? == X* W?, where X *//* Y == Just W

(*?>*) :: RE -> RE -> Maybe [RE]
Rep x *?>* y         |  x===y
                     =  Just []
                     |  x `sublang` y
                     =  fmap ((:[]).pressOpt) (Rep x *//* y)
_     *?>* _         =  Nothing

-- The mirror of (*?>*).
(*<?*) :: RE -> RE -> Maybe [RE]
y     *<?* Rep x     |  x===y
                     =  Just []
                     |  x `sublang` y
                     =  fmap ((:[]).pressOpt) (Rep x *//* y)
_     *<?* _         =  Nothing

-- The (*=?=*) function implements the combination of successive Cat items,
-- where the Cat is in an optional context.
-- (XY*)?=(XZ*)*, if X sublang Y*, and Y\X sublang Z sublang X+Y, where X*//*Y == Just Z
-- (XY?)?=X+(XY)?, worthwhile if (XY)? can be reduced by other means

(*=?=*) :: RE -> RE -> Maybe [RE]
x     *=?=* y        |  ewp x && ewp y = Nothing -- in that case use standard fusion
Rep x *=?=* y        |  isJust yabs
                     =  fmap (Rep x :) yabs
                     |  y `sublang` Rep x && isJust xy
                     =  Just [pressRep(cat[rep $ fromJust xy,y])]
                        where
                        yabs    = Rep x *?>* y
                        xy      = y *//* x
y *=?=* Rep x        |  isJust yabs
                     =  fmap (++ [Rep x]) yabs
                     |  y `sublang` Rep x && isJust xy
                     =  Just [pressRep(cat[y,rep $ fromJust xy])]
                        where
                        yabs    = y *<?* Rep x
                        xy      = y *//* x
a@(Alt i xs) *=?=* x |  ew i && not (ewp x) && not(null cand1)
                     =  Just $ [pressAlt [rep x1, cat [altSubseq a xs',x1]]]
                        where
                        cand1 = [ (x',ys) | (Rep y,ys)<- itemRest xs, Just x'<-[eqr x y]]
                        (x1,xs') = head cand1
x *=?=* a@(Alt i xs) |  ew i && not(ewp x) && not (null cand1)
                     =  Just $ [pressAlt [ rep x1, cat [x1,altSubseq a xs']]]
                        where
                        cand1 = [ (x',ys) | (Rep y,ys)<- itemRest xs, Just x'<-[eqr x y]]
                        (x1,xs') = head cand1
Opt x *=?=* y        |  isCat x && not (null cand1)
                     =  Just  $ pressOptCatList(cat (yin ++ [yn])) ++ [Opt yn]
                     |  isCat x && not (null cand2)
                     =  Just $ pressOptCatList ym ++ pressOptCatList(cat(ytl ++[ym]))
                     where   
                     cand1 = [(y'',ys) | (ys,Opt y') <- rMostCom' x, Just y''<-[eqr y' y]]
                     (yn,yin) = head cand1
                     cand2 = [(y'',xs) | (Opt y',xs) <- lMostCom' x, Just y''<-[eqr y' y]]
                     (ym,ytl) = head cand2
y *=?=* Opt x        |  isCat x && not (null cand1)
                     =  Just $ pressOptCatList yn ++pressOptCatList(cat ([yn] ++ ytl))
                     |  isCat x && not (null cand2)
                     =  Just $ pressOptCatList(cat([ym] ++ yin)) ++ [ Opt ym]
                        where   
                        cand1 = [ (y'',ys) | (Opt y',ys) <- lMostCom' x, Just y''<-[eqr y' y]]
                        (yn,ytl) = head cand1
                        cand2 = [ (y'',xs) | (xs,Opt y') <- rMostCom' x, Just y''<-[eqr y' y]]
                        (ym,yin) = head cand2
_ *=?=* _            =  Nothing

-- The (*=*=*) function implements combination rules in Rep bodies.
-- (X(Y+Z))* = (X+Y'+Z)* if (XY)?=XY' and mirror
-- N.B. the resulting lists are Alt items, not Cat items.
(*=*=*) :: RE -> RE -> Maybe [RE]
x *=*=* Alt _ zs  |  ewp x && not (null cands)
                  =  listToMaybe cands
                     where
                     cands = [ concatMap whiteAltList (x' : (tail xy' ++ ys))
                              | (y,ys)<- itemRest zs, Just xy'<-[ x *=?=* y ], all ewp xy',
                                Just x' <- [eqr x (head xy')] ]
Alt _ zs *=*=* x  |  ewp x && (not $ null cands)
                  =  listToMaybe cands
                     where
                     cands = [ concatMap whiteAltList (x': (tail yx' ++ ys))
                             | (y,ys)<- itemRest zs, Just yx'<-[ y *=?=* x ], all ewp yx',
                               Just x' <- [ eqr x (last yx') ] ]
_ *=*=* _         =  Nothing

-- These comments probably attach to the (*==*) function.
-- X* (A+C) = X*(A'+C), if X*A = X*A' (includes: A=X*Y => A'=Y, A=X?Y => A'=Y), and mirror
-- (XY)? Z = X?Z, if Y? Z=Z
-- X* (A+C)? = X*(A'+C), if X*A? = X*A', in that case ewp A' will necessarily hold
-- (X+Y)Z = XZ+Y if YZ=Y; size preserving multiplication

toList :: RE -> [RE]
toList Lam        = []
toList (Cat _ xs) = xs
toList e          = [e]

-- The (*===*) implements rules for the combination of successive Cat items,
-- not requiring any specific context. It is a combined application of
-- (*>*), (*<*) and (*==*).

(*===*) :: RE -> RE -> Maybe[RE]
x *===* y      |  isJust absleft
               =  fmap (\z->x : toList z) absleft
               |  isJust absright
               =  fmap (\z->toList z ++[y]) absright
               |  otherwise
               =  fmap (:[]) $ x *==* y 
                  where
                  absleft = x *>* y
                  absright = x *<* y

-- Absorption from left where the rhs is in an optional context.
-- X* (Y+Z)? = X* (Y'+Z)? if  X*Y? = X*Y'?
-- X* Y?     = X*         if  Y sublang X*
-- X* Y?     = X* Z?      if  X*Y = X*Z
-- X* (YZ?)? = X* (YZ)?   if Y sublang X*
-- X* (YZ)?  = X* (YV)?   if Y sublang X* and X* *//* Z == Just V
-- (X+Y)?((X+Y+Z)?X)? = (X+Y)?((X+Y+Z)X)?

(*>?*) :: RE -> RE -> Maybe RE
x      *>?* Alt _ xs      =  fmap pressAlt $ lift2SeqAll (x *>?*) xs
Rep x  *>?* y             |  y `sublang` Rep x
                          =  Just Lam
                          |  not (null cand)
                          =  listToMaybe cand
                          |  otherwise
                          =  Rep x *>* y
                             where
                             cand = [ pressCat[npr,nsu]
                                    | (pre,suf)<-prefixCom y,
                                      (npr,nsu)<- [ (pre,nsuf)
                                                  | not(ewp pre), pre `sublang` Rep x,
                                                    Just nsuf<- [Rep x *//* mkCat suf] ] ++
                                                  [ (npre,suft)
                                                  | let suft=cat suf, not(ewp suft),
                                                    suft `sublang` Rep x,
                                                    Just npre<- [Rep x *//* pre]]]
Opt x  *>?* y             =  listToMaybe cand
                             where
                             cand = [ pressCat [nx,tlt]
                                    | (Opt x',tl)<- lMostCom' y, let tlt=pressCat tl,
                                      nx <- [ x' | x `sublang` x', tlt `sublang` x] ++
                                            [ Opt x'' | Just x''<- [Opt x *>?* x']] ]
x      *>?* y             =  Nothing

-- This is the mirror of (*>?*).

(*?<*) :: RE -> RE -> Maybe RE
Alt _ xs  *?<*     x      =  fmap pressAlt $ lift2SeqAll (*?<* x) xs
y         *?<* Rep x      |  y `sublang` Rep x
                          =  Just Lam
                          |  not (null cand)
                          =  listToMaybe cand
                          |  otherwise
                          =  y *<* Rep x
                             where
                             cand = [ pressCat[npr,nsu]
                                    | (pre,suf)<-prefixCom y,
                                      (npr,nsu)<- [ (pre,nsuf)
                                                  | not(ewp pre), pre `sublang` Rep x,
                                                    Just nsuf<- [Rep x *//* mkCat suf] ] ++
                                                  [ (npre,suft)
                                                  | let suft=cat suf, not(ewp suft),
                                                    suft `sublang` Rep x,
                                                    Just npre<- [Rep x *//* pre]]]
y        *?<* Opt x       =  listToMaybe cand
                             where
                             cand = [ pressCat [tlt,nx]
                                    | (lt,Opt x') <- rMostCom' y, let tlt=pressCat lt,
                                      nx <- [x' | x `sublang` x', tlt `sublang` x ] ++
                                            [ Opt x'' | Just x''<- [x' *?<* Opt x]] ]
_         *?<* _          =  Nothing

-- (*>*) implements absorption from left, with no specific context required.
-- If A *>* B gives Just C then AB == AC and size C < size B.
-- X* Y* = X* if Y sublang X*

(*>*) :: RE -> RE -> Maybe RE
Rep x  *>*  Rep y           =  justIf (y `sublang` Rep x) Lam --only way to absorb a Rep
x      *>*  Opt y           =  fmap pressOpt $ x *>?* y
x      *>*  c@(Cat _ _)     =  listToMaybe cands
                               where cands = [ nc | (y,ys) <- lMostCom' c,
                                                    Just y'<- [x *>* y],
                                                    let nc=pressCat(y':ys) ]
x      *>*  a@(Alt i _)     |  ew i
                            =  x *>?* a
x      *>*  Alt i xs        |  not (ew i)
                            =  fmap pressAlt $ lift2SeqAll (x *>*) xs
_      *>*  _               =  Nothing

-- mirror of *>*
(*<*) :: RE -> RE -> Maybe RE
Rep y          *<*  Rep x   =  justIf (y `sublang` Rep x) Lam
Opt y          *<*      x   =  fmap pressOpt $ y *?<* x
c@(Cat _ _)    *<*      x   =  listToMaybe cands
                               where cands = [ nc | (ys,y) <- rMostCom' c,
                                                    Just y'<- [y *<* x],
                                                    let nc=pressCat(ys++[y']) ]
a@(Alt i _)    *<*      x   |  ew i
                            =  a *?<* x
Alt i xs       *<*      x   |  not (ew i)
                            =  fmap pressAlt $ lift2SeqAll (*<* x) xs
_              *<*  _       =  Nothing


t *<=* u = listToMaybe $ [ r | Just r <- [t *==* u]] ++ [ pressCat[t',u] | Just t'<-[t*<*u] ]
t *>=* u = listToMaybe $ [ r | Just r <- [t *==* u]] ++ [ pressCat[t,u'] | Just u'<-[t*>*u] ]

-- fusion rules, excluding absorptions
-- (X*Y)X*=(X+Y)*
-- (X*Y)*X* = (X+Y)*, and mirror

(*==*) :: RE -> RE -> Maybe RE
Rep body *==* y       | ewp y && not (null candidates)
                      = Just $ head candidates
                        where
                        candidates = [ pressRep(alt [yb, cat tl])
                                     | (hd,tl)<-lMostCom' body,
                                       Just (Rep yb)<-[eqr hd y]]
y *==* Rep body       | ewp y && not (null candidates)
                      = Just $ head candidates
                        where
                        candidates = [ pressRep(alt [yb, cat lt])
                                     | (lt,dh)<-rMostCom' body,
                                       Just (Rep yb)<-[eqr dh y] ]
Opt x *==* Opt y      |  not (null cands)
                      =  listToMaybe cands
                         where
                         cands = [ t | y `sublang` x, let t=pressOpt(mkCat[x,Opt y]) ]
                                 ++
                                 [ t | x `sublang` y, let t=pressOpt(mkCat[Opt x,y]) ]
x *==* Opt y          |  not $ null cands
                      =  Just $ head cands
                      where
                      cands  = cands1++cands2
                      cands1 = [ pressAlt [x,xy]
                               | Just xy <-[x *<=* y], size xy <= size y ]
                      cands2 = [ pressAlt [x,txy]
                               | ewp x, Just xy<- [ x*===* y],
                                 let txy=pressCat xy, size txy <= size y ]
Opt y *==* x          |  not $ null cands
                      =  Just $ head cands
                      where
                      cands  = cands1 ++ cands2
                      cands1 = [ pressAlt [x,yx]
                               | Just yx <- [y *>=* x], size yx <= size y ]
                      cands2 = [ pressAlt [x,tyx]
                               | ewp x, Just yx<- [ y*===*x],
                                 let tyx=pressCat yx, size tyx <= size y ]
x *==* a@(Alt i xs)   | not(null cands) 
                      = Just $ head cands
                        where                       
                        cands = [ pressAlt [xy, cat [x, altSubseq a ys]]
                                | (y,ys) <- itemRest xs, Just xy <- [x *<=* y], size xy < size y ]
a@(Alt i xs) *==* x   | not(null cands) 
                      = Just $ head cands
                        where
                        cands = [ pressAlt [yx, cat [altSubseq a ys, x]]
                                | (y,ys) <- itemRest xs, Just yx <- [y *>=* x], size yx < size y]
x *==* c@(Cat _ xs)   | not $ null candidates
                      = Just $ head candidates
                        where
                        candidates =
                         [  pressCat(zs' ++ xy ++ ys') |
                               (zs,ys)<- allSplits xs, Just (zs',x') <- [rCom x zs],
                               (y,ys')<- lMostComList ys, Just xy <- [x' *===* y] ]
c@(Cat _ xs) *==* x   | not $ null candidates
                      = Just $ head candidates
                        where
                        candidates =
                         [  pressCat(ys' ++ yx ++ zs') |
                               (ys,zs)<- allSplits xs, Just (x',zs') <- [lCom zs x],
                               (ys',y)<- rMostComList ys, Just yx <- [y *===* x'] ]
x *==* y              |  ewp x && ewp y && subTransitive x y
                      =  Just $ pressRep(alt(concatMap whiteAltList [x,y]))
                      |  otherwise
                      =  Nothing

subTransitive :: RE -> RE -> Bool
subTransitive x y  =  let e = cat [x,y] in e === rep e

eqrListCommute :: [RE] -> Maybe RE
eqrListCommute (x:y:xs) |  x==y
                        =  eqrListCommute (y:xs)
                        |  otherwise
                        =  Nothing
eqrListCommute [x]      =  Just x
eqrListCommute []       =  Nothing

eqrCommute :: RE -> RE -> Maybe RE
eqrCommute x y = justIf (x==y) x

commute :: (RE,RE) -> Maybe (RE,RE)
commute (x, y) |  x == y
               =  Just (y,x)
               |  isJust cr
               =  cr
               |  isJust cl
               =  cl
               |  otherwise
               =  Nothing
                  where
                  cr           = commuteR (x,y)
                  cl           = commuteL (x,y)

-- commuteStrict does not commute identical elements

commuteStrict :: (RE,RE) -> Maybe (RE,RE)
commuteStrict (x,y) =  if x/=y then commute (x,y) else Nothing  

-- For commuting over Alt items, to the right.
commuteAlternativeR :: (RE,RE) -> Maybe(RE,RE)
commuteAlternativeR p            | isJust p'
                                 = p'
                                   where
                                   p' = commute p
commuteAlternativeR (x,Cat _ xs) = Just(previousCat(x:lt),dh)
                                   where Just(lt,dh)=unsnoc xs
commuteAlternativeR _            = Nothing

-- And the mirror function.
commuteAlternativeL :: (RE,RE) -> Maybe(RE,RE)
commuteAlternativeL p            | isJust p'
                                 = p'
                                   where p' = commute p
commuteAlternativeL (Cat _ xs,x) = Just(head xs,previousCat(tail xs++[x]))
commuteAlternativeL _            = Nothing

commuteR :: (RE,RE) -> Maybe (RE,RE)                 
commuteR (x, Alt _ ys)       |  all isJust coms && isJust eqrs
                             =  Just $ (pressAlt ys', x')
                                where coms       =  [commuteAlternativeR (x,y) | y <- ys]
                                      eqrs       =  eqrListCommute xs'
                                      Just x'    =  eqrs
                                      (ys',xs')  =  unzip $ map fromJust coms
commuteR (x, Cat _ ys)       |  isJust com
                             =  Just $ (pressCat ys', x')
                                where com = rCom x ys ; Just (ys',x') = com
commuteR (x, Rep (Cat i ys)) |  not $ null candidates
                             =  Just (pressRep $ cat nl, head nl)
                                where
                                candidates = [x' : init' | (init',x'') <- rMostCom'(Cat i ys),
                                                           Just x' <- [eqrCommute x'' x]]
                                nl=head candidates
commuteR (x, Rep y)          |  isJust com && x == x' && y == y'
                             =  Just (previousRep y, x) 
                                where com = commute (x,y); Just (y',x') = com
commuteR (x, Opt (Cat i ys)) |  not $ null candidates
                             =  Just (pressOpt $ cat nl, head nl)
                                where
                                candidates = [x':init'| (init',x'') <- rMostCom'(Cat i ys),
                                                        Just x' <- [eqrCommute x'' x]]
                                nl=head candidates
commuteR (x, Opt y)          |  isJust com && x == x'
                             =  Just (Opt y', x) 
                                where com = commute (x,y); Just (y',x') = com
commuteR _                   =  Nothing 


commuteL :: (RE,RE) -> Maybe (RE,RE)                 
commuteL (Alt _ xs, y)       |  all isJust coms && isJust eqrs
                             =  Just $ (y', pressAlt xs')
                                where coms       =  [commuteAlternativeL (x,y) | x <- xs]
                                      eqrs       =  eqrListCommute ys'
                                      Just y'    =  eqrs
                                      (ys',xs')  =  unzip $ map fromJust coms
commuteL (Cat _ xs, y)       |  isJust com
                             =  Just $ (y', pressCat xs')
                                where com = lCom xs y ; Just (y',xs') = com
commuteL (Rep (Cat i xs), y) |  not $ null candidates
                             =  Just (last nl, pressRep $ cat nl)
                                where
                                candidates = [tail'++[y'] | (y'',tail') <- lMostCom'(Cat i xs),
                                                           Just y' <- [eqrCommute y'' y]]
                                nl=head candidates
commuteL (Rep x, y)          |  isJust com && x == x' && y == y'
                             =  Just (y, previousRep x) 
                                where com = commute (x,y); Just (y',x') = com
commuteL (Opt (Cat i xs), y) |  not $ null candidates
                             =  Just (last c, pressOpt $ cat c)
                                where
                                candidates = [tail'++[y'] | (y'',tail') <- lMostCom'(Cat i xs),
                                                        Just y' <- [eqrCommute y'' y]]
                                c = head candidates
commuteL (Opt x, y)          |  isJust com && y == y'
                             =  Just (y, Opt x') 
                                where com = commute (x,y); Just (y',x') = com
commuteL _                   =  Nothing
    
-- lCom xs y = Just y' if y can commute through xs backwards
-- (ie. leftwards) arriving as y'; rCom is similar but forwards

lCom :: [RE] -> RE -> Maybe (RE,[RE])
lCom xs y  =  foldr lCom' (Just (y,[])) xs
  where
  lCom' _ Nothing          =  Nothing
  lCom' x (Just (y',xs'))  =  maybe Nothing (\(y'',x')-> Just (y'', x':xs')) $
                              commuteStrict (x,y')

rCom :: RE -> [RE] -> Maybe ([RE],RE)
rCom y xs  =  foldl rCom' (Just([], y)) xs
  where
  rCom' Nothing   _        =  Nothing
  rCom' (Just (xs',y')) x  =  maybe Nothing (\(x',y'')-> Just (snoc xs' x',y'')) $
                              commuteStrict (y',x)

suffixCom :: RE -> [([RE],RE)]
suffixCom x    =  nubBy (kernel snd) $
                  [ (xs',rollIfCat $ previousCat [suf,x])
                  | (xs,x) <- rMostCom' x,
                    (xs',suf) <- (xs,Lam) : suffixCom (mkCat xs) ] 

prefixCom :: RE -> [(RE,[RE])]
prefixCom x    =  nubBy (kernel fst) $
                  [ (rollIfCat $ previousCat [x,pre],xs')
                  | (x,xs) <- lMostCom' x,
                    (pre,xs') <- (Lam,xs) : prefixCom (mkCat xs) ] 

-- fi/la/ew/sw cannot change under rolling, but so we rebuild attributes
rollIfCat (Cat i xs) = mkCat $ rollList xs
rollIfCat x          = x

lMostCom :: Bool -> RE -> [(RE,[RE])]
lMostCom b x  =  [(pressOpt x,[]) | b] ++ lMostCom' x

-- NB: in both lMostCom'/rMostCom'  x' could be a Cat, hence recursive calls.
lMostCom' Lam           =  []
lMostCom' (Cat _ xs)    =  nubBy (kernel fst) $
                           [ (x'',xtl++pre'++suf) | (pre, x:suf) <- allSplits xs,
                                                    Just (x',pre') <- [lCom pre x],
                                                    (x'',xtl) <- lMostCom' x' ]
lMostCom' a@(Alt i xs)  =  (a,[]) : nubBy (kernel fst)
                           [ (hd,ntl) | (y,ys) <- itemRest xs, isCat y||any ewp ys,
                                        (hd,tl)<- lMostCom' y, ew i ===> ewp hd,
                                        let tlt=pressAlt(mkCat tl:ys),
                                        cat[hd,tlt]===a,
                                        let ntl=asList(tlt)]
lMostCom' x             =  [(x,[])]

asList (Cat _ xs) = xs
asList x          = [x]

-- For an alternative (Cat xs), lmostComList xs lists all the expressions that
-- could be brought to the head of xs, along with their corresponding tails,
-- using rules including:
-- XX? --> X?X, XX* --> X*X, X(YX)* --> (XY)*X, X(YX)? -> (XY)?X
-- N.B. These commuting rules reverse pressed order --- see pressCatNonSucc.
-- The 3rd rule changes (YX)* to (XY)*, which may change further after pressing.

-- avoiding the pattern lMostCom' . mkCat
lMostComList :: [RE] -> [(RE,[RE])]
lMostComList []  = []
lMostComList [x] = [(x,[])]
lMostComList xs  = nubBy (kernel fst) $
                           [ (x'',xtl++pre'++suf) | (pre, x:suf) <- allSplits xs,
                                                    Just (x',pre') <- [lCom pre x],
                                                    (x'',xtl) <- lMostCom' x' ]

rMostCom :: Bool -> RE -> [([RE],RE)]
rMostCom b x  =  [([],pressOpt x) | b] ++ rMostCom' x

rMostCom' Lam           =  []
rMostCom' (Cat _ xs)    =  nubBy (kernel snd) $ 
                           [ (pre++suf'++xin,x'') | (pre, x:suf) <- allSplits xs,
                                                    Just (suf',x') <- [rCom x suf],
                                                    (xin,x'') <- rMostCom'  x' ]
rMostCom' a@(Alt i xs)  =  ([],a) : nubBy (kernel snd) 
                           [ (nlt,dh) | (y,ys) <- itemRest xs, isCat y||any ewp ys,
                                        (lt,dh)<- rMostCom' y, ew i ===> ewp dh,
                                        let tlt=pressAlt(mkCat lt:ys),
                                        cat[tlt,dh]===a,
                                        let nlt=asList(tlt)]
rMostCom' x             =  [([],x)]

-- avoiding rMostCom' . mkCat
rMostComList :: [RE] -> [([RE],RE)]
rMostComList []   =  []
rMostComList [x]  =  [([],x)]
rMostComList xs   =  nubBy (kernel snd) $ 
                           [ (pre++suf'++xin,x'') | (pre, x:suf) <- allSplits xs,
                                                    Just (suf',x') <- [rCom x suf],
                                                    (xin,x'') <- rMostCom'  x' ]

-- to be used on lists that have no fusion-opportunities
-- i.e. catP pressP False xs
rollList :: [RE] -> [RE]
rollList xs  |  rolled xs
             =  xs
             |  otherwise
             =  rollList (rollPass xs)

-- formerly, rollList was just rollPass
rollPass :: [RE] -> [RE]
rollPass []  = []
rollPass [x] = [x]
rollPass xs  = m : rollPass (flat tl)
    where
    (m,tl)  =  minimumBy (comparing fst) $ lMostComList xs
    flat []               =  []
    flat (Cat _ xs : ys)  =  flat (xs++ys)
    flat (x: xs)          =  x: flat xs

rolled :: [RE] -> Bool
rolled [] = True
rolled (x:xs) = all (\(y,ys)->x<=y)(lMostComList (x:xs)) && rolled xs

--------------- NEW STUFF BELOW ---------------------------------------------------------------------------------
previousKP :: KataPred
previousKP  =  stelKP

previousH :: HomTrans
previousH  =  mkHomTrans $ khom previousKP

HomTrans {falt = previousAlt, fcat = previousCat, 
          fopt = previousOpt, frep = previousRep }  =  previousH

pressEX :: Extension
pressEX = extensionLtd 15 20 $
          mkExtension pressAltListOne pressCatListOne previousKP Pressed

pressK :: Katahom
pressK = khom pressKP

pressKP :: KataPred
pressKP = target pressEX

pressP :: RecPred
pressP = kpred pressKP

Katahom { kalt = pressAltK, kcat = pressCatK } = pressK

pressH = mkHomTrans pressK
press = extension2trafo pressEX

pressCxt :: Cxt -> RE -> OK RE
pressCxt = katahom pressK

-- non-generic
pressAltListOne :: Cxt -> Info -> [RE] -> OK [RE]
pressAltListOne c i xs = symbolFactorTrafo i xs `orOK`
                         thinAltList c xs `orOK`
                         factAltElem c xs `orOK`
                         factList xs

thinAltList :: Cxt -> [RE] -> OK [RE]
thinAltList c xs = list2OK xs $ [ (z:ys) | (y,ys)<- itemRest xs,
                                           let others=contextFunction c (mkAlt ys),
                                           z <- catMaybes [others *//* y] ]   

-- factorization modulo rolling; because of symbol-optimizations 
-- this will not bite for small regexp
-- because common symbol factors are eliminated before we look at this, we can eliminate the case
factList :: [RE] -> OK [RE]
factList xs = list2OK xs [ match:xs' |([x,y],xs') <- subsetRest 2 xs,
                           match <- [ pressCat[he,mkAlt[mkCat xtl,mkCat ytl]]
                                    | let lmx=lMostCom' x, let lmy=lMostCom' y,
                                      (xhe,xtl)<-lmx, not (isSym xhe), (yhe,ytl)<-lmy,
                                      Just he<-[eqr xhe yhe]] ++
                                    [ pressCat[mkAlt[mkCat xin,mkCat yin],la]
                                    | let rmx=rMostCom' x, let rmy=rMostCom' y,
                                      (xin,xla)<-rmx, not(isSym xla), (yin,yla)<-rmy,
                                      Just la<-[eqr xla yla]] ++
                                    [ pressCat[hd,tlt] | (hd,tl)<-lMostCom'(mkAlt[x,y]), not(null tl),
                                      let tlt=pressCat tl, size hd+size tlt<size x+size y] ++
                                    [ pressCat[tlt,dh] | (lt,dh)<-rMostCom'(mkAlt[x,y]), not(null lt),
                                      let tlt=pressCat lt, size dh+size tlt<size x+size y] ]


-- factorization of a single element against the remainder of the alternatives;
-- context has to be taken into account
-- size condition is needed because a?b+ba=ab+ba?
factAltElem :: Cxt -> [RE] -> OK [RE]
factAltElem c xs = list2OK xs
                   [ res | (y,ys)<-itemRest xs,
                           res <- [ result
                                  | (pre,suf)<- prefixCom y, let suft=mkCat suf,
                                    not $ ewp suft, pre `sublang` lang, 
                                    Just nys<- [cf pre *///* ys],
                                    let result=pressCat[pre,Opt suft]: nys,
                                    listSize result<listSize xs ] ++
                                  [ result

                                  | (pre,suf)<- suffixCom y, let pret=mkCat pre,
                                    not $ ewp pret, suf `sublang` lang,
                                    Just nys<- [cf suf *///* ys],
                                    let result=pressCat[Opt pret,suf]: nys,
                                    listSize result<listSize xs ] ]                               
                    where
                    cf    =  contextFunction c        
                    lang  =  cf (alt xs)

-- is a Cat really an Alt? only try for nullable cats!
catSplit :: [RE] -> OK [RE]
catSplit xs = list2OK xs
                [ [press nx] | (pre,suf)<- prefixCom x, not(null suf), let suft=cat suf,
                  let nx=alt[pre,suft], nx === x]
              where
              x     = cat xs

-- accelerated factorization for symbols
-- we can only factorize symbols from cats that are non-nullable
-- and whose first/last symbol can only be that symbol
symbolFactorTrafo :: Info -> [RE] -> OK [RE]
symbolFactorTrafo i xs  |  plural nonewxs && (plural sglcL || plural sglcR)
                        =  list2OK xs (leftCands ++ rightCands)
                        |  otherwise
                        =  unchanged xs
                       where
                       (ewxs,nonewxs) = partition ewp xs
                       (plnonL,sglcL) = partition (pluralAlpha . fir) nonewxs
                       (plnonR,sglcR) = partition (pluralAlpha . las) nonewxs
                       leftCands = [ pressCat[Sym cx,nt] : (ys++plnonL++ewxs) |
                                     ([x,y],ys) <- subsetRest 2 sglcL,
                                     let lmx=lMostCom' x, let lmy=lMostCom' y, --because of backtracking
                                     (Sym cx,tlx)<- lmx,
                                     (Sym cy,tly)<- lmy, cx==cy,
                                     let nt=alt[cat tlx,cat tly] ]
                       rightCands = [ pressCat[ni,Sym cx] : (ys++plnonR++ewxs) |
                                     ([x,y],ys) <- subsetRest 2 sglcR,
                                     let rmx=rMostCom' x, let rmy=rMostCom' y,
                                     (inx,Sym cx)<- rmx,
                                     (iny,Sym cy)<- rmy, cx==cy,
                                     let ni=alt[cat inx,cat iny] ]

----------- Cat section for the Katahom ----------------------
   
-- one rewrite step, result not in pressed form in general
pressCatListOne :: Cxt -> Info -> [RE] -> OK [RE]
pressCatListOne c i xs  =  
           pressCatListOK xs `orOK`
           ( guardOK (c>=EwpCxt) (plus2star c xs)
           $ guardOK (c==RepCxt) (presspreviousCatRepCxt xs)
           $ guardOK (c==OptCxt && not(ew i)) (presspreviousCatOptCxt xs)
           $ guardOK (ew i) (catSplit xs)
           $ rollPress xs )

pressCatListOK :: [RE] -> OK [RE]
pressCatListOK xs = list2OK xs $ candidatesFrom [] xs
    where
    candidatesFrom _   []   =  []
    candidatesFrom pre suf  =  concat [ [ pre'++mid++suf'
                                        | not $ null pre,
                                          (pre',x) <- rMostComList pre,
                                          Just mid <- [x *===* y] ] ++
                                        candidatesFrom (pre++[y]) suf'
                                      | (y,suf') <- lMostComList suf ]

pressCatListRepOK :: [RE] -> OK [RE]
pressCatListRepOK xs = list2OK xs $ 
    [ pre ++ (t:suf)| (p,suf) <- prefixCom(mkCat xs), all ewp suf,
                      (pre,m) <- suffixCom p, all ewp pre,
                      (l,r)   <- prefixCom m, not (null r),
                      Just t <- [ l *=+=* (mkCat r) ]]
        
-- fusion in a transitive, non-star context
(*=+=*) :: RE -> RE -> Maybe RE
x *=+=* y = listToMaybe $ [pressCat [x,z] | ewp y, Just z <- [ x **>* y ]] ++
                          [pressCat [z,y] | ewp x, Just z <- [ x *<** y ]]

-- absorption in a transitive context
-- the absorbing expression is on the left
-- the absorbee is either nullable or in a nullable context
-- laws:
-- y `sublang` x implies (xy?)^+ = x^+
-- (xz?)^+ = (xe?)^+ implies (x(z+y)?)^+ = (x(e+y)?)^+
-- (xz?)^+ = (xe?)^+ implies (xz??)^+ = (xe?)^+
-- no law for Rep
(**>*) :: RE -> RE -> Maybe RE
x **>* y          | y `sublang` rep x = Just Lam
x **>* (Alt _ xs) = listToMaybe [ pressAlt (e:zs) | (z,zs)<-itemRest xs, Just e<-[ x **>* z ]]
x **>* (Opt y)    = fmap pressOpt (x **>* y)
_ **>* _          = Nothing

-- dual to the above
(*<**) :: RE -> RE -> Maybe RE
y *<** x          | y `sublang` rep x = Just Lam
(Alt _ xs) *<** x = listToMaybe [ pressAlt (e:zs) | (z,zs)<-itemRest xs, Just e<-[ z *<** x ]]
(Opt y) *<** x    = fmap pressOpt (y *<** x)
_ *<** _          = Nothing

-- Note: size condition necessary, because *//* can succeed with merely knocking a Lam off
-- SMK 23072019, addition of pressCatListRepOK
presspreviousCatRepCxt :: [RE] -> OK [RE]
presspreviousCatRepCxt xs  =  list2OK xs can `orOK` pressCatListRepOK xs
           where
           x    =  previousCat xs
           xr   =  rep x
           can  =  cands1 ++ cands2 ++ cands3 ++ cands4
           cands1 = [ [p,newsuf] | (p,suf) <- prefixCom x, not (null suf), p `sublang` xr,
                                      let oldsuf=previousCat suf, Just z <-[ previousRep p *//* oldsuf],
                                      let newsuf=previousOpt z, size newsuf < size oldsuf ]
           cands2 = [ [newpre,s] | (pre,s)<- suffixCom x, not (null pre), s `sublang` xr,
                                      let oldpre=previousCat pre, Just z <-[ previousRep s *//* oldpre],
                                      let newpre=previousOpt z, size newpre < size oldpre]
           cands3 = [ (prep:suf) |  (p,suf)<-prefixCom x, ewp p, not(isRep p),
                      let prep=rep p, cat [xr,p]===prep]
           cands4 = [ (pre++[srep]) | (pre,s)<-suffixCom x, ewp s, not(isRep s),
                      let srep=rep s, cat [s,xr]===srep]

plus2starOpt :: [RE] -> Maybe [RE]
plus2starOpt xs | hasChanged call
                = Just (valOf call)
                | otherwise
                = Nothing
                  where call = plus2star OptCxt xs

-- this used to be pressOpt' within pressOpt
-- uses (H*T)?==(H*T?) whenever sound, provided it gives rise to fusion
-- ditto (H?T)? == H?T?, and mirrors
-- size condition is needed to stop circular rotations
presspreviousCatOptCxt :: [RE] -> OK [RE]
presspreviousCatOptCxt xs = unchanged xs -- now these go in the wrong direction
       where
       x        =  previousCat xs
       xo       =  opt x
       can      =  lca ++ rca 
       lca      =  [ res | (he,tl) <- prefixCom x, not(null tl), ewp he, he `sublang` xo,
                           let tln =  pressCatListOne OptCxt (catInfo tl) tl,
                           Just res <- [ Just (he : valOf tln) | plural tl, hasChanged tln, listSize (valOf tln)<listSize tl ] ++
                                       [ he *===* mkCat tl] ]
       rca      =  [ res | (lt,la) <- suffixCom x, not(null lt), ewp la, la `sublang` xo,
                           let ltn =  pressCatListOne OptCxt (catInfo lt) lt,
                           Just res <- [ Just (valOf ltn ++ [la]) | plural lt, hasChanged ltn, listSize (valOf ltn)<listSize lt ] ++
                                       [ mkCat lt *===* la] ]

rollPress :: [RE] -> OK [RE]
rollPress xs = updateEQ xs (rollList xs)

-- plus2star presses cat-sequences in any optional context

plus2star :: Cxt -> [RE] -> OK [RE]
plus2star c ys   =  repfix $ list2OK ys cands
    where
    repfix zs    |  hasChanged zs && c==RepCxt && all ewp (valOf zs)
                 =  changed [ valOf $ pressCxt c (mkAlt (valOf zs)) ]
                 |  otherwise
                 =  zs
    r            =  c==RepCxt
    cands        =  leftCands ++ rightCands ++ leftReps ++ rightReps
    leftCands    =  [ p
                    | (hd,tl)<- lMostComList ys, let tl'=previousCat tl, Just p <-[hd *=?=* tl']]
    leftReps     =  [ [previousAlt p]
                    | r, (hd,tl)<- lMostComList ys, let tl'=previousCat tl, Just p <-[hd *=*=* tl']]
    rightCands   =  [ p
                    | (lt,dh)<- rMostComList ys, let lt'=previousCat lt, Just p <-[lt' *=?=* dh]]
    rightReps    =  [ [previousAlt p]
                    | r, (lt,dh)<- rMostComList ys, let lt'=previousCat lt, Just p <-[lt' *=*=* dh]]

-- X+Y --> X if Y `sublang` X 
-- ...+XX*+... -> ...+X*+... if ewp(alt), and mirrored law

-- X*Y*     --> Y* if X `sublang` Y*, or X* if Y `sublang` X*
-- X*Y?     --> X* if Y `sublang` X*
-- X?Y*     --> Y* if X `sublang` Y*
-- X*(YX*)* --> (X+Y)*, and mirror
-- (XY)*X   --> X(YX)*
-- X*X      --> XX*
-- X?X      --> XX?

-- (X+Y)* --> X* if Y subset X* (generalizes Salomaa star rule: (X+1)* --> X*) 
-- (XY*)* --> X* if Y `sublang` X* and mirror
-- (XY?)* --> X* if Y `sublang` X* and mirror

-- (XY*)? --> X?Y* if Y `sublang` X? and mirror
-- (XY?)? --> X?Y? if Y `sublang` X? and mirror
-- (XX*)? --> X* and mirror

