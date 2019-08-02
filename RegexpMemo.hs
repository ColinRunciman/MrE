module RegexpMemo where

import Data.Map.Strict as M
import Context
import Expression
{- first version, requires kataCat etc.

data MemoTable b = MemoTable {
   cham :: M.Map Char b,
   catm :: MemoTable (MemoTable b),
   altm :: MemoTable (MemoTable b),
   repm :: MemoTable b,
   optm :: MemoTable b }
-}

{- one could use more context-aware memo tables:
data ListTable t b = ListTable {
    nilm  :: b,
    consm :: t (ListTable b)
}

type AltListTable b = ListTable AltElemTable b
type CatListTable b = ListTable CatElemTable b

data AltElemTable b = AltElemTable {
    chaaltm :: M.Map Char b,
    cataltm :: CatListTable b,
    repaltm :: NonnullTable b
}

data CatElemTable b = CatElemTable {
   chacatm :: M.Map Char b,
   altcatm :: AltListTable b,
   repcatm :: Nonnulltable b,
   optcatm :: Nonnulltable b }

data NonnullTable b = {
   channm :: M.Map Char b,
   catnnm :: CatListTable b,
   altnnm :: AltListTable b }
-}

data MemoTable b = MemoTable {
   cham :: M.Map Char b,
   catm :: MemoTable (ListTable b),
   altm :: MemoTable (ListTable b),
   repm :: MemoTable b,
   optm :: MemoTable b }

data ListTable b = ListTable {
    nilm  :: b,
    consm :: MemoTable (ListTable b)
}

lookupList :: ListTable b -> [RE] -> b
lookupList t [] = nilm t
lookupList t (x:xs) = lookupList (lookupM (consm t) x) xs

{- old version, with kataAlt & kataCat: 
lookupM :: MemoTable b -> RE -> b
lookupM t (Sym s) = cham t M.! s
lookupM t (Alt _ (x:xs)) = lookupM (lookupM (altm t) x)(kataAlt xs)
lookupM t (Cat _ (x:xs)) = lookupM (lookupM (catm t) x)(kataCat xs)
lookupM t (Rep x)        = lookupM (repm t) x
lookupM t (Opt x)        = lookupM (optm t) x
-}

lookupM :: MemoTable b -> RE -> b
lookupM t (Sym s) = cham t M.! s
lookupM t (Alt _ (x:xs)) = lookupList (lookupM (altm t) x) xs
lookupM t (Cat _ (x:xs)) = lookupList (lookupM (catm t) x) xs
lookupM t (Rep x)        = lookupM (repm t) x
lookupM t (Opt x)        = lookupM (optm t) x



{- old version, with kataCat & kataAlt :
tabulate :: [Char] -> (RE -> b) -> MemoTable b
tabulate cs f = MemoTable {
    cham = M.fromList [(x,f (Sym x))| x<-cs],
    catm = tabulate cs (\i1 -> tabulate cs (\i2 -> f (kataCat [i1,i2]))),
    altm = tabulate cs (\i1 -> tabulate cs (\i2 -> f (kataAlt [i1,i2]))),
    repm = tabulate cs (\x-> f (Rep x)),
    optm = tabulate cs (\x-> f (Opt x))
 }
-}

tabulateList :: [Char] -> ([RE]->b) -> ListTable b
tabulateList cs f = ListTable {
    nilm  = f [],
    consm = tabulate cs (\x-> tabulateList cs (\ds -> f (x:ds)))
}

tabulate :: [Char] -> (RE -> b) -> MemoTable b
tabulate cs f = MemoTable {
    cham = M.fromList [(x,f (Sym x))| x<-cs],
    catm = tabulate cs (\i1 -> tabulateList cs (\i2 -> f (kataCat (i1:i2)))),
    altm = tabulate cs (\i1 -> tabulateList cs (\i2 -> f (kataAlt (i1:i2)))),
    repm = tabulate cs (\x-> f (Rep x)),
    optm = tabulate cs (\x-> f (Opt x))
 }

deriveGeneric :: HomTrans -> [Char] -> Char -> RE -> RE
deriveGeneric ht cs c = dTop
                 where
                 mem = tabulate cs dGen
                 dTop Emp = Emp
                 dTop Lam = Emp
                 dTop x   = lookupM mem x
                 dGenM    = lookupM mem
                 dGen Lam        = Emp
                 dGen Emp        = Emp
                 dGen (Sym d)    = if c==d then Lam else Emp
                 dGen (Rep re)   = fcat ht [dGenM re, Rep re]
                 dGen (Opt re)   = dGenM re
                 dGen (Alt _ xs) = falt ht [dGenM x | x<-xs]
                 dGen (Cat _ (x:xs))  |  ewp x
                                      =  falt ht [dx,dxs]
                                      |  otherwise
                                      =  dx
                                         where  dx   =  fcat ht (dGenM x : xs)
                                                dxs  =  dGenM (fcat ht xs)
deriveKat :: [Char] -> Char -> RE -> RE
deriveKat = deriveGeneric kataGradeH

derivationGroup :: [Char] -> Derivation
derivationGroup cs = M.fromList [ (c,deriveKat cs c) | c<- cs]

derivationGroupGeneric :: HomTrans -> [Char] -> Derivation
derivationGroupGeneric ht cs = M.fromList [ (c,deriveGeneric ht cs c) | c <- cs]


type Derivation = M.Map Char (RE->RE)

deriv :: Derivation -> Char -> RE -> RE
deriv der c = der M.! c

