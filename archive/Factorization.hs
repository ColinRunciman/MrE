module Factorization where

import Data.List (minimumBy)
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing, listToMaybe)
import Function (claim, justIf)
import List (allSplits, itemRest, mergeBy, powerSplits, sublistPairsOf, subsetRest)
import Expression
import Comparison
import Normalization
import Pressing
import Info
import Context

-- The next stage is factorization.  In an Alt, no component
-- should have a common prefix or suffix with another, nor
-- a prefix or suffix that is the same as another component.

type FactRE = RE

isFactorized :: RE -> Bool
isFactorized = checkWith factP

factEX :: Extension
factEX = mkExtension factAltListOne noChangeRule pressKP Factorized

factK :: Katahom
factK = khom factKP

factKP :: KataPred
factKP = target factEX

factP :: RecPred
factP = kpred factKP

Katahom { kalt = factAltK, kcat = factCatK } = factK
-- pressK = Katahom { kalt = pressAltK, kcat = pressCatK, grade = Pressed }

factH = mkHomTrans factK
HomTrans { falt = factAlt, fcat = factCat, frep = factRep, fopt = factOpt } = factH

factorize = fst . katahom factK NoCxt 

factCxt :: Cxt -> RE -> OK RE
factCxt = katahom factK
                            
-- plain factorizations, no re-factorings
(*-=->*) :: RE -> RE -> [RE] -- list result is a list of alternative results
c1 *-=->* c2           | isCat c1 || isCat c2
                       = mergeBy sizeOrder
                         [ factCat[xy,mkAlt[mkCat xs,mkCat ys]]
                         | (x,xs)<-prefixCom c1, (y,ys)<-prefixCom c2, Just xy<-[eqr x y]]
                         [ factCat[mkAlt[mkCat xs,mkCat ys],xy]  
                         | (xs,x)<-suffixCom c1, (ys,y)<-suffixCom c2, Just xy<-[eqr x y]]   
                       | otherwise
                       = []
                        
(*-=?->*) :: RE -> RE -> [RE]
c1 *-=?->* c2  =  mergeBy sizeOrder
                          [ x | not $ ewp c1, x <- (Opt c1 *-=->* c2)]
                          [ x | not $ ewp c2, x <- (c1 *-=->* Opt c2)]

altArity :: RE -> Maybe Int
altArity (Alt _ xs) = Just (length xs)
altArity (Opt x)    = altArity x
altArity _          = Nothing

factAltListOne :: RewRule -- Cxt -> Info -> [RE] -> OK [RE]
--factAltList :: Bool -> [FactRE] -> Maybe [FactRE]
factAltListOne c i []   =  unchanged []
factAltListOne c i [x]  =  unchanged [x]
factAltListOne c i xs   |  null candidates
                        =  unchanged xs
                        |  not $ hasChanged rec
                        =  list2OK xs candidates
                        |  otherwise
                        =  rec
                           where
                           rec        = factAltListOne c (altInfo headcand) headcand
                           -- TO DO: consider order of candidates, currently greedy
                           headcand   = head candidates
                           candidates = [ altList r ++ xs'
                                        | ([x,y],xs') <- subsetRest 2 xs, r <- (x *-=->* y) ] ++
                                        [ altList r ++ xs'
                                        | c>=EwpCxt, ([x,y],xs') <- subsetRest 2 xs, r <- (x *-=?->* y) ] ++
                                        [ altList r ++ ys2
                                        | (x,ys) <- itemRest xs, isCat x,
                                          x' <- unCat x, Just n <- [altArity x'],
                                          (ys1,ys2) <- subsetRest n ys,
                                          let yst1=mkAlt ys1,
                                          r <- (x *-=->* yst1)++[r'| c>=EwpCxt, r'<- (x *-=?->* yst1)]]

altList (Alt _ xs)        =  xs
altList (Opt x)           =  altList x -- 15/06/2016 was Lam:altList x, but rules are now allowed/encouraged to remove Lams
altList x                 =  [x]



