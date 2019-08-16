module Derivative (derive) where

import Expression
import Alphabet
import Info
import List

-- This module supports Comparison.  The derive function is standard:
-- given an expression e and an initial character c the result is an
-- expression e' such that L(e') = {w | cw <- L(e)}.
-- N.B. Repeated application of derive gives only a finite set of REs

derive :: Char -> RE -> RE
derive c e = alt $ map cat $ deriveAlts c e []

deriveAlts :: Char -> RE -> [RE] -> [[RE]]
deriveAlts c (Sym d)    cont   =  [cont | c==d]
deriveAlts c (Alt i xs) cont   |  elemAlpha c (fi i)
                               =  unions [ deriveAlts c x cont | x<-xs ]
deriveAlts c (Cat i xs) cont   |  elemAlpha c (fi i)
                               =  deriveCatList c xs cont
deriveAlts c (Opt x) cont      =  deriveAlts c x cont
deriveAlts c (Rep x) cont      =  deriveAlts c x (Rep x:cont)
deriveAlts c _ _               =  [] -- Lam or Emp, or bad (fi i)

-- can assume: char can be first character
deriveCatList :: Char -> [RE] -> [RE] -> [[RE]]
deriveCatList c (x:xs) cont   |  not (elemAlpha c (fir x)) -- x must be optional
                              =  tailDerive
                              |  not (ewp x) || not (firstCharList c xs)
                              =  headDerive
                              |  otherwise -- c can be knocked off either way
                              =  tailDerive `nubMerge` headDerive
                                 where
                                 headDerive = deriveAlts c x (xs++cont)
                                 tailDerive = deriveCatList c xs cont

firstCharList :: Char -> [RE] -> Bool
firstCharList c []     = False
firstCharList c (x:xs) = elemAlpha c (fir x) || ewp x && firstCharList c xs
