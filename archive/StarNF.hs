module StarNF where
import Expression
import Info
--------------------------------------------------------------------------------
nonnull :: Info
nonnull = newInfo False

semOpt :: RE -> RE
semOpt Emp = Lam
semOpt x    | ewp x
            = x
            | otherwise
            = Opt x


-- strong star query flat normal form
ssqfnf :: RE -> RE
ssqfnf Emp = Emp
ssqfnf Lam = Lam
ssqfnf x   | ewp x
           = semOpt $ addAlt x Emp
           | otherwise
           = addAlt x Emp

-- can remove Lam from language
addAlt (Alt i [x,y]) z = addAlt x $ addAlt y z
addAlt (Opt x) z =       addAlt x z
addAlt (Rep x) y       = addElem (Rep $ white x) y
addAlt (Cat i [x,y]) z = addElem (addCat x (ssqfnf y)) z
addAlt x z             = addElem x z

addElem x Emp          = x
addElem x (Alt i xs)   = Alt (newInfo (ewp x||ew i))  (x:xs)
addElem x y            = Alt (newInfo (ewp x||ewp y)) [x,y]

addCat :: RE -> RE -> RE
addCat (Cat _ [x,y]) z = addCat x (addCat y z)
addCat x z             = addCatElem (ssqfnf x) z

addCatElem x (Cat i xs) = Cat (newInfo (ewp x&&ew i)) (x:xs)
addCatElem x y          = Cat (newInfo (ewp x&&ewp y)) [x,y]

white :: RE -> RE
white (Alt _ [x,y]) = addAltWhite x (white y)
white (Cat i [x,y]) | ew i
                    = addAltWhite x (white y)
                    | otherwise
                    = addCat x (ssqfnf y)
white (Rep x)       = white x
white (Opt x)       = white x
white x             = x

addAltWhite :: RE -> RE -> RE
addAltWhite (Rep x) y       = addAltWhite x y
addAltWhite (Opt x) y       = addAltWhite x y
addAltWhite (Alt _ [x,y]) z = addAltWhite x (addAltWhite y z)
addAltWhite (Cat i [x,y]) z | ew i
                            = addAltWhite x (addAltWhite y z)
                            | otherwise
                            = addElem (addCat x (ssqfnf y)) z
addAltWhite c (Alt _ xs)    = Alt nonnull (c:xs)
addAltWhite c x             = Alt nonnull [c,x]


ssnf :: RE -> RE
ssnf (Alt i xs) = Alt i (map ssnf xs)
ssnf (Cat i xs) = Cat i (map ssnf xs)
ssnf (Rep x)    = Rep $ whiteSSNF x
ssnf (Opt x)    | ewp x
                = ssnf x
                | otherwise
                = Opt (ssnf x)
ssnf x          = x

whiteSSNF :: RE -> RE
whiteSSNF (Alt i xs) = Alt nonnull (map whiteSSNF xs)
whiteSSNF (Cat i xs) | ew i
                     = Alt nonnull (map whiteSSNF xs)
                     | otherwise
                     = Cat nonnull (map ssnf xs)
whiteSSNF (Rep x)    = whiteSSNF x
whiteSSNF (Opt x)    = whiteSSNF x
whiteSSNF x          = x -- Lam/Emp cannot occur anymore

-- same as above, but using nonmemoEWP rather than ewp
nonmemoSsnf :: RE -> RE
nonmemoSsnf (Alt i xs) = Alt i (map nonmemoSsnf xs)
nonmemoSsnf (Cat i xs) = Cat i (map nonmemoSsnf xs)
nonmemoSsnf (Rep x)    = Rep $ nonmemoWhiteSSNF x
nonmemoSsnf (Opt x)    | nonMemoEWP x
                       = nonmemoSsnfsnf x
                       | otherwise
                       = Opt (nonmemoSsnf x)
nonmemoSsnf x          = x

nonmemoWhiteSSNF :: RE -> RE
nonmemoWhiteSSNF (Alt _ xs) = Alt nonnull (map nonmemoWhiteSSNF xs)
nonmemoWhiteSSNF (Cat _ xs) | all nonmemoEWP xs
                     = Alt nonnull (map nonmemoWhiteSSNF xs)
                     | otherwise
                     = Cat nonnull (map nonmemoSsnf xs)
nonmemoWhiteSSNF (Rep x)    = nonmemoWhiteSSNF x
nonmemoWhiteSSNF (Opt x)    = nonmemoWhiteSSNF x
nonmemoWhiteSSNF x          = x -- Lam/Emp cannot occur anymore


