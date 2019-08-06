module Sanify where

-- very basic transformation, should be done to expressions before === if not katagraded
-- this will add insects if none existed

import Info
import Expression
import List

unGraded :: RE -> Bool
unGraded (Alt i _) = null $ gr i
unGraded (Cat i _) = null $ gr i
unGraded (Rep e)   = isRep e || isOpt e || isLam e || isEmp e || ungraded e
unGraded (Opt e)   = unGraded (Rep e)
ungraded _         = False

sanify :: RE -> RE
sanify  e | unGraded e = homTrans sanHom e
          |  otherwise = e

sanHom :: HomTrans 
sanHom = HomTrans { falt = sanAlt, fcat = sanCat, frep = sanRep, fopt = sanOpt }

sanOpt :: RE -> RE
sanOpt Emp     = Lam
sanOpt Lam     = Lam
sanOpt x       | ewp x
               = x
               | otherwise
               = Opt x

sanRep :: RE -> RE
sanRep Emp = Lam
sanRep Lam = Lam
sanRep x   = Rep x

sanCat xs = upgradeRE RepCxt NoGrade $ cat xs

-- sanAlt throws out duplicates, as a+a===a would be an issue
-- it really is only an issue for 'sub'
sanAlt xs | any ewp xs
          = sanOpt na
          | otherwise
          = na
            where
            na  = upgradeRE RepCxt NoGrade (mkAlt nxs)
            nxs = unions $ map altList xs
            altList Emp        = []
            altList Lam        = []
            altList (Alt _ xs) = xs
            altList (Opt x)    = altList x
            altList y          = [y]



