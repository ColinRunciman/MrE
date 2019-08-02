module Parser where
import Data.Char
import Info
import Expression

{- A nearly raw parser, recursive descent -}
{- Only semantic actions: absorb Lam and Emp, memoize ewp -}

readFullExp :: String -> RE
readFullExp cs =
   case readExp cs of
       [(e,"")] -> e
       [(e,s)]  -> error ("parsing junk at end: " ++ s)
       []       -> error "no parse"

readExp :: String -> [(RE,String)]
readExp ""       = []
readExp ('0':xs) = readRest Emp xs
readExp ('1':xs) = readRest Lam xs
readExp (' ':xs) = readExp xs
readExp ('(':xs) = [ p | (x,cs) <- readExp xs, cs' <- readChar ')' cs, p<-readRest x cs' ]
readExp (a:cs)   = [ p | isAlpha a, p<-readRest (Sym a) cs ]

readChar :: Char -> [Char] -> [[Char]]
readChar c (d:ds) | c==d      = [ds]
                  | d==' '    = readChar c ds
readChar _ _                  = []

readRest :: RE -> [Char] -> [(RE,String)]
readRest e (')':cs) = [(e,')':cs)]
readRest e (' ':cs) = readRest e cs
readRest e ('(':cs) = [ p | (e2,cs1)<-readExp cs, cs2 <- readChar ')' cs1,
                            (e3,cs3)<-readSequence e2 cs2, p<-readRest (synCat e e3) cs3 ]
readRest e ('+':cs) = [ (synAlt e e1,cs1)  | (e1,cs1)<-readExp cs]
readRest e ('*':cs) = readRest (synRep e) cs
readRest e ('?':cs) = readRest (synOpt e) cs
readRest e ('0':cs) = [ p | (e3,cs2)<-readSequence Emp cs, p<-readRest (synCat e e3) cs2]
readRest e ('1':cs) = [ p | (e3,cs2)<-readSequence Lam cs, p<-readRest (synCat e e3) cs2]
readRest e (c:cs1)  = [ p | isAlpha c, (e3,cs2)<-readSequence (Sym c) cs1, p<-readRest (synCat e e3) cs2]
readRest e ""       = [(e,"")]

readSequence :: RE -> [Char] -> [(RE,String)]
readSequence e ""       = [(e,"")]
readSequence e (')':cs) = [(e,')':cs)]
readSequence e ('+':cs) = [(e,'+':cs)]
readSequence e ('*':cs) = readSequence (synRep e) cs
readSequence e ('?':cs) = readSequence (synOpt e) cs
readSequence e ('0':cs) = [ (synCat e e3,cs2) | (e3,cs2)<-readSequence Emp cs]
readSequence e ('1':cs) = [ (synCat e e3,cs2) | (e3,cs2)<-readSequence Lam cs]
readSequence e (' ':cs) = readSequence e cs
readSequence e ('(':cs) = [ (synCat e e3,cs3) | (e2,cs1)<-readExp cs, cs2 <- readChar ')' cs1,
                            (e3,cs3)<-readSequence e2 cs2]
readSequence e (c:cs1)  = [ (synCat e e3,cs2) | isAlpha c, (e3,cs2)<-readSequence (Sym c) cs1]

synRep Emp = Lam
synRep Lam = Lam
synRep x   = Rep x

synOpt Emp = Lam
synOpt Lam = Lam
synOpt x   = Opt x

synAlt Emp x = x
synAlt x Emp = x
synAlt Lam x = synOpt x
synAlt x Lam = synOpt x
synAlt x y   = Alt (newInfo (ewp x||ewp y)) [x,y]

synCat Emp x = Emp
synCat x Emp = Emp
synCat Lam x = x
synCat x Lam = x
synCat x y   = Cat (newInfo (ewp x&&ewp y)) [x,y]

-- computes the attributes of a parsed RE
-- flattens Alts/Cats/Reps/Opts
-- assumes an RE with ewp attribute
-- assumes Lam/Emp have been absorbed
attribute :: RE -> RE
attribute = foldHomInfo attributeHom

attributeHom :: HomInfo RE
attributeHom = HomInfo { hiemp=Emp, hilam=Lam, hisym=Sym, hialt=attrAlt, hicat=attrCat, hiopt=attrOpt, hirep=attrRep }

-- only ew information is assumed to be present
-- because concatAlt removes Lam/Opt, we may have to recover them
attrAlt :: Info -> [RE] -> RE
attrAlt i xs =  opti (ew i) $ mkAlt (concatAlt xs)
                where
                opti True  x |  not (ewp x)
                             =  Opt x
                opti _     x =  x

-- no Emp in list
attrCat :: Info -> [RE] -> RE
attrCat i xs = mkCat $  concatCat xs

-- Lam/Emp should not occur here
attrOpt x |  ewp x
          =  x
          |  otherwise
          =  Opt x

attrRep (Rep x) = Rep x
attrRep (Opt x) = Rep x
attrRep x       = Rep x

readAttributedRE :: String -> RE
readAttributedRE = attribute . readFullExp 



