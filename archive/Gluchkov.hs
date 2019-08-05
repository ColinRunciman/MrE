module Gluchkov where
import Expression
import AutIntersect
import List

data GRE a = NULL | SYM a | CAT (GRE a)(GRE a) | ALT (GRE a)(GRE a) | REP (GRE a) 

linearise :: RE -> GRE (Int,Char)
linearise re = fst $ linny re [1..]

class Show a => Display a where
    display :: a -> String
    display x = show x

instance (Show a,Display b) => Display (a,b)
    where
    display (x,y) = display y ++ show x

instance Display Char
    where
    display c = [c]

instance Display a => Show (GRE a)
    where
    show NULL = "0"
    show (SYM x) = display x
    show (CAT x y) = "(" ++ show x ++ "." ++ show y ++ ")"
    show (ALT x y) = "(" ++ show x ++ "+" ++ show y ++ ")"
    show (REP x)   = show x ++ "*"
    

linny Emp xs = (NULL,xs)
linny Lam xs = (REP NULL,xs)
linny (Sym c) (n:ns) = (SYM(n,c),ns)
linny (Alt _ (x:xs)) ns = (ALT nx nxs,qs)
    where
    (nx,ms) = linny x ns
    (nxs,qs) = linny (mkAlt xs) ms
linny (Cat _ (x:xs)) ns = (CAT nx nxs,qs)
    where
    (nx,ms) = linny x ns
    (nxs,qs) = linny (mkCat xs) ms
linny (Rep x) ns = (REP nx,ms)
    where
    (nx,ms) = linny x ns
linny (Opt x) ns = (ALT (REP NULL) nx,ms)
    where
    (nx,ms) = linny x ns

first :: Ord a => GRE a -> [a]
first NULL = []
first (SYM x) = [x]
first (CAT x y) | nu x
                = first x `nubMerge` first y
                | otherwise
                = first x
first (ALT x y) = first x `nubMerge` first y
first (REP x)   = first x

nu :: GRE a -> Bool
nu (CAT x y) = nu x && nu y
nu (ALT x y) = nu x || nu y
nu (REP x)   = True
nu _         = False

lastc :: Ord a => GRE a -> [a]
lastc NULL = []
lastc (SYM x) = [x]
lastc (CAT x y) | nu y
                = lastc x `nubMerge` lastc y
                | otherwise
                = lastc y
lastc (ALT x y) = lastc x `nubMerge` lastc y
lastc (REP x)   = lastc x

followc :: Ord a => GRE a -> [(a,a)]
followc NULL = []
followc (SYM _) = []
followc (CAT x y) = followc x `nubMerge` followc y `nubMerge` [ (v,w) | v <- lastc x, w<- first y]
followc (ALT x y) = followc x `nubMerge` followc y
followc (REP x)   = followc x `nubMerge` [ (y,z) | y <- lastc x, z<- first x]

chars :: GRE a -> [a]
chars re = charsC re []
charsC NULL      = id
charsC (SYM x)   = (x:)
charsC (CAT x y) = charsC x . charsC y
charsC (ALT x y) = charsC x . charsC y
charsC (REP x)   = charsC x

createGluchkov :: Ord a => GRE a -> NFA (Maybe a) a
createGluchkov gr =
    NFA {
        states = Nothing : map Just cs,
        eps = [],
        final = fi,
        start = Nothing,
        trans = [(Just a,b,Just b) | (a,b)<-fo] ++ [(Nothing,c,Just c)|c<-fs]
    }
    where
    cs = chars gr
    fs = first gr
    ls = lastc gr
    fo = followc gr
    fi Nothing = nu gr
    fi (Just c) = elem c ls

gluchkov :: RE -> NFA Int Char
gluchkov re = NFA {
                  states = states nfa2,
                  eps=[],
                  start = 0,
                  trans = [ (x,y,z) | (x,(_,y),z) <- trans nfa2 ],
                  final = final nfa2
              }
    where nfa1=createGluchkov(linearise re)
          nfa2=nfaTrans transl nfa1
          transl Nothing      = 0
          transl (Just (x,y)) = x



    


