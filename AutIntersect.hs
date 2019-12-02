module AutIntersect where
import Expression
import List
import Data.List
import Data.Maybe
import Context
import Function
import Fuse
import Comparison
import PreOrderTrees -- for state minimisation
import Alphabet
import OK
import Queue

import qualified Data.Map.Strict as M
import qualified Data.Set as S


data NFA a b = NFA {
    states :: [a],
    start :: a, final :: a->Bool, eps :: [(a,a)],
    trans :: [(a,b,a)] }

-- extract an RE a la Hopcroft/Ullman
hu_extract :: Ord a => NFA a Char -> RE
hu_extract nfa = alt [ rhu n (start nfa) s | s<-states nfa, final nfa s ]
    where
    n = length $ states nfa
    rhu 0 s1 s2 = alt $ [ Sym c | (x,c,y)<-trans nfa, x==s1, y==s2] ++ [ Lam | elem (s1,s2) (eps nfa) || s1==s2 ]
    rhu m s1 s2 = alt (rhu (m-1) s1 s2:[cat[rhu (m-1)s1 s3,rep(rhu (m-1) s3 s3),rhu(m-1)s3 s2]|s3<-states nfa])

finalStates :: NFA a b -> [a]
finalStates nfa = filter (final nfa)(states nfa)

instance (Show a,Show b) => Show (NFA a b) where
    show aut =
         "NFA { start=" ++ show (start aut) ++ ", final=" ++
         show (finalStates aut) ++ "; " ++
         concatMap showEps (eps aut) ++ concatMap showTrans (trans aut) ++ " }"
         where
         showEps (x,y) = show x ++ "-->" ++ show y ++ ";"
         showTrans (x,c,y) = show x ++ "==" ++ show c ++ "==>" ++ show y ++ ";"

graphViz :: (Show a,Show b) => NFA a b -> String
graphViz nfa = "digraph finite_state_machine { \n\trankdir=LR;\n" ++ sta++ finals ++ staarr ++ epsilons ++ chartrans ++ "}"
    where
    --sta      = "node [shape = " ++ stashape ++ "]; " ++ show(show (start nfa)) ++ "\n"
    --stashape = if final nfa (start nfa) then "invtriangle" else "triangle"
    sta      = "secret_node [style=invis];\n"
    staarr   = "secret_node -> " ++ (show(show(start nfa))) ++ ";\n"
    finals   = "node [shape = doubleoctagon]; " ++ unwords (map (show.show) (finalStates nfa)) ++
               "\nnode [shape = ellipse];\n"
    epsilons = unlines (map showpair (eps nfa))
    chartrans = unlines (map showtriple (trans nfa))
    showpair (x,y) = show(show x)++" -> " ++ show(show y) ++ " [label = \"&epsilon;\"];"
    showtriple (x,y,z) = show(show x) ++ " -> " ++ show(show(z)) ++ " [ label = " ++ show(show y) ++ "];"

convertNice :: RE -> NFA RE Char
convertNice re = removeEpsTrans $ convert re
-- Bernstein-style, state-based RE-translation
convert :: RE -> NFA RE Char
convert re = NFA {
    states = theStates, start = re, final = ewp,
    eps = [ (x,y) | x <- theStates, y <- epstran x ],
    trans = [ (x,c,y) | x <- theStates, (c,y) <- chartran x ] }
    where
    theStates = allStates re

epstran :: RE -> [RE]
epstran (Alt _ xs)     = xs
epstran (Cat _ (x:xs)) = [ kataCat (x':xs) | x' <- epstran x ] ++ [ mkCat xs | ewp x]
epstran (Rep x)        = [ kataCat[x,Rep x] ] -- was [x,.., the x not needed
epstran (Opt x)        = [x]
epstran _              = []

chartran :: RE -> [(Char,RE)]
chartran (Sym c)            = [(c,Lam)]
chartran (Cat _ (Sym c:xs)) = [(c,mkCat xs)]
chartran _                  = []

tran :: RE -> [RE]
tran x = epstran x ++ map snd (chartran x)

allStates re = allOtherStates [re] [re]
allOtherStates (y:ys) xs = allOtherStates (zs ++ ys) (nubMerge xs zs)
    where zs = nubSort [ z | z<- tran y, not (elem z xs) ]
allOtherStates [] xs = xs
-- end of Bernstein-style translation --

-- the product nfa with the intersection of two languages
productNFA :: (Ord a,Ord b,Eq c) => NFA a c -> NFA b c -> NFA (a,b) c
productNFA x y = removeUnreachable $ NFA {
    states = [(sx,sy)| sx<- states x, sy<- states y],
    start = (start x,start y),
    final = \(sx,sy)-> final x sx && final y sy,
    eps = [((sx,sy),(sx',sy)) | (sx,sx')<- eps x, sy <- states y] ++
          [((sx,sy),(sx,sy')) | (sy,sy')<- eps y, sx <- states x],
    trans = [((sx1,sy1),c,(sx2,sy2)) | (sx1,c,sx2)<- trans x,
             (sy1,d,sy2)<- trans y, c==d]}

-- prune an NFA by removing states that are not reachable/coreachable
removeUnreachable :: Ord a => NFA a c -> NFA a c
removeUnreachable aut = NFA { states = prodstates,
                              start = start aut, final = final aut,
                              eps = [ (x,y)| (x,y)<-eps aut, elem x bireachable, elem y bireachable],
                              trans = [ (x,c,y)|(x,c,y)<-trans aut, elem x bireachable, elem y bireachable] }
    where
    prodstates = if null bireachable then [start aut] else bireachable
    bireachable = intersect reachable coreachable
    coreachable = coreach fs fs where fs = finalStates aut
    coreach [] xs = xs
    coreach (y:ys) xs = coreach (newstates ++ ys) (nubMerge xs newstates)
        where
        newstates = [ z | (z,y')<-eps aut, y'==y, not(elem z xs)] `nubMerge`
                    [ z | (z,_,y')<- trans aut, y'==y, not(elem z xs)]
    reachable = reach [start aut] [start aut]
    reach [] xs     = xs
    reach (y:ys) xs = reach (newstates ++ ys) (nubMerge xs newstates)
        where
        newstates = [ z | (y',z)<-eps aut, y'==y, not(elem z xs)] `nubMerge`
                    [ z | (y',_,z)<- trans aut, y'==y, not(elem z xs)]

-- NFA with a single final state; no incoming trans into initial state, no outgoing trans from final state
data Add2 a = Start | End | NormalS a deriving (Eq,Ord)
instance Show a => Show (Add2 a)
    where
    show Start = "S"
    show End = "E"
    show (NormalS x) = show x

isEnd :: Add2 a -> Bool
isEnd End = True
isEnd _   = False

emptyNFA :: NFA (Add2 RE) Char
emptyNFA = NFA { states = [Start,End], start=Start, final = isEnd, eps=[], trans=[] }

-- translating epsilon-rules along a function, removing reflexive steps
epsTrans :: Eq b => (a->b) -> [(a,a)] -> [(b,b)]
epsTrans f xs = [ (fx,fy) | (x,y)<-xs, let fx= f x, let fy=f y, fx/=fy ]

charTrans :: (a->b) -> [(a,c,a)] -> [(b,c,b)]
charTrans f xs = [(f x,c,f y)|(x,c,y)<-xs]

-- translate nfa along a function
nfaTrans :: (Ord b,Ord x) => (a->b) -> NFA a x -> NFA b x
nfaTrans f nfa = NFA { states = nubSort(map f(states nfa)), start = f(start nfa),
                       final = \s->any(\y->f y==s && final nfa y)(states nfa),
                       eps=nubSort $ epsTrans f (eps nfa),
                       trans=nubSort $ charTrans f (trans nfa) }

convertEdgeRE :: RE -> NFA (Add2 RE) Char
convertEdgeRE Emp     = emptyNFA
convertEdgeRE Lam     = emptyNFA { eps=[(Start,End)] }
convertEdgeRE (Sym d) = emptyNFA { trans=[(Start,d,End)]}
convertEdgeRE (Alt _ xs) = emptyNFA { states = unions(map states nfas),
                                      eps    = unions(map eps nfas),
                                      trans  = unions(map trans nfas) }
                           where
                           nfas = map convertEdgeRE xs
convertEdgeRE (Cat _ (x:xs)) =
    emptyNFA {
          states = nubSort(map f1trans (states nfa1) ++ map f2trans (states nfa2)),
          eps    = nubSort(epsTrans f1trans (eps nfa1) ++ epsTrans f2trans (eps nfa2)),
          trans  = nubSort(charTrans f1trans (trans nfa1) ++ charTrans f2trans (trans nfa2)) }
                               where nfa1 = convertEdgeRE x
                                     nfa2 = convertEdgeRE midp
                                     midp = mkCat xs
                                     f1trans End = NormalS midp
                                     f1trans Start = Start
                                     f1trans (NormalS y) = NormalS (fuseCat(y:xs))
                                     f2trans Start = NormalS midp
                                     f2trans y     = y
convertEdgeRE (Rep x) = 
    emptyNFA {
          states = Start : End : map btrans (states bnfa),
          eps    = [(Start,End),(Start,xplus),(xstar,End),(xstar,xplus)] ++
                   epsTrans btrans (eps bnfa),
          trans  = charTrans btrans (trans bnfa) }
                            where
                            bnfa = convertEdgeRE x
                            xplus        = NormalS (fuseCat [x,Rep x])
                            xstar        = NormalS (Rep x)
                            btrans Start = xplus
                            btrans End   = xstar
                            btrans (NormalS y) = NormalS (fuseCat [y,Rep x])
convertEdgeRE (Opt x) =
     bnfa { eps = (Start,End) : eps bnfa }
     where
     bnfa = convertEdgeRE x

-- remove epsilon-transitions from an NFA, including restriction to reachable states
removeEpsTrans :: (Ord a,Ord b) => NFA a b -> NFA a b
removeEpsTrans nfa = removeUnreachable $ NFA {
     states   =  map snd copairs,
     start    =  head [ s | Just set <- [lookup (start nfa) pairs], Just s<-[lookup set copairs] ],
     final    =  \s-> or [ any (final nfa) set | Just set <- [lookup s pairs]],
     eps      =  [],
     trans    =  [ (s,b,t) | (set,s)<-copairs, (x,b,y)<- trans nfa, elem x set, 
                             Just set' <- [lookup y pairs], Just t <- [lookup set' copairs]]}
     where
     pairs = [(x,epsClosure nfa x) | x <- states nfa]
     copairs = nubSort [(set,x') | (x,set) <- pairs,
                                   let x'=minimum (x:[ y|y<-set, y/=x, lookup y pairs==Just set])]


epsClosure :: Ord a => NFA a b -> a -> [a]
epsClosure nfa x = epsReach [x] [x]
    where
    epsReach [] xs = xs
    epsReach (y:ys) xs = epsReach (newstates++ys)(nubMerge newstates xs)
        where
        newstates = nubSort [ z | (y',z)<- eps nfa, y'==y, not (elem z xs) ]

-- translate an NFA into a hybrid NFA, with REs as transition labels
reAuto :: NFA a Char -> NFA (Add2 a) RE
reAuto x = NFA {
    states = [Start, End] ++ map NormalS (states x),
    start = Start,
    final = isEnd,
    eps=[],
    trans = [(Start,Lam,NormalS(start x))] ++
            [(NormalS y,Lam,End)|y<-states x, final x y] ++
            [(NormalS a,Lam,NormalS b)| (a,b)<-eps x] ++
            [(NormalS a,Sym c,NormalS b) | (a,c,b)<- trans x] }

-- simpler version when the NFA is already well-pointed
reAuto2 :: NFA (Add2 a) Char -> NFA (Add2 a) RE
reAuto2 nfa = nfa { eps=[],
                    trans=[(a,Lam,b)| (a,b)<- eps nfa] ++
                          [(a,Sym d,b) | (a,d,b) <- trans nfa] }



elimParallel :: Ord a => NFA (Add2 a) RE -> OK(NFA (Add2 a) RE)
elimParallel x =  okmap (\ntrans-> x { trans = ntrans }) (parMerge (trans x))
{-
     where ntrans = parMerge (trans x)
     [ x { trans = newTrans} | 
       ([(a,r,b),(c,s,d)],others) <- subsetRest 2 (trans x),
       --((a,r,b),others)  <- itemRest (trans x),
       -- ((c,s,d),others') <- itemRest others,
       a==c, b==d, let newTrans = (a,fuseAlt[r,s],b):others]
-}

parMerge :: Ord a => [(a,RE,a)] -> OK [(a,RE,a)]
parMerge xs = pm (sortBy (\(x,y,z)(a,b,c)->compare x a &&& compare z c) xs) unchanged where
    pm []  cont = cont []
    pm [x] cont = cont [x]
    pm ((x1,e1,y1):(x2,e2,y2):xs) cont
           |  x1==x2 && y1==y2
           =  pm ((x1,fuseAlt[e1,e2],y1):xs) changed
           |  otherwise
           =  okmap ((x1,e1,y1):) (pm ((x2,e2,y2):xs) cont)

fix :: (a -> [a]) -> a -> a
fix f x = let nx = f x in if null nx then x else fix f (head nx)

elimLoop :: Ord a => NFA (Add2 a) RE -> [NFA (Add2 a) RE]
elimLoop aut =
     [ aut { trans = newTrans} |
       ((a,r,b),others)<- itemRest (trans aut), a==b,
       let (as,bs) = partition (\(v,w,z)->v==a) others,
       let r'=fuseRep r,
       let newTrans=[(x,fuseCat[r',e],y)|(x,e,y)<-as]++bs ]

elimState :: Ord a => NFA (Add2 a) RE -> OK (NFA (Add2 a) RE)-- [NFA (Add2 a) RE]
elimState aut |  null ss
              =  unchanged aut
              |  otherwise
              =  changed $ aut { states=[Start,End] ++ tail ss,
                                 trans = elimState' (head ss)(trans aut) }
                 where
                 ss = sortOn (elimCount aut) [ NormalS x | NormalS x <- states aut ]

elimCount :: Ord a => NFA a b -> a -> Int
elimCount nfa a = indegree a nfa * outdegree a nfa

indegree :: Eq a => a -> NFA a b -> Int
indegree x nfa = length (filter ((==x) . snd) (eps nfa)) +
                 length [ () | (a,b,c)<- trans nfa, c==x]
outdegree :: Eq a => a -> NFA a b -> Int
outdegree x nfa = length (filter ((==x) . fst) (eps nfa)) +
                  length [ () | (a,b,c)<- trans nfa, a==x]
{-
    [ aut { states = newStates, trans = newTrans } |
      (NormalS x,newStates) <- itemRest (states aut),
      let (as,bs) = partition (\(v,w,z)->v==NormalS x) (trans aut),
      let (cs,ds) = partition (\(v,w,z)->z==NormalS x) bs,
      let newTrans = ds ++ [ (a,fuseCat[c,d],b) | (a,c,_)<- cs, (_,d,b)<-as]]
-}

elimState' :: Ord a => a -> [(a,RE,a)] -> [(a,RE,a)]
elimState' x xs = os ++ [(v,fuseCat[e1,loop,e2],w) | (v,e1,_)<-ds, (_,e2,w)<- cs]
    where
    (as,bs) = partition (\(v,w,z)->v==x) xs
    (ls,cs) = partition (\(v,w,z)->z==x) as
    (ds,os) = partition (\(v,w,z)->z==x) bs
    loop    = fuseRep(fuseAlt[ e | (_,e,_)<- ls])

-- eliminate states only connected by eps-transitions
elimEpsStates :: Ord a => NFA a b -> NFA a b
elimEpsStates = valOf . fixOK ees 
          where
          ees aut |  null ss
                  =  unchanged aut
                  |  final aut loser -- we remove a final state
                  =  changed newaut{final=nfinal}
                  |  otherwise
                  =  changed newaut
                     where
                     ss      = [ s | s<-states aut, s/=start aut,
                                     all (\(s1,_,s2)->s/=s1 && s/=s2) (trans aut) ]
                     loser   = head ss
                     (as,bs) = partition (\(v,w)->v==loser) (eps aut)
                     (cs,ds) = partition (\(v,w)->w==loser) bs
                     neweps  = ds ++ [(v,w)| (v,_)<-cs, (_,w)<-as, v/=w]
                     newaut  = aut{ states= states aut \\ [loser], eps=neweps}
                     nfinal  = \s -> final aut s || elem s (map fst cs)


extractRE2 :: Ord a => NFA (Add2 a) RE -> RE
extractRE2 aut |  hasChanged aut1
               =  extractRE2 (valOf aut1)
               -- |  not(null aut2)
               -- =  extractRE2 (head aut2)
               -- |  not(null aut3)
               |  hasChanged aut3
               =  extractRE2 (valOf aut3)
               |  otherwise
               =  head ([ e | (Start,e,End) <- trans aut] ++ [Emp])
               where
               aut1 = elimParallel aut
               --aut2 = elimLoop aut
               aut3 = elimState aut

data InEquation a = From a RE | Between a RE a deriving Eq

instance Show a => Show (InEquation a) where
    show (From x e) = show x ++ " <= " ++ show e
    show (Between x e y) = show x ++ " <= " ++ show e ++ show y

instance Ord a => Ord (InEquation a) where
    compare (From x y) (From v w) = compare x v &&& compare y w
    compare (From x y) (Between v w z) = compare x v &&& LT
    compare (Between v w z) (From x y) = compare v x &&& GT
    compare (Between a b c)(Between d e f) = compare a d &&& compare c f &&& compare b e

extractRE1 :: Ord a => NFA a Char -> RE
extractRE1 nfa = solveInequations (extractInequations nfa) (start nfa)

extractInequations :: Ord a => NFA a Char -> [InEquation a]
extractInequations x = sort $
            [From a Lam | a<- states x, final x a] ++
            [Between a Lam b| (a,b)<- eps x] ++
            [Between a (Sym d) b | (a,d,b) <- trans x]

solveInequations :: Ord a => [InEquation a] -> a -> RE
solveInequations xs x = oneSolve ys
    where
    vars = extractVars xs \\ [x]
    ys   = eliminateVarsEquation (elimParallelEquations xs) vars
    oneSolve [From _ e] = e
    oneSolve [From _ e, Between _ f _ ] = fuseCat [fuseRep f, e]
    oneSolve []         = Emp
    oneSolve _          = error "this should not arise"

extractVarsI :: Ord a => InEquation a -> [a]
extractVarsI (From x _) = [x]
extractVarsI (Between x _ y) = nubSort [x,y]

extractVars :: Ord a => [InEquation a] -> [a]
extractVars xs = unions $ map extractVarsI xs

elimParallelEquations :: Ord a => [InEquation a] -> [InEquation a]
elimParallelEquations [] = []
elimParallelEquations (From x e:From y f:xs) | x==y
                                             = elimParallelEquations (From x (fuseAlt [e,f]):xs)
elimParallelEquations (From x e:xs) = From x e : elimParallelEquations xs
elimParallelEquations (Between x e y:Between v f w:xs) | x==v && y==w
                                                       = elimParallelEquations (Between x (fuseAlt [e,f]) y:xs)
elimParallelEquations (Between x e y:xs) = Between x e y : elimParallelEquations xs

eliminateVarsEquation :: Ord a => [InEquation a] -> [a] -> [InEquation a]
eliminateVarsEquation xs [] =  xs
eliminateVarsEquation xs (v:vs) = eliminateVarsEquation (elimStateEquation xs v) vs

elimStateEquation :: Ord a => [InEquation a] -> a -> [InEquation a]
elimStateEquation xs x = elimParallelEquations $ nubSort $
    others ++
    [ From y (fuseCat[e,mid,theRE]) | not(isEmp theRE), (y,e) <- tox ] ++
    [ Between y (fuseCat[e,mid,f]) z | (y,e)<-tox, (f,z)<-fromx ]
    where
    (others,theRE,looped,fromx,tox) = splitByVar xs x
    mid = fuseRep looped -- would be Lam if no loops

splitByVar :: Ord a => [InEquation a] -> a -> ([InEquation a],RE,RE,[(RE,a)],[(a,RE)])
splitByVar xs x = spv xs [] Emp Emp [] []
    where
    spv [] a b c d e = (a,b,c,d,e)
    spv (eq@(From y f):xs) a b c d e
        | y==x
        = spv xs a (fuseAlt [f,b]) c d e
        | otherwise
        = spv xs (eq:a) b c d e
    spv (eq@(Between v f w):xs) a b c d e
        | v/=x && w/=x
        = spv xs (eq:a) b c d e
        | v==x && w==x
        = spv xs a b (fuseAlt [c,f]) d e
        | v==x -- && w/=x
        = spv xs a b c ((f,w):d) e
        | otherwise -- v/=x && w==x
        = spv xs a b c d ((v,f):e)
                              

                               


extractRE :: Ord a => NFA a Char -> RE
extractRE = extractRE2 . reAuto

intersectRE :: RE -> RE -> RE
intersectRE x y = extractRE $ (convert x `productNFA` convert y)

intersectRE2 x y = extractRE $ convertEdgeRE x `productNFA` convertEdgeRE y

-- identifies semantic duplicates within the list and replaces them by a the
-- smallest alternative from the list
minFunc :: [RE] -> RE -> RE
minFunc res = quotientMap pickMinList (groupOrder compRE res)

stateMin0 :: NFA (Add2 RE) Char -> NFA (Add2 RE) Char
stateMin0 = stateMin1 . autMirror . stateMin1 . autMirror

stateMin1 :: NFA (Add2 RE) Char -> NFA (Add2 RE) Char
stateMin1 nfa =
    nfa { states = [ Start, End ] ++ map (NormalS . pickMinList) gord,
          eps = epsTrans func (eps nfa),
          trans = nubSort $ charTrans func (trans nfa) }
    where
    gord            =  groupOrder compRE [ r | NormalS r <- states nfa]
    mf              =  quotientMap pickMinList gord
    func Start      =  Start
    func End        =  End
    func (NormalS x) =  NormalS (mf x)

{-
simpleStateMin :: (Ord a, Eq b) => NFA a b -> Maybe (NFA a b)
simpleStateMin nfa = [ nfaTrans (quotientfun x y) nfa | [x,y] <- chooseN 2 (states nfa), simpleStateEquivalence nfa x y ]
-}
quotientfun :: Eq a => a -> a -> a -> a
quotientfun x y z = if x==z then y else z

simpleStateEquivalence :: (Ord a, Ord b) => NFA a b -> a -> a -> Bool
simpleStateEquivalence nfa s1 s2 =
    final nfa s1==final nfa s2 && -- they have to be either both final or both non-final, and...
    eps1==eps2 && -- they eps-transition to the same states
    tr1==tr2
    where
    eps1 = sort [ s | (t,s)<-eps nfa, t==s1 ]
    eps2 = sort [ s | (t,s)<-eps nfa, t==s2 ]
    tr1  = sort [ (c,s) | (t,c,s)<-trans nfa, t==s1]
    tr2  = sort [ (c,s) | (t,c,s)<-trans nfa, t==s2]

epsfunPar :: Ord a => Bool -> NFA a b -> a -> [a]
epsfunPar True  nfa x = sort [ s | (t,s)<-eps nfa, t==x ]
epsfunPar False nfa x = sort [ t | (t,s)<-eps nfa, s==x ]

charfunPar :: (Ord a,Ord b) => Bool -> NFA a b -> a -> [(b,a)]
charfunPar  True nfa x = sort [ (c,s) | (t,c,s)<-trans nfa, t==x]
charfunPar False nfa x = sort [ (c,t) | (t,c,s)<-trans nfa, s==x]

-- an inductive state minimisation:: if states
simpleStateMin2 :: (Ord a, Ord b) => NFA a b -> Maybe (a->a)
simpleStateMin2 = simpleStateMinPar True

simpleStateMinPar:: (Ord a, Ord b) => Bool -> NFA a b -> Maybe (a->a)
simpleStateMinPar direction nfa
    | any plural is2 
    = Just (eqclassfun ss)
    | otherwise
    = Nothing
    where
    is  = sort [ ((final nfa s,epsfunPar direction nfa s,charfunPar direction nfa s),s) | s <- states nfa ]
    is2 = groupBy (\x y->fst x==fst y) is
    ss  = map (map snd) is2

-- dual to simpleStateMin2, are two states reached in the same way
simpleStateMin3 :: (Ord a, Ord b) => NFA a b -> Maybe (a->a)
simpleStateMin3 = simpleStateMinPar False

fullSimple :: (Ord a, Ord b) => NFA a b -> NFA a b
fullSimple nfa =
   case (simpleStateMin2 nfa,simpleStateMin3 nfa) of
       (Nothing,Nothing) -> nfa
       (Nothing, Just f) -> fullSimple (nfaTrans f nfa)
       (Just f, Nothing) -> fullSimple (nfaTrans f nfa)
       (Just f,  Just g) -> fullSimple (nfaTrans (f.g) nfa)

-- quotient map of a set of equivalence classes
eqclassfun :: Eq a => [[a]] -> a -> a
eqclassfun [] x       = x -- should not happen
eqclassfun (xs:xss) y | elem y xs
                      = head xs
                      | otherwise
                      = eqclassfun xss y

-- quotientmap of sorts, the func parameter is useful when type a carries semantic content, like REs
-- idea is when we form the backward quotient in an nfa to identify co-indistinguishable states
-- that the resulting value is a meaningful RE if e.g. fuseAlt is used to combine the states
eqclassfunPar :: Eq a => ([a]->a) -> [[a]] -> a -> a
eqclassfunPar func xss = efp ys xss
      where
      ys = map func xss
      efp [] [] x = x -- should not happen
      efp (v:vs) (zs:zss) x | elem x zs
                            = v
                            | otherwise
                            = efp vs zss x
    
-- autMirror is incorrect, in the sense that the REs (as states) no longer describe their language

autMirror :: NFA (Add2 RE) b -> NFA (Add2 RE) b
autMirror aut    = aut { states = [Start,End] ++ [NormalS (mirror x)|NormalS x<- states aut],
                         eps = epsTrans func (eps aut),
                         trans = charTrans func (trans aut) }
                   where
                   func Start = End
                   func End   = Start
                   func (NormalS x) = NormalS (mirror x)  

stateMin2 :: NFA RE Char -> NFA RE Char
stateMin2 nfa =
       nfa { start  = mf (start nfa),
             states = map pickMinList gord,
             eps    = epsTrans mf (eps nfa),
             trans  = nubSort $ charTrans mf (trans nfa) }
       where
       gord            =  groupOrder compRE (states nfa)
       mf              =  quotientMap pickMinList gord

debruijnify :: (Ord a,Ord b) => NFA a b -> NFA Int b
debruijnify nfa = nfaTrans numberOf nfa
                  where
                  asl = zip (states nfa) [0..]
                  numberOf x = fromJust $ lookup x asl


stateMin3 :: NFA RE Char -> NFA RE Char
stateMin3 nfa =
       nfa { start  = mf (start nfa),
             states = map pickMinList gord,
             eps    = epsTrans mf (eps nfa),
             trans  = nubSort $ charTrans mf (trans nfa) }
       where
       gord            =  groupOrder compRE (states nfa)
       mf              =  quotientMap pickMinList gord


nfaUnfoldingPar :: HomTrans -> RE -> [ (Char,RE) ]
nfaUnfoldingPar _ Emp             = []
nfaUnfoldingPar _ Lam             = []
nfaUnfoldingPar _ (Sym c)         = [(c,Lam)]
nfaUnfoldingPar ht (Alt i xs)     = unions $ map (nfaUnfoldingPar ht) xs
nfaUnfoldingPar ht (Cat i (x:xs)) | ewp x
                                  = first `nubMerge` second
                                  | otherwise
                                  = first
                                    where
                                    first  = [ (c,fcat ht(nx:xs)) | (c,nx)<- nfaUnfoldingPar ht x ]
                                    second = nfaUnfoldingPar ht (fcat ht xs)
nfaUnfoldingPar ht (Rep x)        = [ (c,fcat ht [nx,Rep x]) | (c,nx)<-nfaUnfoldingPar ht x ]
nfaUnfoldingPar ht (Opt x)        = nfaUnfoldingPar ht x

-- legacy
nfaUnfolding = nfaUnfoldingPar fuseH
convertUnfolding = convertUnfoldingPar fuseH

convertUnfoldingPar :: HomTrans -> RE -> NFA RE Char
convertUnfoldingPar ht re =
    NFA { start = re, final = ewp, eps=[], states = ss,
          trans = ts }
    where
    (ss,ts)=computeTrans [re] [] []
    -- computeTrans todo doneStates doneTransitions
    computeTrans [] ss ts = (sort ss,sort ts)
    computeTrans (x:xs) ss ts | elem x ss
                              = computeTrans xs ss ts
                              | otherwise
                              = computeTrans (nubMerge xs bs) (x:ss) (cs++ts)
                                where
                                as = nfaUnfolding x
                                bs = nubSort $ map snd as
                                cs = [ (x,c,y) | (c,y) <- as ]

cuSize :: RE -> Int
cuSize x = length (states (convertUnfolding x))

cuSizeGen :: Katahom -> RE -> Int
cuSizeGen kh x = length (states (compactUnfolding kh x))

compactUnfolding :: Katahom -> RE -> NFA RE Char
compactUnfolding kh re =
   nfa1 -- here without bisim quotient
   where
   transform = mkTransform kh
   nre       = transform re -- new regexp, transformed with the katahom
   nfa1      = convertUnfoldingPar ht nre
   ht        = mkHomTrans kh
--   cs        = enumerate $ alpha nre
--   de        = derivationGroupGeneric ht cs

-- should perhaps be debruinified, as the backward quotient does not preserve languages
-- it doesnot even give use the union of languages, something more complex
-- really a bisimulation equivalence thing
semanticStateMin :: Ord a => NFA a Char -> NFA a Char
semanticStateMin nfa = ssm nfa (stateMinGenericPar True nfa)(stateMinGenericPar False nfa)
    where
    ssm x Nothing Nothing  = x
    ssm x (Just y) _       = ssm y Nothing (stateMinGenericPar False y)
    ssm x Nothing (Just y) = ssm y (stateMinGenericPar True y) Nothing

langQuotient :: Ord a => NFA a Char -> NFA a Char
langQuotient nfa = fromMaybe nfa (stateMinGenericPar True nfa)

-- for epsilon-free nfa
stateMinGeneric :: Ord a => ([a]->a) -> NFA a Char -> Maybe (NFA a Char)
stateMinGeneric comb nfa | not (null $ eps nfa)
                         = error "this state quotient is only defined for epsilon-free nfa"
                         | any plural xss
                         = Just (nfaTrans (eqclassfunPar comb xss) nfa)
                         | otherwise
                         = Nothing
                           where
                           (as,bs)    = partition (final nfa) (states nfa)
                           xss        = refinePar True nfa [sort as,sort bs]

refinePar :: Ord a => Bool -> NFA a Char -> [[a]] -> [[a]]
refinePar direction nfa xss = rf xss [] xss
                 where
                 rf tss yss [] = yss
                 rf _ _ ([]:_) = error "empty equivalence class"
                 rf tss yss ([x]:zss) = rf tss ([x]:yss) zss -- not needed, just a short-cut
                 rf tss yss (zs:zss)  = case statePartitionPar direction nfa tss zs of
                                            [_] -> rf tss (zs:yss) zss
                                            pss -> refinePar direction nfa (zss ++ yss ++ pss)

statePartitionPar :: Ord a => Bool -> NFA a Char -> [[a]] -> [a]-> [[a]]
statePartitionPar direction nfa tss (x:xs) | null nos
                                           = [x:xs]
                                           | otherwise
                                           = (x:yes):statePartitionPar direction nfa tss nos
                                             where (yes,nos) = partition (compatiblePar direction nfa tss x) xs


stateMinGenericOp :: Ord a => ([a]->a) -> NFA a Char -> Maybe (NFA a Char)
stateMinGenericOp comb nfa | not (null $ eps nfa)
                           = error "this state quotient is only defined for epsilon-free nfa"
                           | any plural xss
                           = Just (nfaTrans (eqclassfunPar comb xss) nfa)
                           | otherwise
                           = Nothing
                             where
                             st         = [start nfa]                    
                             bs         = states nfa \\ st
                             xss        = refinePar False nfa [st,sort bs]
                        

compatiblePar :: Ord a => Bool -> NFA a Char -> [[a]] -> a -> a -> Bool
compatiblePar direction nfa xss x y = xs==ys
    where
    xs = nubSort [ (c,head ts) | (c,t) <- charfunPar direction nfa x, ts <- xss, elem t ts ]
    ys = nubSort [ (c,head ts) | (c,t) <- charfunPar direction nfa y, ts <- xss, elem t ts ]


type Eqelem a    = (a,[(Char,a)])
type Eqclass a   = [ Eqelem a ]
type Eqclasses a = [ Eqclass a ]

-- the Bool output indicates whether we have a non-trivial map
refine :: Ord a => Eqclasses a -> (Bool,M.Map a a)
refine eqss = rf (converter eqss) [] eqss
             where
             rf fm eqs []          = (any plural eqs,fm)
             rf fm yss ([]:zss)    = rf fm yss zss -- can happen intially, e.g. all states are final
             rf fm yss ([x]:zss)   = rf fm ([x]:yss) zss -- not needed, just a short-cut
             rf fm yss (zs:zss)    = case statePartition fm zs of
                                            [_] -> rf fm (zs:yss) zss
                                            pss -> rf (M.union (converter pss) fm) [] (zss ++ yss ++ pss)

converter :: Ord a => Eqclasses a -> M.Map a a
converter eqss = quotMap head $ map (map fst) eqss

statePartition :: Ord a => M.Map a a -> Eqclass a -> Eqclasses a
statePartition fm (x:xs) | null nos
                         = [x:xs]
                         | otherwise
                         = (x:yes):statePartition fm nos
                           where (yes,nos) = partition (compatible fm x) xs
statePartition fm []     = []  -- should not happen, error

compatible :: Ord a => M.Map a a -> Eqelem a -> Eqelem a -> Bool
compatible fm (_,xs) (_,ys) = compatibleList fm xs ys

compatibleList _ [] [] = True
compatibleList _ [] _  = False
compatibleList _ _  [] = False
compatibleList fm ((c,x):xs) ys =
    classEquivalent fm (x:is) is2 && compatibleList fm cs cs2
    where
    (is,cs)   = splitChar c xs
    (is2,cs2) = splitChar c ys

splitChar :: Char -> [(Char,a)] -> ([a],[(Char,a)])
splitChar c xs = spc xs [] []
                 where
                 spc [] is cs = (is,cs)
                 spc ((d,x):ys) is cs | c==d
                                      = spc ys (x:is) cs
                                      | otherwise
                                      = spc ys is ((d,x):cs)

classEquivalent :: Ord a => M.Map a a -> [a] -> [a] -> Bool
classEquivalent fm xs ys = nubSort [ fm M.! x | x<- xs] == nubSort [fm M.! y | y<-ys]

-- for epsilon-free nfa
stateMinGenericPar :: Ord a => Bool -> NFA a Char -> Maybe (NFA a Char)
stateMinGenericPar direction nfa
                            | not (null $ eps nfa)
                            = error "this state quotient is only defined for epsilon-free nfa"
                            | b
                            = Just (nfaTrans (fm M.!) nfa)
                            | otherwise
                            = Nothing
                              where
                              mk     = if direction then makeFwdClasses else makeBwdClasses
                              (b,fm) = refine (mk nfa)

makeFwdClasses :: Ord a => NFA a Char -> Eqclasses a
makeFwdClasses nfa =  [ [ (x,charfunPar True nfa x) | x<-states nfa, final nfa x ]
                      , [ (x,charfunPar True nfa x) | x<-states nfa, not(final nfa x) ] ]

makeBwdClasses :: Ord a => NFA a Char -> Eqclasses a
makeBwdClasses nfa = let st = start nfa in
                      [ [ (st,charfunPar False nfa st)  ]
                      , [ (x, charfunPar False nfa x) | x<-states nfa, x/=st ] ]

