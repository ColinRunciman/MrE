module FactSearch where
import Info
import Generator
import StarPromotion
import Catalogue
import Expression
import Alphabet
import OK

type Pred = RE -> RE -> Bool

ascond :: Pred
ascond (Cat _ x1) x2 = all singleChar x1
ascond x1 x2 = singleChar x1

ascond2 :: Pred
ascond2 (Cat _ x1) x2 = all isSym x1
ascond2 x1 x2         = isSym x1


lastCharCondition :: Pred
lastCharCondition x1 x2 = isEmptyAlpha $ las x1 .&&. alpha x2

lcc2 :: Pred
lcc2 x1 x2 = lastCharCondition x1 x2 && singularAlpha(las x1)

disjointCharCondition :: Pred
disjointCharCondition x1 x2 = isEmptyAlpha $ alpha x1 .&&. alpha x2

dcc2 :: Pred
dcc2 x1 x2 = disjointCharCondition x1 x2 && not(ewp x1) && not(ewp x2)

-- condition for Alts
filac :: Pred
filac x1 x2 = isEmptyAlpha $ (fir x1 .&&. fir x2) .||. (las x1 .&&. las x2)

pool :: [RE]
pool = concat $ createGradedCarrier "abc" promoteKP

-- no base case, these are infinite lists
altlists, catlists :: [RE] -> [[RE]]
altlists (Alt _ xs: res) = xs : altlists res
altlists (_       : res) = altlists res

catlists (Cat _ xs: res) = xs : catlists res
catlists (_       : res) = catlists res

altpool = altlists pool
catpool = catlists pool
optpool = map unOpt $ filter isOpt pool
reppool = map unRep $ filter isRep pool

optaltpool = altlists optpool
optcatpool = catlists optpool
repaltpool = altlists reppool
repcatpool = catlists reppool

listSplits :: [a] -> [([a],[a])]
listSplits [x,y] = [([x],[y])]
listSplits (x:xs) = ([x],xs): [(x:ys,zs) | (ys,zs) <- listSplits xs]

disjointCandidates :: ([RE]->RE) -> [[RE]] -> [(RE,RE)]
disjointCandidates cons ps = [ (x,y) | cs <- ps, (xs,ys) <- listSplits cs,
                               let x=cons xs, let y=rename (zip "abcdef" "vwxyz") $ cons ys]

disjointRepCounterExamples :: Int -> [(RE,RE)]
disjointRepCounterExamples n = take 10 $ [ (t1,t2) | (t1,t2)<-take n (disjointCandidates alt repaltpool), reptest alt t1 t2]

testCandidates :: Pred -> ([RE]->RE) -> [[RE]] -> [(RE,RE)]
testCandidates p cons ps = [(x,y)| cs <- ps, (xs,ys)<-listSplits cs,
                              let x=cons xs, let y=cons ys, p x y]

plaintest cons t u = cons [semcat t,semcat u] //== semcat (cons [t,u])
ewptest t u = opt (alt [valOf $ semCatalogueCxt OptCxt t,valOf $ semCatalogueCxt OptCxt u]) //== semcat (alt[t,u])
opttest cons t u = opt(cons [semcat t,semcat u]) //== semcat (opt(cons [t,u]))
reptest cons t u = rep(cons [valOf $ semCatalogueCxt RepCxt t,valOf $ semCatalogueCxt RepCxt u]) //== semcat (rep(cons [t,u]))

plainCatCounterExamples :: Pred -> Int -> [(RE,RE)]
plainCatCounterExamples p n = take 10 $
    [ (t1,t2) | (t1,t2)<-take n (testCandidates p cat catpool),
                plaintest cat t1 t2 ]

plainAltCounterExamples :: Pred -> Int -> [(RE,RE)]
plainAltCounterExamples p n = take 10 $
    [ (t1,t2) | (t1,t2)<-take n (testCandidates p alt altpool),
                if ewp t1 || ewp t2 then ewptest t1 t2 else plaintest alt t1 t2 ]

optCatCounterExamples :: Pred -> Int -> [(RE,RE)]
optCatCounterExamples p n = take 10 $
    [ (t1,t2) | (t1,t2)<-take n (testCandidates p cat optcatpool),
                opttest cat t1 t2 ]

optAltCounterExamples :: Pred -> Int -> [(RE,RE)]
optAltCounterExamples p n = take 10 $
    [ (t1,t2) | (t1,t2)<-take n (testCandidates p alt optaltpool),
                opttest alt (opt t1) (opt t2) ]

repCatCounterExamples :: Pred -> Int -> [(RE,RE)]
repCatCounterExamples p n = take 10 $
    [ (t1,t2) | (t1,t2)<-take n (testCandidates p cat repcatpool),
                reptest cat t1 t2 ]

repAltCounterExamples :: Pred -> Int -> [(RE,RE)]
repAltCounterExamples p n = take 10 $
    [ (t1,t2) | (t1,t2)<-take n (testCandidates p alt repaltpool),
                reptest alt t1 t2]

universalCatCounterExamples :: Pred -> Int -> [(RE,RE)]
universalCatCounterExamples p n = take 10 $
    plainCatCounterExamples p n ++ optCatCounterExamples p n ++ repCatCounterExamples p n

universalAltCounterExamples :: Pred -> Int -> [(RE,RE)]
universalAltCounterExamples p n = take 10 $
    plainAltCounterExamples p n ++ optAltCounterExamples p n ++ repAltCounterExamples p n

(//==) :: RE -> RE -> Bool
t //== u = size t > size u

-- TO DO
-- create a corresponding divide-and-conquer testing regime for Alts
-- test existing reduction predicate
-- disable current context reductions from MrE before testing
