module Museum where
import Alphabet
import Comparison
import Expression
import Info
import Context
import Generator
import List
import StarPromotion

-- IO return type, so we can report stage of progress
britishMuseumMethod :: RE -> KataPred -> IO RE
britishMuseumMethod re kp =
    bmm (createGradedCarrier (alpha2String $ alpha re) kp)
    where
    nre = mkTransform (khom kp) re
    bmm car = putStrLn ("transforming " ++ show nre) >> stage 0 car
    give result = do  putStrLn $ "found " ++ show result
                      return result
    stage n car = do
                     putStrLn $ "trying REs of size " ++ show n
                     let equis = filter (===nre) (head car)
                     if null equis then stage (n+1)(tail car)
                     else give (head equis)

-- same as britishMuseumMethod, but does not report on progress
silentMuseumMethod :: RE -> RE
silentMuseumMethod re =
    head [ ne | sz <- car, r <- sz, okGradeCxt Promoted c r, let ne = f r, ne===re ]
    where
    (f,e,c) = splitContext (promote re)
    car     = makeCarrier (alpha2String $ alpha e)


makeCarrier :: String -> Carrier
makeCarrier s = createGradedCarrier s promoteKP

disjoint :: RE -> RE -> Bool
disjoint a b = isEmptyAlpha (alpha a .&&. alpha b)

-- splits the re into an irreducible context, and its smaller content
-- if splitContext e1=(f,e2) then
-- (i) f e2==e1
-- (ii) e3===e2 => f e3===f e2
-- (iii) a minimal-size version of e1 is of the form f e0 for some e0
-- (iv) either f=id, e1=e2 or size e2<size e1
splitCxt :: RE -> Cxt-> Bool -> (RE->RE,RE,Cxt)
splitCxt (Alt _ xs) c False | not (null csplit)
                            = head csplit
                              where
                              csplit = [ (\e'-> alt[f e',s],e,d)
                                      | (s,ys)<-itemRest xs, singleCharC s, all (disjoint s) ys, let (f,e,d)=splitCxt (alt ys) (max c NoCxt) True ]
splitCxt (Cat _ (x:xs)) c b | singleChar x
                            = let (f,e,d)=splitCxt (cat xs) NoCxt b in (\e'->cat[x,f e'],e,d)
                            | singleChar l
                            = let (f,e,d)=splitCxt (cat ini) NoCxt b in (\e'->cat[f e',l],e,d)
                              where Just(ini,l) = unsnoc (x:xs)
splitCxt (Rep x)  _ False   = let (f,e,d)=splitCxt x RepCxt True in (Rep . f,e,d)
splitCxt re   c   _         = (id,re,c)

splitContext :: RE -> (RE->RE,RE,Cxt)
splitContext e = splitCxt e RootCxt False

refactor :: Bool -> RE -> Maybe (Char,RE)
refactor b (Sym c)     = Just (c,Lam)
refactor b (Alt i xs)  | ew i || b && not (singularAlpha (fi i)) || not b && not (singularAlpha (la i))
                       = Nothing
                       | otherwise
                       = Just (c,alt ys)
                          where
                          (c,ys) = process (map (refactor b) xs)
                          process (Just (d,x):ys) = (d,x:[y|Just(_,y)<- ys])
refactor b (Cat i xs)  | ew i || b && not (singularAlpha (fi i)) || not b && not (singularAlpha (la i))
                       = Nothing
                       | otherwise
                       = Just (c, (cat $ if b then ys else reverse ys))
                         where (c,ys) = refactorSequence b (if b then xs else reverse xs)
refactor b _           = Nothing


refactorSequence :: Bool -> [RE] -> (Char,[RE])
refactorSequence b (x:xs) | not (ewp x)
                          = (c,e:xs)
                          | otherwise
                          = (d,refactorRoll x d b:ys)
                            where
                            Just (c,e) = refactor b x
                            (d,ys)     = refactorSequence b xs
refactorSequence _ []     = error "empty sequence not factorisable"



-- add the char at the end/beginning, remove it from the other end 
refactorRoll :: RE -> Char -> Bool -> RE
refactorRoll Emp  _ _       = error "invariant violation in rolling"
refactorRoll Lam  _ _       = Lam -- not needed because of options
refactorRoll (Sym c) _ _    = Sym c
refactorRoll (Alt _ xs) d b = alt [ refactorRoll x d b | x<- xs ]
refactorRoll (Cat _ xs) d True =   cat ys
                                   where (_,ys) = refactorSequence True (xs ++ [Sym d])
refactorRoll (Cat _ xs) d False =  cat (reverse ys)
                                   where (_,ys) = refactorSequence False $ reverse (Sym d: xs)
refactorRoll (Rep x) d b    = Rep (refactorRoll x d b)
refactorRoll (Opt x) d b    = Opt (refactorRoll x d b)


singleChar :: RE -> Bool
singleChar (Sym _)    = True
singleChar (Alt _ xs) = all isSym xs
singleChar _          = False

singleCharC :: RE -> Bool
singleCharC (Sym _)    = True
singleCharC (Cat _ xs) = all isSym xs
singleCharC _          = False


museum :: RE -> RE
museum x = silentMuseumMethod x


