module Main where

import qualified Data.Map.Strict as M
import qualified Data.IntSet as S
--import Data.List.Extra (trimStart) -- we rewrite it instead

type State = (S.IntSet,M.Map Int [Double])

make2D :: [(Int,Int,Double)] -> State
make2D trs = foldr addTriple (S.empty,M.empty) trs

addTriple :: (Int,Int,Double) -> State -> State
addTriple (al,ex,ef) (szs,mp) = (S.insert ex szs,M.insertWith ((++)) al [ef] mp)

type Record = (Int,[Double])

printList :: [String] -> IO()
printList [x]    = putStrLn x
printList (x:xs) = putStr (x++",") >> printList xs
printList []     = error "list should not be empty"

printRecord :: Record -> IO()
printRecord (n,ds) = putStr (show n++",") >> printList (map show ds)

main :: IO()
main = do
    s <- getContents
    let ls = lines s
    let out = map readTriple ls
    let (h,rs) = make2D out
    printList ("size":map show (S.elems h))
    mapM printRecord (M.toList rs)
    return ()

-- as the field are separated by tabs, we simply skip them, without checking
readTriple :: String -> (Int,Int,Double)
readTriple s = head [(al,es,ef)| (al,r1)<-reads s,
                     (es,r2)<-reads (trimStart r1), (ef,_)<-reads (trimStart r2)]

trimStart (' ':xs)  = trimStart xs
trimStart ('\t':xs) = trimStart xs
trimStart xs        = xs
