module ReadTable where

import qualified Data.Map.Strict as M
-- import qualified Data.IntSet as S
import Numeric
import List (nubSort)
import Data.List (groupBy,sort)
--import Data.List.Extra (trimStart) -- we rewrite it instead

type NTable = M.Map Int [Maybe Double]
type State  = ([Int],NTable)
make2D :: [(Int,Int,Double)] -> State
make2D trs = (alphalist, M.fromList pmap)
             where
             sizelist   = nubSort [s | (s,_,_) <- trs]
             alphalist  = nubSort [a | (_,a,_) <- trs]
             pmap = map mapentry $ groupBy fsteq $ sort trs
             fsteq p q = fst3 p==fst3 q
             fst3 (x,_,_) = x
             mapentry xs = (fst3 (head xs),formList xs alphalist)
             formList [] xs = map (const Nothing) xs
             formList zs@((_,x,y):xs) (al:als)
                 | x==al
                 = Just y : formList xs als
                 | otherwise
                 = Nothing : formList zs als

readTable:: String -> IO State
readTable filename = do
    s <- readFile filename
    let ls = lines s
    let out = map readTriple ls
    return $ make2D out

-- as the field are separated by tabs, we simply skip them, without checking
-- es: expression size, al: alphabet size, ef: data value (time, average size, etc)
readTriple :: String -> (Int,Int,Double)
readTriple s = head [(es,al,ef)| (al,r1)<-reads s,
                     (es,r2)<-reads (trimStart r1), (ef,_)<-reads (trimStart r2)]

trimStart (' ':xs)  = trimStart xs
trimStart ('\t':xs) = trimStart xs
trimStart xs        = xs

filenames, trafonames :: [String]
filenames  = [ "Gruber-Gulan",  "normal",    "fused",  "promoted",  "stellar",   "pressed", "synsearch",    "semsearch"]
trafonames = [ "Gruber-Gulan+", "normalise", "+ fuse", "+ promote", "+ stellate","+ press", "+ syn.search", "+ sem. search"]

tableEntries :: [String] -> String
tableEntries xs = concat $ map (" & " ++ )  xs

processDirectory :: String -> ([NTable] -> String -> Int -> IO()) -> IO()
processDirectory dir pt = do
    statelist <- mapM readTable $ map ((dir ++ "/")++) filenames
    let alplist = fst (head statelist)
    let maplist = map snd statelist
    let sizelist = M.keys (head maplist)
    let alpString = tableEntries $ map show alplist
    mapM_ (pt maplist alpString) sizelist

printFloat :: Maybe Double -> String
printFloat (Just d) = showFFloat (Just 2) d ""
printFloat Nothing  = "--"

produceRow :: Double -> (String,[Maybe Double]) -> IO ()
produceRow scalar (title,ds) =
    do
        let nds = [ printFloat (fmap (scalar*) d) | d <- ds]
        putStr title
        putStr $ tableEntries nds
        putStrLn " \\\\"

argsToBool :: [String] -> Bool
argsToBool ["-u"] = True
argsToBool _      = False

produceGenericTable :: String -> String -> Double -> [NTable] -> String -> Int -> IO()
produceGenericTable header footer scalar tabs sizes n =
  do
      putStrLn "\\begin{figure}\\begin{tabular}{rrrrrrrrrr}"
      putStrLn $ " & \\multicolumn{9}{c}{" ++ header ++ "} \\\\"
      putStrLn $ sizes ++ " \\\\"
      mapM_ (produceRow scalar) (zip trafonames [ t M.! n | t<-tabs])
      putStrLn $ "\\end{tabular}\\caption{" ++ footer ++ show n ++ ".}\\end{figure}"
