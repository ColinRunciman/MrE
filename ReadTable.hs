module ReadTable where

import qualified Data.Map.Strict as M
import qualified Data.IntSet as S
import Numeric
--import Data.List.Extra (trimStart) -- we rewrite it instead

type State = (S.IntSet,M.Map Int [Double])

make2D :: [(Int,Int,Double)] -> State
make2D trs = foldr addTriple (S.empty,M.empty) trs

addTriple :: (Int,Int,Double) -> State -> State
addTriple (al,ex,ef) (szs,mp) = (S.insert al szs,M.insertWith ((++)) ex [ef] mp)

readTable:: String -> IO State
readTable filename = do
    s <- readFile filename
    let ls = lines s
    let out = map readTriple ls
    return $ make2D out

-- as the field are separated by tabs, we simply skip them, without checking
readTriple :: String -> (Int,Int,Double)
readTriple s = head [(al,es,ef)| (al,r1)<-reads s,
                     (es,r2)<-reads (trimStart r1), (ef,_)<-reads (trimStart r2)]

trimStart (' ':xs)  = trimStart xs
trimStart ('\t':xs) = trimStart xs
trimStart xs        = xs

filenames, trafonames :: [String]
filenames  = [ "Gruber-Gulan",  "normal",    "fused",  "promoted",  "stellar",   "pressed", "synsearch",    "semsearch"]
trafonames = [ "Gruber-Gulan+", "normalise", "+ fuse", "+ promote", "+ stellate","+ press", "+ syn.search", "+ sem. search"]

tableEntries :: [String] -> String
tableEntries xs = concat $ map (" & " ++ )  xs

processDirectory :: String -> ([M.Map Int [Double]] -> String -> Int -> IO()) -> IO()
processDirectory dir pt = do
    statelist <- mapM readTable $ map ((dir ++ "/")++) filenames
    let alplist = S.elems $ fst (head statelist)
    let maplist = map snd statelist
    let sizelist = M.keys (head maplist)
    let alpString = tableEntries $ map show alplist
    mapM_ (pt maplist alpString) sizelist

printFloat :: Double -> String
printFloat d = showFFloat (Just 2) d ""

produceRow :: Double -> (String,[Double]) -> IO ()
produceRow scalar (title,ds) =
    do
        let nds = [ printFloat (scalar*d) | d<- ds]
        putStr title
        putStr $ tableEntries nds
        putStrLn " \\\\"

produceGenericTable :: String -> String -> Double -> [M.Map Int [Double]] -> String -> Int -> IO()
produceGenericTable header footer scalar tabs sizes n =
  do
      putStrLn "\\begin{figure}\\begin{tabular}{rrrrrrrrrr}"
      putStrLn $ " & \\multicolumn{9}{c}{" ++ header ++ "} \\\\"
      putStrLn $ sizes ++ " \\\\"
      mapM_ (produceRow scalar) (zip trafonames [ t M.! n | t<-tabs])
      putStrLn $ "\\end{tabular}\\caption{" ++ footer ++ show n ++ ".}\\end{figure}"
