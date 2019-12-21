-- times summary
-- reads the times for the varying trafos from the files in the times directory
-- and assembles them into a latex file
import qualified Data.Map.Strict as M
import qualified Data.IntSet as S
import Numeric
import ReadTable

filenames, trafonames :: [String]
filenames  = [ "Gruber-Gulan",  "normal",    "fused",  "promoted",  "stellar",   "pressed", "synsearch",    "semsearch"]
trafonames = [ "Gruber-Gulan+", "normalise", "+ fuse", "+ promote", "+ stellate","+ press", "+ syn.search", "+sem. search"]

tableEntries :: [String] -> String
tableEntries xs = concat $ map (" & " ++ )  xs

main = do
    statelist <- mapM readTable $ map ("times/"++) filenames
    let alplist = S.elems $ fst (head statelist)
    let maplist = map snd statelist
    let sizelist = M.keys (head maplist)
    let alpString = tableEntries $ map show alplist
    mapM_ (produceTable maplist alpString) sizelist

produceTable :: [M.Map Int [Double]] -> String -> Int -> IO()
produceTable tabs sizes n =
    do
        putStrLn "\\begin{figure}\\begin{tabular}{rrrrrrrrrr}"
        putStrLn " & \\multicolumn{9}{c}{Average simplification time for size:} \\\\"
        putStrLn $ sizes ++ " \\\\"
        mapM_ produceRow (zip trafonames [ t M.! n | t<-tabs])
        putStrLn $ "\\end{tabular}\\caption{Run-times (ms) for alphabets of size " ++ show n ++ ".}\\end{figure}"

printFloat :: Double -> String
printFloat d = showFFloat (Just 2) d ""

produceRow :: (String,[Double]) -> IO ()
produceRow (title,ds) =
    do
        let nds = [ printFloat (1000.0*d) | d<- ds]
        putStr title
        putStr $ tableEntries nds
        putStrLn " \\\\"
