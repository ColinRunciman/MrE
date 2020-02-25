module Main where
import System.Environment
import Parameters
import Expression

main = do
    args <- getArgs
    let p = argsToParams args
    input <- fmap lines $ contents $ inputsource p
    let res = map (readBeforeT (trafo p)) input
    let sws = filter (\x->swa x==alpha x) res
    let tot = filter isRep $ map (transFun p) sws
    putStrLn ("number of expressions: " ++ show(length res))
    putStrLn ("swp for all their charcaters: " ++ show (length sws))
    putStrLn ("total language for all their characters: " ++ show (length tot))
