
import ReadTable
import System.Environment

timingsdir :: Bool -> String
timingsdir p = "timings" ++ (if p then "-u" else "")

tableheader :: Bool -> String
tableheader p = "Average simplification time " ++
                (if p then "(unltd trafo) " else "") ++
                "for size"
tablefooter :: String
tablefooter = "Run-times (ms) for expressions of size "

main = do
    args <- getArgs
    let p = argsToBool args
    processDirectory (timingsdir p) $
       produceGenericTable (tableheader p) tablefooter 1000.0
