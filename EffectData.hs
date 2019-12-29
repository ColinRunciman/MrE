
import ReadTable
import System.Environment

effectsdir :: Bool -> String
effectsdir p = "effects" ++ (if p then "-u" else "")

tableheader :: Bool -> String
tableheader p = "Geometric means " ++
                (if p then "(unltd trafo) " else "") ++
                "of outputs"
tablefooter :: String
tablefooter = "Resulting expression size (\\%) for expressions of size "

main = do
    args <- getArgs
    let p = argsToBool args
    processDirectory (effectsdir p) $
       produceGenericTable (tableheader p) tablefooter 1.0
