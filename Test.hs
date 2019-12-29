-- Test that all MrE transformations are valid in the sense that they
-- give results equivalent to their inputs, and no larger than their inputs.
-- A command-line argument specifies the number of test expressions to be
-- used, drawn from a LeanCheck series.

import List
import Expression
import Info
import Catalogue
import Context
import Comparison
import Fuse
import Parameters
import Pressing
import Stellation
import StarPromotion
import SyntaxCatalogue
import Test.LeanCheck
import System.Environment

-- This instance lists without repetition all the Emp-free and Lam-free
-- REs over the binary alphabet {a,b} satisfying the RE invariant.

instance Listable RE where
  tiers  =  [[Sym 'a'], [Sym 'b']] \/
            filterCons1 a alt \/ filterCons1 c cat \/
            filterCons1 r rep \/ filterCons1 o opt
            where
            a xs  =  plural xs && not (any (\x -> isAlt x || isOpt x) xs) &&
                     strictlyOrdered xs
            c xs  =  plural xs && not (any isCat xs)
            r x   =  not (isRep x || isOpt x)
            o x   =  not (ewp x)

filterCons1 :: Listable a => (a->Bool) -> (a->b) -> [[b]]
filterCons1 p f  =  delay $ mapT f $ filterT p tiers

instance Listable Grade where
  tiers  =  [[Normal .. SemCatMinimal]]

valid :: RE -> Grade -> Bool
valid x g  =  (y ==== x) && (size y <= size x)
  where
  y  =  transFun (defaults{trafo=g}) x

main  =  do [n] <- getArgs
            mapM_ (putStrLn . unwords)
                  (counterExamples (abs (read n) * length (list :: [Grade])) valid)
