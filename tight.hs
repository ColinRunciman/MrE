import Alphabet
import Comparison
import Expression
import Catalogue
import PreOrderTrees

--tight :: Alphabet -> Bool
--tight a = 2^(alphaLength a)-1==a

nonTightMinimal :: Int -> Int -> [RE]
nonTightMinimal n al = filter weirdo $ map pickMinList $ treeClasses $ poTree (take al ['a'..]) n

tightMinimal :: Int -> Int -> [RE]
tightMinimal n al = filter (not.weirdo) $ map pickMinList $ treeClasses $ poTree (take al ['a'..]) n


weirdo :: RE -> Bool
weirdo x = (not $ tight $ fir x) || (not $ tight $ (fir x) .||. (las x))
    
