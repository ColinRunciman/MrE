-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module Function (kernel,fixBy,claim,justIf,(===>)) where

kernel :: Eq b => (a->b) -> a -> a -> Bool
kernel f t u = f t == f u

fixBy :: Eq a => (a->a) -> a -> a
fixBy f x  =  if x' == x then x else fixBy f x'
  where
  x'  =  f x


claim :: Show a => String -> (a->Bool) -> a -> a
-- claim-checking OFF:
claim s p  =  id
-- claim-checking ON:
{-
claim s p x  |  p x
             =  x
             |  otherwise
             =  error $ "claim failure: "++show x++" is not "++s
-}

-- justIf x y = guard x >> Just y
justIf :: Bool -> a -> Maybe a
justIf False _ = Nothing
justIf True  x = Just x

(===>) :: Bool -> Bool -> Bool
False ===> _  =  True
True  ===> b  =  b


