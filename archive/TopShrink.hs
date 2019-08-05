module TopShrink where
import Info
import Context
import Expression
import List
import Fuse
import StarPromotion
import Comparison
-- shrinking, but only at top, only mkAlt/mkCat style
-- point is: these are mkCat/mkAlt shrinking that can retain attributes

topShrinkAltList :: RewRule
topShrinkAltList c i xs =
      list2OK xs $  [ [altSubseq old ys] | (x,ys) <- itemRest xs, sublang x (la (fuseAlt ys)) ]
      where old  = Alt i xs
            la   = contextFunction c
            lang = la old

-- note that in the first list comprehension we are forming a subcat and can therefore maintain attributes
topShrinkCatList :: RewRule
topShrinkCatList c i xs =
      list2OK xs $ [ [catSegment old xs'] | xs' <- [ tail xs | ewp (head xs) || c>NoCxt]
                                                ++ [ init xs | ewp (last xs) || c>NoCxt],
                     lang === la (fuseCat(xs')) ] ++
                   [ xs' | (ys,y,zs)<-segElemSuf xs, not(null ys) && not(null zs) && ewp y, let xs'=ys++zs,
                           lang === la(fuseCat xs') ]
      where old  = Cat i xs
            la   = contextFunction c
            lang = la old

topshrinkEX = mkExtension topShrinkAltList topShrinkCatList promoteKP Topshrunk

topShrinkK = khom $ target topshrinkEX

topshrink :: RE -> RE
topshrink x = valOf $ katahom topShrinkK NoCxt x

