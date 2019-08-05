module DeBruijn where
import Expression
-- produce something like a deBruijn normal form of an RE

deBruijnify :: RE -> (RE, Renaming)
deBruijnify e | isCanonical cs
              = (e,re)
              | otherwise
              = (e'',[(x,z)|(x,y)<-re,(y',z)<-re', y==y'])
    where
    cs = alphaL e
    re = zip cs ['a'..]
    e' = rename re e
    (e'',re') = deBruijnify e'


