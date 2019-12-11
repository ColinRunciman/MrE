module Parameters (Parameters(..), argsToParams, transFun, stringTransFun, readBeforeT, sizeForT, sizeTransFun, PopulationFile(..), contents, reportInput, transKP) where

import Context
import Info
import Expression
import Pressing
import StarPromotion
import Stellation
import Catalogue
import SyntaxCatalogue (syncat, synCatalogueKP)
import GruberP
import Parser
import Fuse
import Museum
import Data.Maybe (fromMaybe)
-- this module defines program parameters for various transformation programs

type Source = Maybe PopulationFile

data Parameters =
     Parameters {
         trafo  :: Grade,
         inputsource :: Source,
         verbose :: Bool,
         allGrades :: [Grade]
     }

-- note: in principle, one could compose transformations:
-- the Grades would then be of type RE -> OK RE, given by katahom bla RootCxt,
-- and their composition would be:
-- fixOK $ t1 `aft` (fmap degrade . t2 . degrade)
-- the degrading (at least some form of it) would be needed because these could operate outside their hierarchy

data PopulationFile = PopulationFile { width :: Int, ofsize :: Int }

defaultWidth :: Int
defaultWidth  =  2

defaultREsize :: Int
defaultREsize = 10

defaultPopFile :: PopulationFile
defaultPopFile = PopulationFile { width = defaultWidth, ofsize = defaultREsize }

-- Nothing inputsource means: stdin
defaults :: Parameters
defaults = Parameters { trafo = Promoted, inputsource = Nothing, verbose=False, allGrades=[] }

updateWidth :: Source -> Int -> Source
updateWidth inputsource w   = Just $ (fromMaybe defaultPopFile inputsource) { width = w}

updateSize :: Source -> Int -> Source
updateSize inputsource s   = Just $ (fromMaybe defaultPopFile inputsource) { ofsize = s}
                        
argsToParams :: [String] -> Parameters
argsToParams ss = resetBy ss defaults

resetBy :: [String] -> Parameters -> Parameters
resetBy []     p  =  p
resetBy (s:ss) p  =  resetBy ss $
                     case letter of
                     'g' -> pushGrade GruberGulan
                     'n' -> pushGrade Normal
                     's' -> pushGrade Stellar
                     'f' -> pushGrade Fused
                     'l' -> pushGrade Promoted
                     'p' -> pushGrade Pressed
                     'c' -> pushGrade SemCatMinimal
                     'y' -> pushGrade SynCatMinimal
                     'm' -> pushGrade Minimal
                     'v' -> p { verbose = True }
                     'S' -> p { inputsource = updateSize  (inputsource p) number }
                     'W' -> p { inputsource = updateWidth (inputsource p) number }
                     _   -> error usage
                     where
                       pushGrade t = p { trafo = t, allGrades = t:allGrades p }
                       '-':letter:digits  =  s
                       number             =  read digits 

-- REVISIT: options -i, -v not explained here and other names obsolete
usage, explanation :: String
usage       = "MrE [-g|-n|-s|-f|-l|-p|-c|-y|-m] \n" ++ explanation
explanation = "REs are taken from stdin, unless options -Sno -Wno specify a file in the populations directory"

contents :: Source -> IO String
contents Nothing   = getContents
contents (Just pf) = readFile $
                     "populations/s" ++ show (ofsize pf) ++ "w" ++ show (width pf)

transFun :: Grade -> RE -> RE 
transFun GruberGulan    =  ggTrans -- both argument and result may be abNormal
transFun Normal         =  id
transFun Fused          =  fuse
transFun Promoted       =  promote
transFun Stellar        =  stellate
transFun Pressed        =  press
transFun SynCatMinimal  =  syncat
transFun SemCatMinimal  =  semcat
transFun Minimal        =  museum

transKP :: Grade -> KataPred
transKP Fused          = fuseKP
transKP Promoted       = promoteKP
transKP Stellar        = stelKP
transKP Pressed        = pressKP
transKP SynCatMinimal  = synCatalogueKP
transKP SemCatMinimal  = semCatalogueKP
transKP g              = error $ "no KataPred for "++show g++" REs"

-- does a grade ensure validated REs with attributes?
unvalidated :: Grade -> Bool 
unvalidated GruberGulan  =  True
unvalidated x            =  False

-- view the RE Grade as a string Grade
stringTransFun :: Grade -> String -> String
stringTransFun x   = show . transFun x . readBeforeT x

-- pick a parser, depending on the grade
readBeforeT :: Grade -> String -> RE
readBeforeT t   |  unvalidated t
                =  readFullExp
                |  otherwise
                =  read

-- for non-memoized size fields, pick the tail-recursive ggSize
sizeForT :: Grade -> RE -> Int
sizeForT t  |  unvalidated t
            =  gSize
            |  otherwise
            =  size

-- transform the RE from a string to an Int (the size of the transformed)
sizeTransFun   ::  Grade -> String -> Int
sizeTransFun x  =  sizeForT x . transFun x . readBeforeT x

reportInput :: Source -> String
reportInput Nothing   =  ""
reportInput (Just pf) =  show (width pf) ++ "\t" ++ show (ofsize pf) ++ "\t"

