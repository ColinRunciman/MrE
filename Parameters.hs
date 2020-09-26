-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

module Parameters (Parameters(..), argsToParams, defaults, transFun, stringTransFun, readBeforeT, sizeForT, sizeTransFun, timedCommand, PopulationFile(..), contents, reportInput, transKP) where

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
import System.Timeout
-- this module defines program parameters for various transformation programs

type Source = Maybe PopulationFile

data Parameters =
     Parameters {
         trafo  :: Grade,
         inputsource :: Source,
         verbose :: Bool,
         unlimited :: Bool,
         timebound :: Int,
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
defaults = Parameters { trafo = Promoted, inputsource = Nothing, verbose=False, unlimited=False, allGrades=[], timebound=0 }

updateWidth :: Source -> Int -> Source
updateWidth inputsource 0   = inputsource
updateWidth inputsource w   = Just $ (fromMaybe defaultPopFile inputsource) { width = w}

updateSize :: Source -> Int -> Source
updateSize inputsource 0   = inputsource
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
                     'u' -> p { unlimited = True }
                     'S' -> p { inputsource = updateSize  (inputsource p) number }
                     'W' -> p { inputsource = updateWidth (inputsource p) number }
                     'T' -> p { timebound = number }
                     _   -> error usage
                     where
                       pushGrade t = p { trafo = t, allGrades = t:allGrades p }
                       '-':letter:digits  =  s
                       number             =  if null digits then 0 else read digits

-- REVISIT: options -i, -v, -u, -S, -W not explained here and other names obsolete
usage, explanation :: String
usage       = "MrE [-g|-n|-s|-f|-l|-p|-c|-y|-m] \n" ++ explanation
explanation = "REs are taken from stdin, unless options -Sno -Wno specify a file in the populations directory"

contents :: Source -> IO String
contents Nothing   = getContents
contents (Just pf) = readFile $
                     "populations/s" ++ show (ofsize pf) ++ "w" ++ show (width pf)

transFun :: Parameters -> RE -> RE
transFun p = case trafo p of
             GruberGulan   -> ggTrans
             Normal        -> id
             Fused         -> fuse
             Promoted      -> promote
             Stellar       -> if unlimited p then stellateU else stellate
             Pressed       -> if unlimited p then pressU    else press
             SynCatMinimal -> syncat
             SemCatMinimal -> if unlimited p then semcatU else semcat
             Minimal       -> museum

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
stringTransFun :: Parameters -> String -> String
stringTransFun x   = show . transFun x . readBeforeT (trafo x)

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
sizeTransFun   ::  Parameters -> String -> Int
sizeTransFun x  =  sizeForT (trafo x) . transFun x . readBeforeT (trafo x)

reportInput :: Source -> String
reportInput Nothing   =  ""
reportInput (Just pf) =  show (width pf) ++ "\t" ++ show (ofsize pf) ++ "\t"

timedCommand :: Parameters -> IO () -> IO()
timedCommand par command | timebound par==0
                         = command
                         | otherwise
                         = timeout (10^6 * timebound par) command >> return ()
