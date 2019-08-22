module Parameters (Parameters(..), argsToParams, Trafo, transFun, stringTrafo, readBeforeT, sizeForT, sizeTrafo, PopulationFile(..), contents, reportInput) where

import Context
import Expression
import Pressing
import StarPromotion
import Stellation
import Catalogue
import SyntaxCatalogue (syncat)
import GruberP
import Parser
import Fuse
import Data.Maybe (fromMaybe)
-- this module defines program paramters for various transformation programs

type Source = Maybe PopulationFile

data Parameters =
     Parameters {
         trafo  :: Trafo,
         inputsource :: Source,
         verbose :: Bool
     }

-- note: in principle, one could compose transformations:
-- the trafos would then be of type RE -> OK RE, given by katahom bla RootCxt,
-- and their composition would be:
-- fixOK $ t1 `aft` (fmap degrade . t2 . degrade)
-- the degrading (at least some form of it) would be needed because these could operate outside their hierarchy
data Trafo = ID | Linear | KataTrafo | Fuse | Promote | Press | SemCat | SynCat | Stellation

data PopulationFile = PopulationFile { width :: Int, ofsize :: Int }

defaultWidth :: Int
defaultWidth  =  2

defaultREsize :: Int
defaultREsize = 10

defaultPopFile :: PopulationFile
defaultPopFile = PopulationFile { width = defaultWidth, ofsize = defaultREsize }

-- Nothing inputsource means: stdin
defaults :: Parameters
defaults = Parameters { trafo = Promote, inputsource = Nothing, verbose=False }

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
                     'i' -> p { trafo  = ID }
                     'l' -> p { trafo  = Linear }
                     'k' -> p { trafo  = KataTrafo }
                     '*' -> p { trafo  = Stellation }
                     'q' -> p { trafo  = Fuse }
                     'c' -> p { trafo  = SemCat }
                     'y' -> p { trafo  = SynCat }
                     'p' -> p { trafo  = Press }
                     'v' -> p { verbose = True }
                     's' -> p { inputsource = updateSize  (inputsource p) number }
                     'w' -> p { inputsource = updateWidth (inputsource p) number }
                     _   -> error usage
                     where
                       '-':letter:digits  =  s
                       number             =  read digits 

-- options -i, -v not explained here
usage, explanation :: String
usage       = "MrE [-l|-k|-*|-q|-c|-y|-p ] \n" ++ explanation
explanation = "REs are taken from stdin, unless options -sno -wno specify a file in the populations directory"

contents :: Source -> IO String
contents Nothing   = getContents
contents (Just pf) = readFile $ "populations/s" ++ show (ofsize pf) ++ "w" ++ show (width pf)


transFun :: Trafo -> RE -> RE
transFun ID          =  id      -- note: not validated REs
transFun Linear      =  ggTrans -- note: not validated REs
transFun KataTrafo   =  kataGrade
transFun Fuse        =  fuse
transFun Promote     =  promote
transFun Press       =  press
transFun SemCat      =  catalogue
transFun SynCat      =  syncat
transFun Stellation  =  stellate

-- does the trafo expect/produce validated REs with attributes?
unvalidatedTrafo :: Trafo -> Bool 
unvalidatedTrafo ID     =  True
unvalidatedTrafo Linear =  True
unvalidatedTrafo x      =  False

-- view the RE trafo as a string trafo
stringTrafo :: Trafo -> String -> String
stringTrafo x   = show . transFun x . readBeforeT x

-- pick a parser, depending on the trafo
readBeforeT :: Trafo -> String -> RE
readBeforeT t   |  unvalidatedTrafo t
                =  readFullExp
                |  otherwise
                =  read

-- for trafos with non-memoized size fields, pick the tail-recursive ggSize
sizeForT :: Trafo -> RE -> Int
sizeForT t  |  unvalidatedTrafo t
            =  gSize
            |  otherwise
            =  size

-- transform the RE from a string to an Int (the size of the transformed)
sizeTrafo   ::  Trafo -> String -> Int
sizeTrafo x  =  sizeForT x . transFun x . readBeforeT x

reportInput :: Source -> String
reportInput Nothing   =  ""
reportInput (Just pf) =  show (width pf) ++ "\t" ++ show (ofsize pf) ++ "\t"

