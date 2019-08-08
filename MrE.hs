module Main where

import Info
import Context
import Data.List (isPrefixOf)
import Expression
import Pressing
import StarPromotion
import Stellation
import Catalogue
import SyntaxCatalogue (syncat)
import System.Environment
import GruberP
import Fuse

-- MrE simplies REs given as a command-line arguments, or if there is
-- no RE argument, the REs on successive stdinput lines.
-- By default, the output is the stellated input, on stdout.
-- However, there may be an initial option argument:
-- -q quick mode: promote only
-- -p press: will be slow for large expressions
-- -m minimizing mode: stellation + minimization using semantic catalogues
-- -z pressing after using the catalogue

-- TO DO: allow users to assemble their own hierarchy of transformations
-- this would be at odds with our enum type for Grades though

usage = "MrE [-q | -m | -p | -c | -s | -z | -k | -y ] re1 re2 ...\n"

stelEX2 :: Extension
stelEX2 = mkExtension altTrans catTrans (target minByCatalogueExtension) Stellar
catalogueStellate = mkTransform (khom (target stelEX2))


-- Note this uses 'Stellar' as a tag, because Pressed is below Catalogued in the order
pressEX2 :: Extension
pressEX2 = mkExtension pressAltListOne pressCatListOne (target minByCatalogueExtension) Stellar
cataloguePress = mkTransform (khom (target pressEX2))


main = do
  args <- getArgs
  (simple, inputs) <- interpret args
  mapM_ (print . simple ) inputs

interpret :: [String] -> IO (String->RE,[String])
interpret args =
  case inpArgs of
  [] -> do
          inp <- getContents
          return (simple, lines inp)
  _  -> do
          return (simple, inpArgs)
  where
  promread           = promote . read {- standard strategy: reduce size via promotion first -}
  (optArgs, inpArgs) = span ("-" `isPrefixOf`) args
  simple = case optArgs of
           []     -> promread {- default: promotion; it's fast, but not superfast -}
           ["-s"] -> stellate . promread 
           ["-q"] -> fuse . read    {- fusion is faster than promotion -}
           ["-m"] -> catalogueStellate . promread
           ["-c"] -> catalogue . promread
           ["-p"] -> press . promread {- let press not even see the whole thing -}
           ["-z"] -> cataloguePress . promread
           ["-l"] -> linearTrans -- uses dedicated parser to maintain linearity
           ["-k"] -> kataGrade . read
           ["-y"] -> syncat . promread

