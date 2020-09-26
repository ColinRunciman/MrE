-- Copyright: (c) 2020 Stefan Kahrs & Colin Runciman
-- License: Creative Commons Attribution-NonCommercial-ShareAlike 4.0

import System.Directory
import Control.Monad
import Catalogue
import SyntaxCatalogue

dir = "syncatalogue"

main  =  do ex <- doesDirectoryExist dir
            when ex (removeDirectoryRecursive dir)
            createDirectory dir
            createSynForest

