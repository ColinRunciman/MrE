import System.Directory
import Control.Monad
import Catalogue
import SyntaxCatalogue

dir = "syncatalogue"

main  =  do ex <- doesDirectoryExist dir
            when ex (removeDirectoryRecursive dir)
            createDirectory dir
            createSynForest

