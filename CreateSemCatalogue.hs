import System.Directory
import Control.Monad
import Catalogue

dir   =  "semcatalogue"

main  =  do ex <- doesDirectoryExist dir
            when ex (removeDirectoryRecursive dir)
            createDirectory dir
            createForest
