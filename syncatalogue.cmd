IF EXIST syncatalogue (del /Q syncatalogue\*) ELSE (mkdir syncatalogue)
CreateSynCatalogue.exe
