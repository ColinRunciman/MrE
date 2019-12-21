set sizes=(10,20,40,80,160,320,640,1280,2560)
set asizes=(1,2,3,4,8,16)

FOR %%i in %sizes% DO (
    FOR %%j in %asizes% DO (
        Tim.exe %1 -S%%i -W%%j >> times/%2
))
