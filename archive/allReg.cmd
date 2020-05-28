IF EXIST populations (del /Q populations\*) ELSE (mkdir populations)
set sizes=(10,20,40,80,160,320,640,1280,2560)
set asizes=(1,2,3,4,8,16)
FOR %%i in %sizes% DO (
    FOR %%j in %asizes% DO (
    Reg.exe -S%%i -W%%j -Q1000 > populations/s%%iw%%j
))
