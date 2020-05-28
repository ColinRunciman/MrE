IF EXIST times (del /Q times\*) ELSE (mkdir times)

call allSizesT.cmd -g Gruber-Gulan
call allSizesT.cmd -n normal
call allSizesT.cmd -f fused
call allSizesT.cmd -l promoted
call allSizesT.cmd -s stellar
call allSizesT.cmd -p pressed
call allSizesT.cmd -y synsearch
call allSizesT.cmd -c semsearch

