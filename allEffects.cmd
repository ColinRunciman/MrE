IF EXIST effects (del /Q effects\*) ELSE (mkdir effects)

call allSizes.cmd -g Gruber-Gulan
call allSizes.cmd -n normal
call allSizes.cmd -f fused
call allSizes.cmd -l promoted
call allSizes.cmd -s stellar
call allSizes.cmd -p pressed
call allSizes.cmd -y synsearch
call allSizes.cmd -c semsearch

