set timelimit=%1
set timingsdir=timings%2
set effectsdir=effects%2
IF EXIST %timingsdir% (del /Q %timingsdir%\*) ELSE (mkdir %timingsdir%)
IF EXIST %effectsdir% (del /Q %effectsdir%\*) ELSE (mkdir %effectsdir%)

call allSizes.cmd -g Gruber-Gulan %timelimit% %2
call allSizes.cmd -n normal       %timelimit% %2
call allSizes.cmd -f fused        %timelimit% %2
call allSizes.cmd -l promoted     %timelimit% %2
call allSizes.cmd -s stellar      %timelimit% %2
call allSizes.cmd -p pressed      %timelimit% %2
call allSizes.cmd -y synsearch    %timelimit% %2
call allSizes.cmd -c semsearch    %timelimit% %2
