IF EXIST effects (del /Q effects\*) ELSE (mkdir effects)

call allSizes.cmd -v prom
call allSizes.cmd -l linear-l
call allSizes.cmd -k kata-k
call allSizes.cmd -q fuse-q
call allSizes.cmd -p press-p
call allSizes.cmd "-*" "stellate-*"
call allSizes.cmd -c semcat-c
call allSizes.cmd -y syncat-y
