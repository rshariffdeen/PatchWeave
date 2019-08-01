#!/bin/bash

declare -a directories
directories=(normal asan-addr asan-mem asan-int asan-undef)

declare -a subdirectories
i=0
while read line
do
	subdirectories[ $i ]="$line"
    (( i++ ))
done < <(ls normal)

declare -a exploits
i=0
while read line
do
    exploits[ $i ]="$line"
    (( i++ ))
done < <(ls $1)


for e in "${exploits[@]}";
do
	printf "\n\n$e"
	printf "\n*********************************************\n"
	for dir in "${directories[@]}";
	do
		printf "\n$dir"
		printf "\n=====================================\n"

		for subdir in "${subdirectories[@]}";
		do
			printf "\n$dir/$subdir"
			printf "\n---------------------------------\n"
			if [ -f ./$dir/$subdir/build/mp42aac ]; then
				printf "$ mp42aac $e output.aac \n"
				timeout 5m ./$dir/$subdir/build/mp42aac $1/$e output.aac
            fi
			if [ -f ./$dir/$subdir/build/aac2mp4 ]; then
				printf "$ aac2mp4 $e output.mp4 \n"
				timeout 5m ./$dir/$subdir/build/aac2mp4 $1/$e output.mp4
            fi
		done
	done
done
