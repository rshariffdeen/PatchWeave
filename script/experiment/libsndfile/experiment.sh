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
			if [ -f ./$dir/$subdir/programs/sndfile-convert ]; then
				printf "$ sndfile-convert $e out.wav \n"
				timeout 5m ./$dir/$subdir/programs/sndfile-convert $1/$e out.wav
            fi
			if [ -f ./$dir/$subdir/programs/sndfile-resample ]; then
				printf "$ sndfile-resample -to 24000 -c 1 $e out \n"
				timeout 5m ./$dir/$subdir/programs/sndfile-resample -to 24000 -c 1 $1/$e out
            fi
		done
	done
done

