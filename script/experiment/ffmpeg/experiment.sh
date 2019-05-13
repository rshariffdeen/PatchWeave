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
			if [ -f ./$dir/$subdir/ffmpeg_g ]; then
				printf "$ ffmpeg_g -threads 1 -y -i $e -threads 1 -c:v mpeg4 -c:a copy output.mp4"
				timeout 5m ./$dir/$subdir/ffmpeg_g -threads 1 -y -i $1/$e -threads 1 -c:v mpeg4 -c:a copy out.mp4
			fi
		done
	done
done
