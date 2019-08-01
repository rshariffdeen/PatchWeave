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
			if [ -f ./$dir/$subdir/x86_64-pc-linux-gnu/bins/unzzip-mem ]; then
				printf "$ unzzip-mem $e\n"
				timeout 5m ./$dir/$subdir/x86_64-pc-linux-gnu/bins/unzzip-mem $1/$e
			fi
			if [ -f ./$dir/$subdir/x86_64-pc-linux-gnu/bins/unzzip-seeko ]; then
				printf "$ unzzipcat-seeko $e\n"
				timeout 5m ./$dir/$subdir/x86_64-pc-linux-gnu/bins/unzzip-seeko $1/$e
			fi
		done
	done
done
