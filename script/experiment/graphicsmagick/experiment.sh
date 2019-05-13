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
			if [ -f ./$dir/$subdir/utilities/gm ]; then
				printf "$ gm identify $e \n"
				timeout 5m ./$dir/$subdir/utilities/gm identify $1/$e

				printf "$ gm convert -negate -clip $e output \n"
				timeout 5m ./$dir/$subdir/utilities/gm convert -negate -clip $1/$e output

				printf "$ gm convert $e output \n"
				timeout 5m ./$dir/$subdir/utilities/gm convert $1/$e output

				rm -f output
			fi
		done
	done
done

