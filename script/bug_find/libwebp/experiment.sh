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
			if [ -f ./$dir/$subdir/cwebp ]; then
				printf "$ cwebp $e -o output.webp \n"
				timeout 5m ./$dir/$subdir/cwebp $1/$e -o output.webp
            fi
			if [ -f ./$dir/$subdir/examples/cwebp  ]; then
				printf "$ cwebp $e -o output.webp \n"
				timeout 5m ./$dir/$subdir/examples/cwebp $1/$e -o output.webp
            fi

			if [ -f ./$dir/$subdir/gif2webp ]; then
				printf "$ gif2webp $e -o output.webp \n"
				timeout 5m ./$dir/$subdir/gif2webp $1/$e -o output.webp
            fi
			if [ -f ./$dir/$subdir/examples/gif2webp ]; then
				printf "$ gif2webp $e -o output.webp \n"
				timeout 5m ./$dir/$subdir/examples/gif2webp $1/$e -o output.webp
            fi
		done
	done
done

