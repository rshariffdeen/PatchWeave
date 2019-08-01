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
			if [ -f ./$dir/$subdir/imagew ]; then
				printf "$ imagew $e output -outfmt bmp \n"
				timeout 5m ./$dir/$subdir/imagew $1/$e output -outfmt bmp
            fi
			if [ -f ./$dir/$subdir/imagew ]; then
				printf "$ imagew $e output -outfmt jpg \n"
				timeout 5m ./$dir/$subdir/imagew $1/$e output -outfmt jpg
            fi
			if [ -f ./$dir/$subdir/imagew ]; then
				printf "$ imagew $e output -outfmt gif \n"
				timeout 5m ./$dir/$subdir/imagew $1/$e output -outfmt gif
            fi
			if [ -f ./$dir/$subdir/imagew ]; then
				printf "$ imagew $e output -outfmt tiff \n"
				timeout 5m ./$dir/$subdir/imagew $1/$e output -outfmt tiff
            fi
		done
	done
done
