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
			if [ -f ./$dir/$subdir/build/tools/podofotxt2pdf/podofotxt2pdf ]; then
				printf "$ podofotxt2pdf $e out.pdf \n"
				timeout 5m ./$dir/$subdir/build/tools/podofotxt2pdf/podofotxt2pdf $1/$e output.pdf
            fi

			if [ -f ./$dir/$subdir/build/tools/podofocolor/podofocolor ]; then
				printf "$ podofocolor dummy $e foo \n"
				timeout 5m ./$dir/$subdir/build/tools/podofocolor/podofocolor dummy $1/$e foo
            fi

			if [ -f ./$dir/$subdir/build/tools/podofopdfinfo/podofopdfinfo ]; then
				printf "$ podofopdfinfo $e \n"
				timeout 5m ./$dir/$subdir/build/tools/podofopdfinfo/podofopdfinfo $1/$e
            fi

			if [ -f ./$dir/$subdir/build/tools/podofotxtextract/podofotxtextract ]; then
				printf "$ podofotxtextract $e \n"
				timeout 5m ./$dir/$subdir/build/tools/podofotxtextract/podofotxtextract $1/$e
            fi

		done
	done
done
