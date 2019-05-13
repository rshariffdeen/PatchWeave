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
			if [ -f ./$dir/$subdir/binutils/nm ]; then
				printf "$ nm -A -a -l -S -s --special-syms --synthetic --with-symbol-versions -D $e \n"
				timeout 5m ./$dir/$subdir/binutils/nm -A -a -l -S -s --special-syms --synthetic --with-symbol-versions -D $1/$e > /dev/null
				#echo "yes"
			fi
			if [ -f ./$dir/$subdir/binutils/nm-new ]; then
				printf "$ nm -A -a -l -S -s --special-syms --synthetic --with-symbol-versions -D $e \n"
				timeout 5m ./$dir/$subdir/binutils/nm-new -A -a -l -S -s --special-syms --synthetic --with-symbol-versions -D $1/$e > /dev/null
				#echo "yes"
			fi

			if [ -f ./$dir/$subdir/binutils/readelf ]; then
				printf "$ readelf -a $e \n"
				timeout 500ms ./$dir/$subdir/binutils/readelf -a $1/$e > /dev/null
				#echo "yes"
			fi
		done
	done
done
