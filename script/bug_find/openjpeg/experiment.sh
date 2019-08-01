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
			if [ -f ./$dir/$subdir/bin/j2k_dump ]; then
               printf "\n j2k_dump -i $e \n";
               timeout 5m ./$dir/$subdir/bin/j2k_dump -i $1/$e
            fi
			if [ -f ./$dir/$subdir/bin/j2k_to_image ]; then
               printf "\n j2k_to_image -i $e -o output.pgm \n";
               timeout 5m  ./$dir/$subdir/bin/j2k_to_image -i $1/$e -o output.pgm
            fi
			if [ -f ./$dir/$subdir/bin/image_to_j2k ]; then
               printf "\n image_to_j2k -i $e -o output.j2k \n";
               timeout 5m ./$dir/$subdir/bin/image_to_j2k -i $1/$e -o output.j2k
            fi
			if [ -f ./$dir/$subdir/bin/opj_dump ]; then
				printf "$ opj_dump -i $e \n"
				timeout 5m ./$dir/$subdir/bin/opj_dump -i $1/$e
            fi
			if [ -f ./$dir/$subdir/bin/opj_decompress ]; then
				printf "$ opj_decompress -i $e -o output.pgm \n"
				timeout 5m ./$dir/$subdir/bin/opj_decompress -i $1/$e -o output.pgm
            fi
			if [ -f ./$dir/$subdir/bin/opj_compress ]; then
				printf "$ opj_compress -n 1 -i $e -o output.j2c \n"
				timeout 5m ./$dir/$subdir/bin/opj_compress -n 1 -i $1/$e -o output.j2c
            fi
			if [ -f ./$dir/$subdir/bin/opj_compress ]; then
				printf "$ opj_compress -r 20,10,1 -jpip -EPH -SOP -cinema2K 24 -n 1 -i $e -o output.j2k \n"
				timeout 5m ./$dir/$subdir/bin/opj_compress -r 20,10,1 -jpip -EPH -SOC -cinema2K 24 -n 1 -i $1/$e -o output.j2k
            fi
			if [ -f ./$dir/$subdir/bin/opj_compress ]; then
				printf "$ opj_compress -l cinema4K -n 1 -i $e -o output.jp2 \n"
				timeout 5m ./$dir/$subdir/bin/opj_compress -l -cinema4K -n 1 -i $1/$e -o output.jp2
            fi
			if [ -f ./$dir/$subdir/bin/opj_compress ]; then
				printf "$ opj_compress -n 1 -i $e -o output.j2k \n"
				timeout 5m ./$dir/$subdir/bin/opj_compress -n 1 -i $1/$e -o output.j2k
            fi
		done
	done
done

