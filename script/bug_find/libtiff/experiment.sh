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
			if [ -f ./$dir/$subdir/tools/bmp2tiff ]; then
				printf "$ bmp2tiff $e output.tiff \n"
				timeout 5m ./$dir/$subdir/tools/bmp2tiff $1/$e output.tiff
            		fi
			if [ -f ./$dir/$subdir/tools/gif2tiff ]; then
				printf "$ gif2tiff $e output.tiff \n"
				timeout 5m ./$dir/$subdir/tools/gif2tiff $1/$e output2.tiff
            		fi
			if [ -f ./$dir/$subdir/tools/ras2tiff ]; then
				printf "$ ras2tiff $e output.tiff \n"
				timeout 5m ./$dir/$subdir/tools/ras2tiff $1/$e output.tiff
			fi
			if [ -f ./$dir/$subdir/tools/raw2tiff ]; then
				printf "$ raw2tiff $e output.tiff \n"
				timeout 5m ./$dir/$subdir/tools/raw2tiff $1/$e output.tiff
            		fi
			if [ -f ./$dir/$subdir/tools/tiffcp ]; then
				printf "$ tiffcp -i $e output \n"
				timeout 5m ./$dir/$subdir/tools/tiffcp -i $1/$e output 2>/dev/null
            		fi
			if [ -f ./$dir/$subdir/tools/tiffcrop ]; then
				printf "$ tiffcrop -i $e output \n"
				timeout 5m ./$dir/$subdir/tools/tiffcrop -i $1/$e output 2>/dev/null
            		fi
			if [ -f ./$dir/$subdir/tools/tiff2ps ]; then
				printf "$ tiff2ps $e \n"
				timeout 5m ./$dir/$subdir/tools/tiff2ps $1/$e
            		fi
			if [ -f ./$dir/$subdir/tools/tiff2pdf ]; then
				printf "$ tiff2pdf $e -o output.pdf \n"
				timeout 5m ./$dir/$subdir/tools/tiff2pdf $1/$e -o output.pdf
            		fi
			if [ -f ./$dir/$subdir/tools/tiff2rgba ]; then
				printf "$ tiff2rgba $e output \n"
				timeout 5m ./$dir/$subdir/tools/tiff2rgba $1/$e output
            		fi
			if [ -f ./$dir/$subdir/tools/tiffmedian ]; then
				printf "$ tiffmedian $e output \n"
				timeout 5m ./$dir/$subdir/tools/tiffmedian $1/$e output
	        fi
			rm -f output.tiff output2.tiff output.pdf output
		done
	done
done

