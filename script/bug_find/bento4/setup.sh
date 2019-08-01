#!/bin/bash

prog_name="bento4"
declare -a directories
directories=(
 v1.4.2-584
 v1.4.2-586
 v1.4.2-587
 v1.4.2-588
 v1.4.2-589
 v1.4.2-590
 v1.4.2-591
 v1.4.2-592
 v1.4.2-593
 v1.4.2-594
 v1.4.3-595
 v1.4.3-596
 v1.4.3-597
 v1.4.3-598
 v1.4.3-599
 v1.4.3-600
 v1.4.3-601
 v1.4.3-602
 v1.4.3-603
 v1.4.3-604
 v1.4.3-605
 v1.4.3-606
 v1.4.3-607
 v1.4.3-608
 v1.5.0-609
 v1.5.0-610
 v1.5.0-611
 v1.5.0-612
 v1.5.0-613
 v1.5.0-614
 v1.5.0-615
 v1.5.0-616
 v1.5.0-617
 v1.5.0-618
 v1.5.0-619
 v1.5.1-620
 v1.5.1-621
 v1.5.1-623
 v1.5.1-624
 v1.5.1-625
 v1.5.1-626
 v1.5.1-627
 v1.5.1-628
)

##############################################

mkdir normal asan-addr asan-mem asan-int asan-undef

pushd $prog_name
for dir in "${directories[@]}";
do
	git checkout "$dir"
	cp -r ../$prog_name ../normal/$dir
	cp -r ../$prog_name ../asan-addr/$dir
	cp -r ../$prog_name ../asan-mem/$dir
	cp -r ../$prog_name ../asan-int/$dir
	cp -r ../$prog_name ../asan-undef/$dir
done
popd


pushd normal
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0" CXXFLAGS="-g -O0"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined"
	popd
done
popd

