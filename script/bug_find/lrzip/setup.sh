#!/bin/bash

# v0.45
# v0.46
# v0.47
# v0.5
# v0.5.1
# v0.5.2
# v0.520
# v0.530
# v0.540
# v0.541
# v0.542
# v0.543
# v0.544
# v0.550
# v0.551
# v0.552
# v0.560
# v0.570
# v0.571

prog_name="lrzip"
declare -a directories
directories=(
 v0.600
 v0.601
 v0.602
 v0.603
 v0.604
 v0.605
 v0.606
 v0.607
 v0.608
 v0.610
 v0.611
 v0.612
 v0.613
 v0.614
 v0.615
 v0.616
 v0.620
 v0.621
 v0.630
 v0.631
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
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined"
	popd
done
popd