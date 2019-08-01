#!/bin/bash

# rel-0-8
# rel-0-9
# rel-0-9-1
# rel-0-9-2
# rel-0-9-3
# rel-0-10
# rel-0-10-1
# rel-0-11
# rel-0-11-1
# rel-0-11-2

prog_name="libzip"
declare -a directories
directories=(
 rel-1-0
 rel-1-0-1
 rel-1-1
 rel-1-1-1
 rel-1-1-2
 rel-1-1-3
 rel-1-2-0
 rel-1-3-0
 rel-1-3-1
 rel-1-3-2
 rel-1-4-0
 rel-1-5-0
 rel-1-5-1
 rel-1-5-2
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
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake ../ -DCFLAGS="-g -O0 -Wno-error" -DCXXFLAGS="-g -O0 -Wno-error" && make -j48 CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake ../ -DCFLAGS="-g -O0 -Wno-error -fsanitize=address" -DCXXFLAGS="-g -O0 -Wno-error -fsanitize=address" && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake ../ -DCFLAGS="-g -O0 -Wno-error -fsanitize=memory" -DCXXFLAGS="-g -O0 -Wno-error -fsanitize=memory" && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake ../ -DCFLAGS="-g -O0 -Wno-error -fsanitize=integer" -DCXXFLAGS="-g -O0 -Wno-error -fsanitize=integer" && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	mkdir build && cd build && export CC=clang CXX=clang++ && cmake ../ -DCFLAGS="-g -O0 -Wno-error -fsanitize=undefined" -DCXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined" && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined"
	popd
done
popd
