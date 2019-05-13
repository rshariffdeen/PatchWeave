#!/bin/bash

# v1.3.12
# v1.3.13
# v1.3.14
# v1.4
prog_name="gzip"
declare -a directories
directories=(
 v1.5
 v1.6
 v1.7
 v1.8
 v1.9
 v1.10
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
	./bootstrap
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./bootstrap
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./bootstrap
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./bootstrap
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./bootstrap
	export CC=clang CXX=clang++ && ./configure && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined"
	popd
done
popd
