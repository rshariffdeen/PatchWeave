#!/bin/bash

prog_name="binutils-gdb"
declare -a directories
directories=(
 binutils-2_10
 binutils-2_11
 binutils-2_12
 binutils-2_13
 binutils-2_14
 binutils-2_15
 binutils-2_16
 binutils-2_17
 binutils-2_18
 binutils-2_19
 binutils-2_20
 binutils-2_21
 binutils-2_22
 binutils-2_23
 binutils-2_24
 binutils-2_25
 binutils-2_26
 binutils-2_27
 binutils-2_28
 binutils-2_29
 binutils-2_30
 binutils-2_31
 binutils-2_32
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
	export CC=clang CXX=clang++ && ./configure --host=x86_64-unknown-linux-gnu --build=x86_64-unknown-linux-gnu && make -j48 CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	export CC=clang CXX=clang++ && ./configure --host=x86_64-unknown-linux-gnu --build=x86_64-unknown-linux-gnu && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	export CC=clang CXX=clang++ && ./configure --host=x86_64-unknown-linux-gnu --build=x86_64-unknown-linux-gnu && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	export CC=clang CXX=clang++ && ./configure --host=x86_64-unknown-linux-gnu --build=x86_64-unknown-linux-gnu && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	export CC=clang CXX=clang++ && ./configure --host=x86_64-unknown-linux-gnu --build=x86_64-unknown-linux-gnu && make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined"
	popd
done
popd
