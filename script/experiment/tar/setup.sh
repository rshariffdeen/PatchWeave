#!/bin/bash

# release_1_14
# release_1_15
# release_1_15_1
# release_1_16
# release_1_16_1
# release_1_17
# release_1_18
# release_1_19
# release_1_20
# release_1_21
# release_1_22
# release_1_23
# release_1_24
# release_1_25
# release_1_26
# release_1_27
# release_1_27_1
# release_1_28

prog_name="tar"
declare -a directories
directories=(
 release_1_29
 release_1_30
 release_1_31
 release_1_32
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
