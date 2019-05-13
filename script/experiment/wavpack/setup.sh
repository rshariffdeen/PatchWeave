#!/bin/bash

prog_name="wavpack"
declare -a directories
directories=(
 4.40.0
 4.41.0
 4.50.0
 4.50.1
 4.60.0
 4.60.1
 4.70.0
 4.75.0
 4.75.2
 4.80.0
 5.0.0
 5.1.0
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
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address -Wno-error" CXXFLAGS="-g -O0 -fsanitize=address -Wno-error"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory -Wno-error" CXXFLAGS="-g -O0 -fsanitize=memory -Wno-error"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer -Wno-error" CXXFLAGS="-g -O0 -fsanitize=integer -Wno-error"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined -Wno-error" CXXFLAGS="-g -O0 -fsanitize=undefined -Wno-error"
	popd
done
popd

