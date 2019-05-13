#!/bin/bash

prog_name="audiofile"
declare -a directories
directories=(
 audiofile-0.2.1
 audiofile-0.2.2
 audiofile-0.2.3
 audiofile-0.2.4
 audiofile-0.2.5
 audiofile-0.2.6
 audiofile-0.2.7
 audiofile-0.3.0
 audiofile-0.3.1
 audiofile-0.3.2
 audiofile-0.3.3
 audiofile-0.3.4
 audiofile-0.3.5
 audiofile-0.3.6
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
	autoreconf -i
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address -Wno-error" CXXFLAGS="-g -O0 -fsanitize=address -Wno-error"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory -Wno-error" CXXFLAGS="-g -O0 -fsanitize=memory -Wno-error"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer -Wno-error" CXXFLAGS="-g -O0 -fsanitize=integer -Wno-error"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined -Wno-error" CXXFLAGS="-g -O0 -fsanitize=undefined -Wno-error"
	popd
done
popd
