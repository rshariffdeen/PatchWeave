#!/bin/bash

prog_name="imagemagick"
declare -a directories
directories=(
  7.0.1-0
  7.0.1-1
  7.0.1-2
  7.0.1-3
  7.0.1-4
  7.0.1-5
  7.0.1-6
  7.0.1-7
  7.0.1-8
  7.0.1-9
  7.0.1-10
  7.0.2-0
  7.0.2-1
  7.0.2-2
  7.0.2-3
  7.0.2-4
  7.0.2-5
  7.0.2-6
  7.0.2-7
  7.0.2-8
  7.0.2-9
  7.0.2-10
  7.0.3-0
  7.0.3-1
  7.0.3-2
  7.0.3-3
  7.0.3-4
  7.0.3-5
  7.0.3-6
  7.0.3-7
  7.0.3-8
  7.0.3-9
  7.0.3-10
  7.0.4-0
  7.0.4-1
  7.0.4-2
  7.0.4-3
  7.0.4-4
  7.0.4-5
  7.0.4-6
  7.0.4-7
  7.0.4-8
  7.0.4-9
  7.0.4-10
  7.0.5-0
  7.0.5-1
  7.0.5-2
  7.0.5-3
  7.0.5-4
  7.0.5-5
  7.0.5-6
  7.0.5-7
  7.0.5-8
  7.0.5-9
  7.0.5-10
  7.0.6-0
  7.0.6-1
  7.0.6-2
  7.0.6-3
  7.0.6-4
  7.0.6-5
  7.0.6-6
  7.0.6-7
  7.0.6-8
  7.0.6-9
  7.0.7-0
  7.0.7-1
  7.0.7-2
  7.0.7-3
  7.0.7-4
  7.0.7-5
  7.0.7-6
  7.0.7.7
  7.0.7-8
  7.0.7-9
  7.0.7-10
  7.0.7-11
  7.0.7-12
  7.0.7-13
  7.0.7-14
  7.0.7-15
  7.0.7-16
  7.0.7-17
  7.0.7-18
  7.0.7-19
  7.0.7-20
  7.0.7-21
  7.0.7-22
  7.0.7-23
  7.0.7-24
  7.0.7-25
  7.0.7-26
  7.0.7-27
  7.0.7-28
  7.0.7-29
  7.0.7-30
  7.0.7-31
  7.0.7-32
  7.0.7-33
  7.0.7-34
  7.0.7-35
  7.0.7-36
  7.0.7-37
  7.0.7-38
  7.0.7-39
  7.0.8-0
  7.0.8-1
  7.0.8-2
  7.0.8-3
  7.0.8-4
  7.0.8-5
  7.0.8-6
  7.0.8-7
  7.0.8-8
  7.0.8-9
  7.0.8-10
  7.0.8-11
  7.0.8-12
  7.0.8-13
  7.0.8-14
  7.0.8-15
  7.0.8-16
  7.0.8-17
  7.0.8-18
  7.0.8-19
  7.0.8-20
  7.0.8-21
  7.0.8-22
  7.0.8-23
  7.0.8-24
  7.0.8-25
  7.0.8-26
  7.0.8-27
  7.0.8-28
  7.0.8-29
  7.0.8-30
  7.0.8-31
  7.0.8-32
  7.0.8-33
  7.0.8-34
  7.0.8-35
  7.0.8-36
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
	./configure --enable-static CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0" CXXFLAGS="-g -O0"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --enable-static CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --enable-static CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --enable-static CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --enable-static CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined"
	popd
done
popd
