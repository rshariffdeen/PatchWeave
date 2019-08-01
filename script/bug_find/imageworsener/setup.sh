#!/bin/bash

prog_name="imageworsener"
declare -a directories
directories=(
  1.0.0
  1.1.0
  1.2.0
  1.3.0
  1.3.1
  1.3.2
  1.3.3
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
	./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 " CXXFLAGS="-g -O0 "
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i
	./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i
	./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i
	./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i
	./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined"
	popd
done
popd

