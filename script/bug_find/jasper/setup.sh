#!/bin/bash

prog_name="jasper"
declare -a directories
directories=(
  version-1.900.1
  version-1.900.2
  version-1.900.3
  version-1.900.4
  version-1.900.5
  version-1.900.6
  version-1.900.7
  version-1.900.8
  version-1.900.9
  version-1.900.10
  version-1.900.11
  version-1.900.12
  version-1.900.13
  version-1.900.14
  version-1.900.15
  version-1.900.16
  version-1.900.17
  version-1.900.18
  version-1.900.19
  version-1.900.20
  version-1.900.21
  version-1.900.22
  version-1.900.23
  version-1.900.24
  version-1.900.25
  version-1.900.26
  version-1.900.27
  version-1.900.28
  version-1.900.29
  version-1.900.30
  version-1.900.31
  version-2.0.0
  version-2.0.1
  version-2.0.2
  version-2.0.3
  version-2.0.4
  version-2.0.5
  version-2.0.6
  version-2.0.7
  version-2.0.8
  version-2.0.9
  version-2.0.10
  version-2.0.11
  version-2.0.12
  version-2.0.13
  version-2.0.14
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
	if [ -f configure.ac ] || [ -f configure.in ]; then
		if [ ! -f configure ]; then autoreconf -i; fi
		./configure
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 " CXXFLAGS="-g -O0 "
	else
		pushd build
		cmake ..
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 " CXXFLAGS="-g -O0 "
		popd
	fi
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f configure.ac ] || [ -f configure.in ]; then
		if [ ! -f configure ]; then autoreconf -i; fi
		./configure
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address"
	else
		pushd build
		cmake ..
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address"
		popd
	fi
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f configure.ac ] || [ -f configure.in ]; then
		if [ ! -f configure ]; then autoreconf -i; fi
		./configure
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory"
	else
		pushd build
		cmake ..
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory"
		popd
	fi
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f configure.ac ] || [ -f configure.in ]; then
		if [ ! -f configure ]; then autoreconf -i; fi
		./configure
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer"
	else
		pushd build
		cmake ..
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer"
		popd
	fi
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f configure.ac ] || [ -f configure.in ]; then
		if [ ! -f configure ]; then autoreconf -i; fi
		./configure
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined"
	else
		pushd build
		cmake ..
		make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined"
		popd
	fi
	popd
done
popd
