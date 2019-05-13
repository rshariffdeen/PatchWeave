#!/bin/bash

# v1.2.1
# v1.2.2
# v1.3.0

prog_name="imlib2"
declare -a directories
directories=(
 v1.4.0
 v1.4.1
 v1.4.2
 v1.4.3
 v1.4.4
 v1.4.5
 v1.4.6
 v1.4.7
 v1.4.8
 v1.4.9
 v1.4.10
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
	if [ ! -f configure ]; then
	./autogen.sh
	fi
	./configure
	export CC=clang CXX=clang++ && make -j40 CFLAGS="-g -O0" CXXFLAGS="-g -O0" LDFLAGS="-lX11"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	if [ ! -f configure ]; then
	./autogen.sh
	fi
	./configure
	export CC=clang CXX=clang++ && make -j40 CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address" LDFLAGS="-lX11"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	if [ ! -f configure ]; then
	./autogen.sh
	fi
	./configure
	export CC=clang CXX=clang++ && make -j40 CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory" LDFLAGS="-lX11"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	if [ ! -f configure ]; then
	./autogen.sh
	fi
	./configure
	export CC=clang CXX=clang++ && make -j40 CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer" LDFLAGS="-lX11"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	if [ ! -f configure ]; then
	./autogen.sh
	fi
	./configure
	export CC=clang CXX=clang++ && make -j40 CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined" LDFLAGS="-lX11"
	popd
done
popd
