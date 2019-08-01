#!/bin/bash

prog_name="libtiff"
declare -a directories
directories=(
  Release-v3-5-4
  Release-v3-5-5
  Release-v3-5-7
  Release-v3-6-0
  Release-v3-6-1
  Release-v3-7-1
  Release-v3-7-2
  Release-v3-7-3
  Release-v3-7-4
  Release-v3-8-0
  Release-v3-8-1
  Release-v3-8-2
  Release-v3-9-0
  Release-v3-9-1
  Release-v3-9-2
  Release-v3-9-3
  Release-v3-9-4
  Release-v3-9-5
  Release-v3-9-6
  Release-v3-9-7
  Release-v4-0-0
  Release-v4-0-1
  Release-v4-0-2
  Release-v4-0-3
  Release-v4-0-4
  Release-v4-0-5
  Release-v4-0-6
  Release-v4-0-7
  Release-v4-0-8
  Release-v4-0-9
  v4.0.10
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
	yes | ./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fPIC" CXXFLAGS="-g -O0 -fPIC"
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
	yes | ./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address -fPIC" CXXFLAGS="-g -O0 -fsanitize=address -fPIC"
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
	yes | ./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory -fPIC" CXXFLAGS="-g -O0 -fsanitize=memory -fPIC"
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
	yes | ./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer -fPIC" CXXFLAGS="-g -O0 -fsanitize=integer -fPIC"
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
	yes | ./configure
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined -fPIC" CXXFLAGS="-g -O0 -fsanitize=undefined -fPIC"
	popd
done
popd
