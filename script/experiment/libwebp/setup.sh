#!/bin/bash

prog_name="libwebp"
declare -a directories
directories=(
  0.2.0
  0.3.0
  0.4.1
  0.4.2
  0.4.3
  0.4.4
  0.5.0
  0.5.1
  0.5.2
  0.6.0
  0.6.1
  1.0.0
  1.0.1
  1.0.2
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
	if [ -f CMakelist.txt ]; then
		export CC=clang CXX=clang++ && cmake .
   	else
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	fi
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fPIC" CXXFLAGS="-g -O0 -fPIC" LDFLAGS="-lpthread"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f CMakelist.txt ]; then
		export CC=clang CXX=clang++ && cmake .
   	else
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	fi
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fPIC -fsanitize=address" CXXFLAGS="-g -O0 -fPIC -fsanitize=address" LDFLAGS="-lpthread -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f CMakelist.txt ]; then
		export CC=clang CXX=clang++ && cmake .
   	else
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	fi
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fPIC -fsanitize=memory" CXXFLAGS="-g -O0 -fPIC -fsanitize=memory" LDFLAGS="-lpthread -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f CMakelist.txt ]; then
		export CC=clang CXX=clang++ && cmake .
   	else
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	fi
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fPIC -fsanitize=integer" CXXFLAGS="-g -O0 -fPIC -fsanitize=integer" LDFLAGS="-lpthread -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f CMakelist.txt ]; then
		export CC=clang CXX=clang++ && cmake .
   	else
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	fi
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fPIC -fsanitize=undefined" CXXFLAGS="-g -O0 -fPIC -fsanitize=undefined" LDFLAGS="-lpthread -fsanitize=undefined"
	popd
done
popd
