#!/bin/bash

prog_name="libarchive"
declare -a directories
directories=(
 v2.6.0
 v2.6.1
 v2.6.2
 v2.7.0
 v2.7.1
 v2.8.0
 v2.8.1
 v2.8.2
 v2.8.3
 v2.8.4
 v2.8.5
 v3.0.2
 v3.0.3
 v3.0.4
 v3.1.0
 v3.1.1
 v3.1.2
 v3.2.0
 v3.2.1
 v3.2.2
 v3.3.0
 v3.3.1
 v3.3.2
 v3.3.3
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
	if [ -f autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	else if [ -f build/autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./build/autogen.sh && ./configure
	fi
	fi
	make -j48 CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"

	if [ ! -f bsdtar ]; then
		if [ -f CMakeLists.txt ] ; then
			export CC=clang CXX=clang++ && cmake .
			make -j48 CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
		fi
	fi
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	else if [ -f build/autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./build/autogen.sh && ./configure
	fi
	fi
	make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fsanitize=address"

	if [ ! -f bsdtar ]; then
		if [ -f CMakeLists.txt ] ; then
			export CC=clang CXX=clang++ && cmake .
			make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fsanitize=address"
		fi
	fi

	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	else if [ -f build/autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./build/autogen.sh && ./configure
	fi
	fi
	make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fsanitize=memory"

	if [ ! -f bsdtar ]; then
		if [ -f CMakeLists.txt ] ; then
			export CC=clang CXX=clang++ && cmake .
			make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fsanitize=memory"
		fi
	fi
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	else if [ -f build/autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./build/autogen.sh && ./configure
	fi
	fi
	make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error -fsanitize=integer"

	if [ ! -f bsdtar ]; then
		if [ -f CMakeLists.txt ] ; then
			export CC=clang CXX=clang++ && cmake .
			make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error -fsanitize=integer"
		fi
	fi
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./autogen.sh && ./configure
	else if [ -f build/autogen.sh ] ; then
		export CC=clang CXX=clang++ && ./build/autogen.sh && ./configure
	fi
	fi
	make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined"

	if [ ! -f bsdtar ]; then
		if [ -f CMakeLists.txt ] ; then
			export CC=clang CXX=clang++ && cmake .
			make -j48 CFLAGS="-g -O0 -Wno-error -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined"
		fi
	fi
	popd
done
popd
