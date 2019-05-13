#!/bin/bash

prog_name="qpdf"
declare -a directories
directories=(
  release-qpdf-5.0.0
  release-qpdf-5.0.1
  release-qpdf-5.1.0
  release-qpdf-5.1.1
  release-qpdf-5.1.2
  release-qpdf-5.1.3
  release-qpdf-5.2.0
  release-qpdf-6.0.0
  release-qpdf-7.0.0
  release-qpdf-7.1.0
  release-qpdf-7.1.1
  release-qpdf-8.0.0
  release-qpdf-8.0.1
  release-qpdf-8.0.2
  release-qpdf-8.1.0
  release-qpdf-8.2.0
  release-qpdf-8.2.1
  release-qpdf-8.3.0
  release-qpdf-8.4.0
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
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0" CXXFLAGS="-g -O0"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./autogen.sh
	export CC=clang CXX=clang++ && ./configure && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined"
	popd
done
popd

