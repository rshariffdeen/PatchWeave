#!/bin/bash

prog_name="graphicsmagick"
declare -a directories
directories=(
  GraphicsMagick-1_3_18
  GraphicsMagick-1_3_19
  GraphicsMagick-1_3_20
  GraphicsMagick-1_3_21
  GraphicsMagick-1_3_22
  GraphicsMagick-1_3_23
  GraphicsMagick-1_3_24
  GraphicsMagick-1_3_25
  GraphicsMagick-1_3_26
  GraphicsMagick-1_3_27
  GraphicsMagick-1_3_28
  GraphicsMagick-1_3_29
  GraphicsMagick-1_3_30
  GraphicsMagick-1_3_31
)

##############################################

mkdir normal asan-addr asan-mem asan-int asan-undef

pushd $prog_name
for dir in "${directories[@]}";
do
	hg up "$dir"
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
	./configure CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0" CXXFLAGS="-g -O0"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./configure CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./configure CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./configure CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./configure CC=clang CXX=clang++
	make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined"
	popd
done
popd
