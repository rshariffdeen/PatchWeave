#!/bin/bash

prog_name="podofo"
declare -a directories
directories=(
  podofo-0.9.0
  podofo-0.9.1
  podofo-0.9.2
  podofo-0.9.3
  podofo-0.9.4
  podofo-0.9.5
  podofo-0.9.6
)

# decompress the source code
# git did not work for this program
declare -a src_files
i=0
while read line
do
	src_files[ $i ]="$line"
    (( i++ ))
done < <(ls $prog_name)

pushd $prog_name
for file in "${src_files[@]}";
do
tar xf $file
done
popd

##############################################

mkdir normal asan-addr asan-mem asan-int asan-undef

pushd $prog_name
for dir in "${directories[@]}";
do
	cp -r $dir ../normal/$dir
	cp -r $dir ../asan-addr/$dir
	cp -r $dir ../asan-mem/$dir
	cp -r $dir ../asan-int/$dir
	cp -r $dir ../asan-undef/$dir
done
popd


pushd normal
for dir in "${directories[@]}";
do
	pushd $dir
	export CC=clang CXX=clang++ && mkdir build && cd build && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0" CXXFLAGS="-g -O0"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
    export CC=clang CXX=clang++ && mkdir build && cd build && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=address" CXXFLAGS="-g -O0 -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	export CC=clang CXX=clang++ && mkdir build && cd build && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=memory" CXXFLAGS="-g -O0 -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	export CC=clang CXX=clang++ && mkdir build && cd build && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=integer" CXXFLAGS="-g -O0 -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	export CC=clang CXX=clang++ && mkdir build && cd build && cmake .. && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -fsanitize=undefined" CXXFLAGS="-g -O0 -fsanitize=undefined"
	popd
done
popd
