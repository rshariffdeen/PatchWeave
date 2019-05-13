#!/bin/bash

#  n3.0
#  n3.0.1
#  n3.0.10
#  n3.0.11
#  n3.0.12
#  n3.0.2
#  n3.0.3
#  n3.0.4
#  n3.0.5
#  n3.0.6
#  n3.0.7
#  n3.0.8
#  n3.0.9
#  n3.1
#  n3.1.1
#  n3.1.10
#  n3.1.11
#  n3.1.2
#  n3.1.3
#  n3.1.4
#  n3.1.5
#  n3.1.6
#  n3.1.7
#  n3.1.8
#  n3.1.9
#  n3.2
#  n3.2.1
#  n3.2.10
#  n3.2.11
#  n3.2.12
#  n3.2.13
#  n3.2.2
#  n3.2.3
#  n3.2.4
#  n3.2.5
#  n3.2.6
#  n3.2.7
#  n3.2.8
#  n3.2.9
#  n3.3
#  n3.3.1
#  n3.3.2
#  n3.3.3
#  n3.3.4
#  n3.3.5
#  n3.3.6
#  n3.3.7
#  n3.3.8
#  n3.3.9
#  n3.4
#  n3.4.1
#  n3.4.2
#  n3.4.3
#  n3.4.4
#  n3.4.5
#  n3.4.6
#  n4.0
#  n4.0.1
#  n4.0.2
#  n4.0.3
#  n4.0.4
#  n4.1
#  n4.1.1
#  n4.1.2
#  n4.1.3

prog_name="ffmpeg"
declare -a directories
directories=(
  9f0077c
  7becc70
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
	./configure --cc=clang --cxx=clang++ --extra-cflags="-O0 -static -g" --extra-cxxflags="-O0 -static -g"
	make -j48
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --cc=clang --cxx=clang++ --extra-cflags="-O0 -static -g -fsanitize=address" --extra-cxxflags="-O0 -static -g -fsanitize=address" --extra-ldflags="-fsanitize=address" && make -j48
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --cc=clang --cxx=clang++ --extra-cflags="-O0 -static -g -fsanitize=memory" --extra-cxxflags="-O0 -static -g -fsanitize=memory" --extra-ldflags="-fsanitize=memory"
	make -j48
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --cc=clang --cxx=clang++ --extra-cflags="-O0 -static -g -fsanitize=integer" --extra-cxxflags="-O0 -static -g -fsanitize=integer" --extra-ldflags="-fsanitize=integer"
	make -j48
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --cc=clang --cxx=clang++ --extra-cflags="-O0 -static -g -fsanitize=undefined" --extra-cxxflags="-O0 -static -g -fsanitize=undefined" --extra-ldflags="-fsanitize=undefined"
	make -j48
	popd
done
popd
