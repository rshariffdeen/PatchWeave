#!/bin/bash

#  v9.15
#  v9.15.1
#  v9.16
#  v9.17
#  v9.18
#  v9.19
#  v9.20
#  v9.21
prog_name="libav"
declare -a directories
directories=(
  v10
  v10.1
  v10.2
  v10.3
  v10.4
  v10.5
  v10.6
  v10.7
  v11
  v11.1
  v11.2
  v11.3
  v11.4
  v11.5
  v11.6
  v11.7
  v11.8
  v11.9
  v11.10
  v11.11
  v12
  v12.1
  v12.3
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
	./configure --cc=clang --extra-cflags="-O0 -static -g"
	make -j48
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --cc=clang --extra-cflags="-O0 -static -g -fsanitize=address" --extra-ldflags="-fsanitize=address"
	make -j48
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --cc=clang --extra-cflags="-O0 -static -g -fsanitize=memory" --extra-ldflags="-fsanitize=memory"
	make -j48
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --cc=clang --extra-cflags="-O0 -static -g -fsanitize=integer" --extra-ldflags="-fsanitize=integer"
	make -j48
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./configure --cc=clang --extra-cflags="-O0 -static -g -fsanitize=undefined" --extra-ldflags="-fsanitize=undefined"
	make -j48
	popd
done
popd

