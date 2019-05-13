#!/bin/bash

# v0.13.36
# v0.13.48

prog_name="zziplib"
declare -a directories
directories=(
 v0.13.50
 v0.13.51
 v0.13.52
 v0.13.54
 v0.13.55
 v0.13.56
 v0.13.57
 v0.13.58
 v0.13.59
 v0.13.60
 v0.13.61
 v0.13.62
 v0.13.63
 v0.13.64
 v0.13.65
 v0.13.66
 v0.13.67
 v0.13.68
 v0.13.69
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
	./configure && sed -i 's/--export-dynamic/-rdynamic/' Makefile  && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	./configure && sed -i 's/--export-dynamic/-rdynamic/' Makefile && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	./configure && sed -i 's/--export-dynamic/-rdynamic/' Makefile && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	./configure && sed -i 's/--export-dynamic/-rdynamic/' Makefile && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	./configure && sed -i 's/--export-dynamic/-rdynamic/' Makefile && make -j48 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined"
	popd
done
popd
