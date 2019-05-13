#!/bin/bash

prog_name="mupdf"
declare -a directories
directories=(
 1.5
 1.6
 1.7
 1.8
 1.9
 1.10
 1.11
 1.11.1
 1.12.0
 1.13.0
 1.14.0
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
	git submodule update --init
	make -j48 XCC=clang XCXX=clang++ XCFLAGS="-g -O0" XCXXFLAGS="-g -O0" HAVE_X11=no HAVE_GLUT=no HAVE_GLFW=no build=release
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	git submodule update --init
	make -j48 XCC=clang XCXX=clang++ XCFLAGS="-g -O0 -fsanitize=address" XCXXFLAGS="-g -O0 -fsanitize=address" XLIBS="-fsanitize=address" HAVE_X11=no HAVE_GLUT=no HAVE_GLFW=no build=release
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	git submodule update --init
	make -j48 XCC=clang XCXX=clang++ XCFLAGS="-g -O0 -fsanitize=memory" XCXXFLAGS="-g -O0 -fsanitize=memory" XLIBS="-fsanitize=memory" HAVE_X11=no HAVE_GLUT=no HAVE_GLFW=no build=release
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	git submodule update --init
	make -j48 XCC=clang XCXX=clang++ XCFLAGS="-g -O0 -fsanitize=integer" XCXXFLAGS="-g -O0 -fsanitize=integer" XLIBS="-fsanitize=integer" HAVE_X11=no HAVE_GLUT=no HAVE_GLFW=no build=release
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	git submodule update --init
	make -j48 XCC=clang XCXX=clang++ XCFLAGS="-g -O0 -fsanitize=undefined" XCXXFLAGS="-g -O0 -fsanitize=undefined" XLIBS="-fsanitize=undefined" HAVE_X11=no HAVE_GLUT=no HAVE_GLFW=no build=release
	popd
done
popd
