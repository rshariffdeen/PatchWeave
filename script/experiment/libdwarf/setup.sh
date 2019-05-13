#!/bin/bash

# 20110605
# 20110607
# 20110612
# 20110908
# 20111009
# 20111030
# 20111214
# 20120410
# 20121127
# 20121130
# 20130125
# 20130126
# 20130207
# 20130729

prog_name="libdwarf"
declare -a directories
directories=(
 20140131
 20140208
 20140413
 20140519
 20140805
 20150112
 20150115
 20150310
 20150507
 20150913
 20150915
 20151114
 20160116
 20160507
 20160613
 20160923
 20160929
 20161001
 20161021
 20161124
 20170416
 20170709
 20180129
 20180527
 20180723
 20180724
 20180809
 20181024
 20190104
 20190110
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
	if [ -f CMakeLists.txt ]; then
	export CC=clang CXX=clang++ && mkdir build_dir && cd build_dir && cmake .. && make -j48 CFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf -I../libdwarf" CXXFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf -I../libdwarf"
	cd ..
	fi

	if [ ! -f build_dir/dwarfdump/dwarfdump ] ; then
	export CC=clang CXX=clang++ && ./configure --disable-static && make -j48 CFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf -I../libdwarf" CXXFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf -I../libdwarf"
	fi
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f CMakeLists.txt ]; then
	export CC=clang CXX=clang++ && mkdir build_dir && cd build_dir && cmake .. && make -j48 CFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf -I../libdwarf -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf -I../libdwarf -fsanitize=address"
	cd ..
	fi

	if [ ! -f build_dir/dwarfdump/dwarfdump ] ; then
	export CC=clang CXX=clang++ && ./configure --disable-static && make -j48 CFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=address"
	fi
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f CMakeLists.txt ]; then
	export CC=clang CXX=clang++ && mkdir build_dir && cd build_dir && cmake .. && make -j48 CFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf -I../libdwarf -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=memory"
	cd ..
	fi

	if [ ! -f build_dir/dwarfdump/dwarfdump ] ; then
	export CC=clang CXX=clang++ && ./configure --disable-static && make -j48 CFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf  -I../libdwarf  -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=memory"
	fi
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f CMakeLists.txt ]; then
	export CC=clang CXX=clang++ && mkdir build_dir && cd build_dir && cmake .. && make -j48 CFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error   -fPIC -I. -Ilibdwarf  -I../libdwarf  -fsanitize=integer"
	cd ..
	fi

	if [ ! -f build_dir/dwarfdump/dwarfdump ] ; then
	export CC=clang CXX=clang++ && ./configure --disable-static && make -j48 CFLAGS="-g -O0 -Wno-error  -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error  -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=integer"
	fi
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	if [ -f CMakeLists.txt ]; then
	export CC=clang CXX=clang++ && mkdir build_dir && cd build_dir && cmake .. && make -j48 CFLAGS="-g -O0 -Wno-error  -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error  -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=undefined"
	cd ..
	fi

	if [ ! -f build_dir/dwarfdump/dwarfdump ] ; then
	export CC=clang CXX=clang++ && ./configure --disable-static && make -j48 CFLAGS="-g -O0 -Wno-error -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error  -fPIC -I. -Ilibdwarf  -I../libdwarf -fsanitize=undefined"
	fi
	popd
done
popd
