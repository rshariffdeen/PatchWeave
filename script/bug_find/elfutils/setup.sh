#!/bin/bash

# elfutils-0.120
# elfutils-0.121
# elfutils-0.122
# elfutils-0.123
# elfutils-0.124
# elfutils-0.125
# elfutils-0.126
# elfutils-0.127
# elfutils-0.128
# elfutils-0.129
# elfutils-0.130
# elfutils-0.131
# elfutils-0.132
# elfutils-0.133
# elfutils-0.134
# elfutils-0.135
# elfutils-0.136
# elfutils-0.137
# elfutils-0.138
# elfutils-0.139
# elfutils-0.140
# elfutils-0.141
# elfutils-0.142
# elfutils-0.143
# elfutils-0.144
# elfutils-0.145
# elfutils-0.146
# elfutils-0.147
# elfutils-0.148
# elfutils-0.149
# elfutils-0.150
# elfutils-0.151
# elfutils-0.152
# elfutils-0.153
# elfutils-0.154
# elfutils-0.155
# elfutils-0.156
# elfutils-0.157
# elfutils-0.158
# elfutils-0.159
# elfutils-0.160
# elfutils-0.161
# elfutils-0.162
# elfutils-0.163
# elfutils-0.164
# elfutils-0.165
# elfutils-0.166
# elfutils-0.167
# elfutils-0.168
# elfutils-0.169
# elfutils-0.170
# elfutils-0.171
# elfutils-0.172
# elfutils-0.173
# elfutils-0.174
# elfutils-0.175

prog_name="elfutils"
declare -a directories
directories=(
 elfutils-0.176
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
	autoreconf -i && ./configure --enable-maintainer-mode && make -j40 && make clean && make -j40 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error" CXXFLAGS="-g -O0 -Wno-error"
	popd
done
popd


pushd asan-addr
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i && ./configure --enable-maintainer-mode && make -j40 && make clean && make -j40 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error -fsanitize=address" CXXFLAGS="-g -O0 -Wno-error -fsanitize=address"
	popd
done
popd


pushd asan-mem
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i && ./configure --enable-maintainer-mode && make -j40 && make clean && make -j40 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error -fsanitize=memory" CXXFLAGS="-g -O0 -Wno-error -fsanitize=memory"
	popd
done
popd


pushd asan-int
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i && ./configure --enable-maintainer-mode && make -j40 && make clean && make -j40 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error -fsanitize=integer" CXXFLAGS="-g -O0 -Wno-error -fsanitize=integer"
	popd
done
popd


pushd asan-undef
for dir in "${directories[@]}";
do
	pushd $dir
	autoreconf -i && ./configure --enable-maintainer-mode && make -j40 && make clean && make -j40 CC=clang CXX=clang++ CFLAGS="-g -O0 -Wno-error -fsanitize=undefined" CXXFLAGS="-g -O0 -Wno-error -fsanitize=undefined"
	popd
done
popd
