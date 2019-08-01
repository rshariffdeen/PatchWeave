# ASE19 Base Image

FROM ubuntu:16.04

RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-updates main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-security main restricted universe multiverse " >> /etc/apt/sources.list
RUN apt update --fix-missing
RUN apt install -y vim tree
RUN apt install -y libtool automake cmake make git subversion mercurial wget

# LLVM
RUN echo "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial main" >> /etc/apt/sources.list
RUN echo "deb-src http://apt.llvm.org/xenial/ llvm-toolchain-xenial main" >> /etc/apt/sources.list
# LLVM 7
RUN echo "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-7 main" >> /etc/apt/sources.list
RUN echo "deb-src http://apt.llvm.org/xenial/ llvm-toolchain-xenial-7 main" >> /etc/apt/sources.list
# LLVM 8
RUN echo "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-8 main" >> /etc/apt/sources.list
RUN echo "deb-src http://apt.llvm.org/xenial/ llvm-toolchain-xenial-8 main" >> /etc/apt/sources.list
RUN wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key|apt-key add -
RUN apt update --fix-missing
RUN apt install -y clang-9
RUN ln -s /usr/bin/clang-9 /usr/bin/clang
RUN ln -s /usr/bin/clang++-9 /usr/bin/clang++
RUN ln -s /usr/bin/clang-cpp-9 /usr/bin/clang-cpp