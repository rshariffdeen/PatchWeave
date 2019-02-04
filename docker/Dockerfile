FROM ubuntu:16.04
MAINTAINER Ridwan Shariffdeen <ridwan@comp.nus.edu.sg>
RUN apt-get update && apt-get install -y software-properties-common \
    git \
    nano \
    python \
    python-pip \
    wget
RUN wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key| apt-key add -
RUN apt-add-repository "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-7 main"
RUN apt-get update
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y  --no-install-recommends --force-yes \
    clang-7
RUN apt-get install -y \
    cmake
RUN mkdir -p /llvm/llvm-7; git clone http://llvm.org/git/llvm.git /llvm/llvm-7/source; cd /llvm/llvm-7/source; git checkout release_70
RUN apt-get install -y \
    ninja
RUN mkdir /llvm/llvm-7/build; cd /llvm/llvm-7/build; cmake -GNinja /llvm/llvm-7/source -DCMAKE_BUILD_TYPE=Release -DCMAKE_ENABLE_ASSERTIONS=OFF -DLLVM_ENABLE_WERROR=OFF -DLLVM_TARGETS_TO_BUILD=X86 -DCMAKE_CXX_FLAGS="-std=c++11" -DCMAKE_C_COMPILER=clang-7 -DCMAKE_CXX_COMPILER=clang++-7

