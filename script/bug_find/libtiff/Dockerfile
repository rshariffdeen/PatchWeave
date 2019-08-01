FROM ubuntu:16.04

RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-updates main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-security main restricted universe multiverse " >> /etc/apt/sources.list
RUN apt update --fix-missing
RUN apt install -y vim tree
RUN apt install -y libtool automake cmake make clang git subversion mercurial
RUN apt build-dep -y libtiff5

# poc files
WORKDIR /patchweave
COPY images /patchweave/poc

# libtiff
WORKDIR /patchweave/libtiff
RUN git clone https://gitlab.com/libtiff/libtiff.git
COPY setup.sh      /patchweave/libtiff/setup.sh
COPY experiment.sh /patchweave/libtiff/experiment.sh
RUN  cd /patchweave/libtiff && ./setup.sh
