FROM ubuntu:16.04

RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-updates main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-security main restricted universe multiverse " >> /etc/apt/sources.list
RUN apt update --fix-missing
RUN apt install -y vim tree
RUN apt install -y libtool automake cmake make clang git subversion mercurial
RUN apt build-dep -y graphicsmagick

# poc files
WORKDIR /patchweave
COPY images /patchweave/poc

# graphicsmagick
WORKDIR /patchweave/graphicsmagick
RUN hg clone http://hg.code.sf.net/p/graphicsmagick/code graphicsmagick
COPY setup.sh      /patchweave/graphicsmagick/setup.sh
COPY experiment.sh /patchweave/graphicsmagick/experiment.sh
RUN  cd /patchweave/graphicsmagick && ./setup.sh