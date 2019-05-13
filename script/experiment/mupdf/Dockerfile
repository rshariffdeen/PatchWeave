FROM ubuntu:16.04

RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-updates main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-security main restricted universe multiverse " >> /etc/apt/sources.list
RUN apt update --fix-missing
RUN apt install -y vim tree
RUN apt install -y clang libtool automake cmake make clang git subversion mercurial
RUN apt build-dep -y mupdf

# poc files
WORKDIR /patchweave
COPY pdf /patchweave/poc

# mupdf
WORKDIR /patchweave/mupdf
RUN git clone git://git.ghostscript.com/mupdf.git
COPY setup.sh      /patchweave/mupdf/setup.sh
COPY experiment.sh /patchweave/mupdf/experiment.sh
COPY clean.sh /patchweave/mupdf/clean.sh
RUN  cd /patchweave/mupdf && ./setup.sh
