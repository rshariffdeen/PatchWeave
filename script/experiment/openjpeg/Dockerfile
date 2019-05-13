FROM ubuntu:16.04

RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-updates main restricted universe multiverse " >> /etc/apt/sources.list
RUN echo "deb-src http://sg.archive.ubuntu.com/ubuntu/ xenial-security main restricted universe multiverse " >> /etc/apt/sources.list
RUN apt update --fix-missing
RUN apt install -y vim tree
RUN apt install -y libtool automake make cmake clang git subversion mercurial

# poc files
WORKDIR /patchweave
COPY images /patchweave/poc

# openjpeg
WORKDIR /patchweave/openjpeg
RUN git clone https://github.com/uclouvain/openjpeg.git
COPY setup.sh      /patchweave/openjpeg/setup.sh
COPY experiment.sh /patchweave/openjpeg/experiment.sh
RUN  cd /patchweave/openjpeg && ./setup.sh
