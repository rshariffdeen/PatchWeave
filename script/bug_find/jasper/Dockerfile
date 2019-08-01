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

# jasper
WORKDIR /patchweave/jasper
RUN git clone https://github.com/mdadams/jasper
COPY setup.sh      /patchweave/jasper/setup.sh
COPY experiment.sh /patchweave/jasper/experiment.sh
RUN  cd /patchweave/jasper && ./setup.sh
