FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y binutils

# poc files
WORKDIR /patchweave
COPY elf /patchweave/elf

# binutils-gdb
WORKDIR /patchweave/binutils
RUN git clone git://sourceware.org/git/binutils-gdb.git
COPY setup.sh      /patchweave/binutils/setup.sh
COPY experiment.sh /patchweave/binutils/experiment.sh
RUN  cd /patchweave/binutils && ./setup.sh