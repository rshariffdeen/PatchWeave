FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y elfutils

# poc files
WORKDIR /patchweave
COPY elf /patchweave/elf

# elfutils
WORKDIR /patchweave/elfutils
RUN git clone git://sourceware.org/git/elfutils.git
COPY setup.sh      /patchweave/elfutils/setup.sh
COPY experiment.sh /patchweave/elfutils/experiment.sh
RUN  cd /patchweave/elfutils && ./setup.sh