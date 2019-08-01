FROM ase19/baseimage

RUN apt update --fix-missing
#RUN apt build-dep -y libdwarf
RUN apt install -y libelf-dev

# poc files
WORKDIR /patchweave
COPY elf /patchweave/elf

# libdwarf
WORKDIR /patchweave/libdwarf
RUN git clone git://git.code.sf.net/p/libdwarf/code libdwarf
COPY setup.sh      /patchweave/libdwarf/setup.sh
COPY experiment.sh /patchweave/libdwarf/experiment.sh
RUN  cd /patchweave/libdwarf && ./setup.sh
