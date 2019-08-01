FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y libzip

# poc files
WORKDIR /patchweave
COPY zip /patchweave/poc

# libzip
WORKDIR /patchweave/libzip
RUN git clone https://github.com/nih-at/libzip
COPY setup.sh      /patchweave/libzip/setup.sh
COPY experiment.sh /patchweave/libzip/experiment.sh
RUN  cd /patchweave/libzip && ./setup.sh