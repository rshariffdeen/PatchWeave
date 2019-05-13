FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y libarchive
RUN apt install -y bison liblz4-dev libssl-dev

# poc files
WORKDIR /patchweave
COPY zip /patchweave/poc

# libarchive
WORKDIR /patchweave/libarchive
RUN git clone https://github.com/libarchive/libarchive
COPY setup.sh      /patchweave/libarchive/setup.sh
COPY experiment.sh /patchweave/libarchive/experiment.sh
RUN  cd /patchweave/libarchive && ./setup.sh