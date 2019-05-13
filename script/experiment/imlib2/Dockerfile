FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y imlib2

# poc files
WORKDIR /patchweave
COPY images /patchweave/poc

# imlib2
WORKDIR /patchweave/imlib2
RUN git clone https://github.com/kkoudev/imlib2.git
COPY setup.sh      /patchweave/imlib2/setup.sh
COPY experiment.sh /patchweave/imlib2/experiment.sh
RUN  cd /patchweave/imlib2 && ./setup.sh