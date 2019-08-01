FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y wavpack

# poc files
WORKDIR /patchweave
COPY multimedia /patchweave/poc

# wavpack
WORKDIR /patchweave/wavpack
RUN git clone https://github.com/dbry/WavPack.git wavpack
COPY setup.sh      /patchweave/wavpack/setup.sh
COPY experiment.sh /patchweave/wavpack/experiment.sh
RUN  cd /patchweave/wavpack && ./setup.sh