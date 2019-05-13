FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y tar
RUN apt install -y autopoint cvs perl

# poc files
WORKDIR /patchweave
COPY zip /patchweave/poc

# tar
WORKDIR /patchweave/tar
RUN git clone git://git.savannah.gnu.org/tar.git
COPY setup.sh      /patchweave/tar/setup.sh
COPY experiment.sh /patchweave/tar/experiment.sh
RUN  cd /patchweave/tar && ./setup.sh
