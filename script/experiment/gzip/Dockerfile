FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y gzip
RUN apt install -y autopoint cvs perl

# poc files
WORKDIR /patchweave
COPY zip /patchweave/poc

# gzip
WORKDIR /patchweave/gzip
RUN git clone git://git.savannah.gnu.org/gzip.git
COPY setup.sh      /patchweave/gzip/setup.sh
COPY experiment.sh /patchweave/gzip/experiment.sh
RUN  cd /patchweave/gzip && ./setup.sh