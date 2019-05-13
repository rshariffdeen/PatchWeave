FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y lrzip

# poc files
WORKDIR /patchweave
COPY zip /patchweave/poc

# lrzip
WORKDIR /patchweave/lrzip
RUN git clone https://github.com/ckolivas/lrzip
COPY setup.sh      /patchweave/lrzip/setup.sh
COPY experiment.sh /patchweave/lrzip/experiment.sh
RUN  cd /patchweave/lrzip && ./setup.sh