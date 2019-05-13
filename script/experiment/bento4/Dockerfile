FROM ase19/baseimage

RUN apt update --fix-missing
#RUN apt install -y xxx

# poc files
WORKDIR /patchweave
COPY multimedia /patchweave/poc

# bento4
WORKDIR /patchweave/bento4
RUN git clone https://github.com/axiomatic-systems/Bento4.git bento4
COPY setup.sh      /patchweave/bento4/setup.sh
COPY experiment.sh /patchweave/bento4/experiment.sh
RUN  cd /patchweave/bento4 && ./setup.sh