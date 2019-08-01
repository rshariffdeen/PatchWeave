FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt install -y autogen pkg-config libflac-dev libflac8 libogg-dev libogg0 libfl-dev

# poc files
WORKDIR /patchweave
COPY multimedia /patchweave/poc

# libsandfile
WORKDIR /patchweave/libsndfile
RUN git clone https://github.com/erikd/libsndfile.git
COPY setup.sh      /patchweave/libsndfile/setup.sh
COPY experiment.sh /patchweave/libsndfile/experiment.sh
RUN  cd /patchweave/libsndfile && ./setup.sh