FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y audiofile
RUN apt install -y asciidoc libtool-bin

# poc files
WORKDIR /patchweave
COPY multimedia /patchweave/poc

# audiofile
WORKDIR /patchweave/audiofile
RUN git clone https://github.com/mpruett/audiofile.git
COPY setup.sh      /patchweave/audiofile/setup.sh
COPY experiment.sh /patchweave/audiofile/experiment.sh
RUN  cd /patchweave/audiofile && ./setup.sh