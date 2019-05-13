FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y qpdf
RUN apt install -y libjpeg8 libjpeg8-dev libpcre2-dev libpcre2-8-0

# poc files
WORKDIR /patchweave
COPY pdf /patchweave/poc

# qpdf
WORKDIR /patchweave/qpdf
RUN git clone https://github.com/qpdf/qpdf.git
COPY setup.sh      /patchweave/qpdf/setup.sh
COPY experiment.sh /patchweave/qpdf/experiment.sh
RUN  cd /patchweave/qpdf && ./setup.sh