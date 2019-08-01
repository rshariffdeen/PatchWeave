FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y libwebp

# poc files
WORKDIR /patchweave
COPY images /patchweave/poc

# libwebp
WORKDIR /patchweave/libwebp
RUN git clone https://chromium.googlesource.com/webm/libwebp
COPY setup.sh      /patchweave/libwebp/setup.sh
COPY experiment.sh /patchweave/libwebp/experiment.sh
RUN  cd /patchweave/libwebp && ./setup.sh