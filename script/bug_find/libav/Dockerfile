FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt install -y yasm pkg-config ffmpeg libavutil-dev libavformat-dev libavfilter-dev libavdevice-dev libavcodec-dev

# poc files
WORKDIR /patchweave
COPY multimedia /patchweave/poc

# libav
WORKDIR /patchweave/libav
RUN git clone https://github.com/libav/libav.git
COPY setup.sh      /patchweave/libav/setup.sh
COPY experiment.sh /patchweave/libav/experiment.sh
RUN  cd /patchweave/libav && ./setup.sh
