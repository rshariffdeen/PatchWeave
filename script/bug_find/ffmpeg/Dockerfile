FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y ffmpeg
RUN apt install -y libsdl2-dev

# poc files
WORKDIR /patchweave
COPY multimedia /patchweave/poc

# ffmpeg
WORKDIR /patchweave/ffmpeg
RUN git clone https://github.com/FFmpeg/FFmpeg.git ffmpeg
COPY setup.sh      /patchweave/ffmpeg/setup.sh
COPY experiment.sh /patchweave/ffmpeg/experiment.sh
RUN  cd /patchweave/ffmpeg && ./setup.sh
