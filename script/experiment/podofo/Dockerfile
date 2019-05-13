FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt install -y fontconfig zlib1g libpng16-16 libjpeg8 libtiff5 libidn11 libidn2-0-dev libcrypto++ libcrypto++-utils libfreetype6 freetype2-demos
RUN apt install -y libfontconfig1-dev zlib1g-dev libpng-dev libjpeg8-dev libtiff5-dev libidn11-dev libidn2-0-dev libcrypto++-dev libfreetype6-dev libcppunit-dev
RUN apt install -y libunistring0 libunistring-dev libssl-dev

# poc files
WORKDIR /patchweave
COPY pdf /patchweave/poc

# podofo
WORKDIR /patchweave/podofo
COPY podofo_src /patchweave/podofo/podofo
COPY setup.sh      /patchweave/podofo/setup.sh
COPY experiment.sh /patchweave/podofo/experiment.sh
RUN  cd /patchweave/podofo && ./setup.sh
