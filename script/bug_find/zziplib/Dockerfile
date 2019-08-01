FROM ase19/baseimage

RUN apt update --fix-missing
RUN apt build-dep -y zziplib

# poc files
WORKDIR /patchweave
COPY zip /patchweave/poc

# zziplib
WORKDIR /patchweave/zziplib
RUN git clone https://github.com/gdraheim/zziplib
COPY setup.sh      /patchweave/zziplib/setup.sh
COPY experiment.sh /patchweave/zziplib/experiment.sh
RUN  cd /patchweave/zziplib && ./setup.sh
