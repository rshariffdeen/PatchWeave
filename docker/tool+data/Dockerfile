FROM rshariffdeen/patchweave:latest
MAINTAINER Ridwan Shariffdeen <ridwan@comp.nus.edu.sg>

RUN mkdir /data

#openjpeg-jasper
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/div-zero-1.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/div-zero-2.sh /data

#jasper-openjpeg
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/div-zero-1.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/div-zero-2.sh /data
