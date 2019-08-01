FROM rshariffdeen/patchweave:latest
MAINTAINER Ridwan Shariffdeen <ridwan@comp.nus.edu.sg>

RUN mkdir /data

#openjpeg-jasper
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/div-zero-1.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/div-zero-2.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/null-ptr.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/signed-int-overflow.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/unsigned-int-overflow-1.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/unsigned-int-overflow-2.sh /data

#jasper-openjpeg
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/div-zero-1.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/div-zero-2.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/null-ptr.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/signed-int-overflow.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/unsigned-int-overflow-1.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/unsigned-int-overflow-2.sh /data

