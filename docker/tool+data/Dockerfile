FROM rshariffdeen/patchweave:latest
MAINTAINER Ridwan Shariffdeen <ridwan@comp.nus.edu.sg>

RUN mkdir /data
RUN cd /patchweave && git pull origin

RUN apt install -y \
    bison

#openjpeg-jasper
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/div-zero-1.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/div-zero-2.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/null-ptr.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/signed-int-overflow.sh /data
#RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-jasper/unsigned-int-overflow.sh /data


#jasper-openjpeg
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/div-zero-1.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/div-zero-2.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/null-ptr.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/signed-int-overflow.sh /data
RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/unsigned-int-overflow-1.sh /data
#RUN bash /patchweave/experiments/scripts/cross-program/jasper-openjpeg/unsigned-int-overflow-2.sh /data

#openjpeg-libwebp
RUN bash /patchweave/experiments/scripts/cross-program/openjpeg-libwebp/signed-int-overflow.sh /data

#jasper-libwebp
RUN bash /patchweave/experiments/scripts/cross-program/jasper-libwebp/shift-overflow.sh /data

#libwebp-jasper
#RUN bash /patchweave/experiments/scripts/cross-program/libwebp-jasper/shift-overflow.sh /data

#jasper-libtiff
#RUN bash /patchweave/experiments/scripts/cross-program/jasper-libtiff/memory-write-error.sh /data

#libtiff-jasper
RUN bash /patchweave/experiments/scripts/cross-program/libtiff-jasper/memory-write-error.sh /data

# jasper  backporting
RUN bash /patchweave/experiments/scripts/backporting/jasper/int-overflow.sh /data

# libtiff backporting
#RUN bash /patchweave/experiments/scripts/backporting/libtiff/heap-buffer-overflow.sh /data

# libming backporting
RUN bash /patchweave/experiments/scripts/backporting/libming/div-zero.sh /data
RUN bash /patchweave/experiments/scripts/backporting/libming/negative-shift.sh /data

# libzip backporting
RUN bash /patchweave/experiments/scripts/backporting/libzip/memory-error.sh /data
RUN bash /patchweave/experiments/scripts/backporting/libzip/use-after-free.sh /data