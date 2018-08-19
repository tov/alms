FROM ubuntu:trusty-20180712

ENV LANG C.UTF-8
ENV LC_ALL C.UTF-8

RUN apt-get update
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y \
    ghc cabal-install libreadline-dev make

RUN cabal update
RUN cabal install --global \
    HUnit-1.6.0.0 \
    QuickCheck-2.11.3 \
    array-0.4.0.1 \
    containers-0.5.0.0 \
    directory-1.2.0.1 \
    fgl-5.6.0.0 \
    filepath-1.3.0.1 \
    incremental-sat-solver-0.1.8 \
    mtl-2.2.2 \
    network-2.7.0.1 \
    parsec-3.1.13.0 \
    pretty-1.1.1.0 \
    random-1.1 \
    readline-1.0.3.0 \
    stm-2.4.5.0 \
    syb-0.7 \
    template-haskell-2.8.0.0 \
    transformers-0.5.2.0 \
    tuple-0.3.0.2

ADD https://github.com/tov/alms/archive/v0.6.9.tar.gz /
RUN tar zxf v0.6.9.tar.gz
RUN mv alms-0.6.9 alms

WORKDIR /alms
RUN make FLAGS=readline || make FLAGS=readline

CMD ["/bin/bash"]
