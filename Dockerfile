FROM ubuntu:trusty-20180712

RUN apt-get update
RUN apt-get install ghc cabal-install libreadline-dev git
RUN cabal update

RUN git clone https://github.com/tov/alms /alms
WORKDIR /alms
RUN git checkout ghc-7.6.3
RUN cabal configure --flags=readline
RUN cabal build
RUN cabal install
