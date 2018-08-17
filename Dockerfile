FROM ubuntu:trusty-20180712

ENV LANG C.UTF-8
ENV LC_ALL C.UTF-8

RUN apt-get update
RUN DEBIAN_FRONTEND=noninteractive apt-get install -y \
    ghc cabal-install libreadline-dev
RUN cabal update
RUN cabal install --flags=readline --global alms

# ADD https://github.com/tov/alms/archive/docker.tar.gz /
# RUN tar zxf docker.tar.gz
# RUN mv alms-docker alms

# WORKDIR /alms
# RUN cabal install 'fgl>=5' 'HUnit>=1.2' --global
# RUN cabal configure --verbose=3 --flags=readline --global
# RUN cabal install --flags=readline --global

CMD ["/bin/bash"]
