FROM ubuntu:14.04.2
MAINTAINER Konstantin Weitz <konstantin.weitz@gmail.com>

# install basic tools
RUN apt-get update && \
    apt-get install -y \
      binutils \
      curl \
      fish \
      git \
      g++ \
      make \
      python \
      python-pip \
      vim \
      unzip \
      wget

# install z3
RUN git clone https://github.com/Z3Prover/z3.git && \
    cd z3; python scripts/mk_make.py && \
           cd build; make; make install

# install racket
RUN wget http://mirror.racket-lang.org/installers/6.6/racket-6.6-x86_64-linux.sh -O install.sh && \
    chmod +x install.sh && \
    ./install.sh --in-place --create-links /usr --dest /usr/racket && \
    rm install.sh

# install rosette
RUN apt-get update && \
    apt-get install -y \
      libcairo2-dev \
      libpango1.0-dev \
      libjpeg-dev && \
    git clone https://github.com/emina/rosette.git && \
    cd rosette; git checkout 2.2 && \
                raco pkg install

# install opam
RUN wget https://raw.github.com/ocaml/opam/master/shell/opam_installer.sh -O - | sh -s /usr/local/bin && \
    opam init -n --comp=4.01.0
ENV PATH "/root/.opam/4.01.0/bin":$PATH

# install coq
RUN opam install coq.8.5.2

# install stoke dependencies
RUN apt-get update && \
    apt-get install -y software-properties-common apt-transport-https && \
    add-apt-repository -y ppa:ubuntu-toolchain-r/test && \
    apt-get update && \
    apt-get install -y \
      bison ccache cmake doxygen exuberant-ctags flex g++-4.9 g++-multilib \
      gcc-4.9 ghc git libantlr3c-dev libboost-dev libboost-filesystem-dev \
      libboost-thread-dev libcln-dev libghc-regex-compat-dev \
      libghc-regex-tdfa-dev libghc-split-dev libjsoncpp-dev python subversion \
      libiml-dev libgmp-dev libboost-regex-dev && \
    update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-4.9 60 --slave /usr/bin/g++ g++ /usr/bin/g++-4.9
ENV PATH /x86sem/lib/stoke/bin:$PATH

# install CPUModels dependencies
RUN wget https://gforge.inria.fr/frs/download.php/file/36199/flocq-2.5.2.tar.gz && \
    tar -xvf flocq-* && \
    cd flocq-*; ./configure && ./remake && ./remake install

# install space-search
RUN opam update && opam install space-search

ENTRYPOINT /x86sem/test/test.sh

# install
ADD . /x86sem
RUN make -C /x86sem
