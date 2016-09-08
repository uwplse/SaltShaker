FROM ubuntu:14.04.2
MAINTAINER Konstantin Weitz <konstantin.weitz@gmail.com>

RUN apt-get update && \
    apt-get install -y \
      binutils \
      camlp5 \
      curl \
      default-jre \
      emacs24-nox \
      git \
      g++ \
      haskell-platform \
      libpcre-ocaml-dev \
      libpcre3-dev \
      libreadline-dev \
      libz-dev \
      make \
      pkg-config \
      python \
      python-pip \
      python-yaml \
      vim \
      wget

# install z3
RUN git clone https://github.com/Z3Prover/z3.git && \
    cd z3; python scripts/mk_make.py && \
           cd build; make; make install

# install racket
RUN wget http://mirror.racket-lang.org/installers/6.1.1/racket-6.1.1-x86_64-linux-ubuntu-precise.sh -O install.sh && \
    chmod +x install.sh && \
    ./install.sh --in-place --create-links /usr --dest /usr/racket && \
    rm install.sh

# install rosette
RUN git clone https://github.com/emina/rosette.git && \
    cd rosette; raco link rosette && \
                raco setup -l rosette && \
                ln -s /usr/bin/z3 bin/

# install smten
ENV PATH ~/.cabal/bin:$PATH
RUN mkdir smten && cd smten && \
    cabal update && \
    wget https://github.com/ruhler/smten/releases/download/v4.1.0.0/smten-4.1.0.0.tar.gz && \
    wget https://github.com/ruhler/smten/releases/download/v4.1.0.0/smten-base-4.1.0.0.tar.gz && \
    wget https://github.com/ruhler/smten/releases/download/v4.1.0.0/smten-lib-4.1.0.0.tar.gz && \
    wget https://github.com/ruhler/smten/releases/download/v4.1.0.0/smten-minisat-4.1.0.0.tar.gz && \
    tar -xf smten-4.1.0.0.tar.gz && cd smten-4.1.0.0 && cabal install && cd - && \
    tar -xf smten-base-4.1.0.0.tar.gz && cd smten-base-4.1.0.0 && cabal install && cd - && \
    tar -xf smten-lib-4.1.0.0.tar.gz && cd smten-lib-4.1.0.0 && cabal install && cd - && \
    tar -xf smten-minisat-4.1.0.0.tar.gz && cd smten-minisat-4.1.0.0 && cabal install && cd -

# install coq
RUN curl -O https://coq.inria.fr/distrib/8.4pl3/files/coq-8.4pl3.tar.gz && \
    tar -xvf coq-8.4pl3.tar.gz && \
    cd coq-8.4pl3; ./configure \
                     -bindir /usr/local/bin \
                     -libdir /usr/local/lib/coq \
                     -configdir /etc/xdg/coq \
                     -datadir /usr/local/share/coq \
                     -mandir /usr/local/share/man \
                     -docdir /usr/local/share/doc/coq \
                     -emacs /usr/local/share/emacs/site-lisp \
                     -coqdocdir /usr/local/share/texmf/tex/latex/misc && \
                   make -j4; make install

# install x86 semantics
ADD CPUmodels /CPUmodels
RUN cd /CPUmodels/x86model/Model/flocq-2.1.0; ./configure; make -j4; make install
RUN cd /CPUmodels/x86model/Model; make -j4
