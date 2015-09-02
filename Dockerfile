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

# install some haskell packets that we think will be useful
RUN cabal update && \
    cabal install --force-reinstalls \
      array \
      base \
      bytestring \
      containers \
      filepath \
      MissingH \
      parsec \
      QuickCheck \
      regex-compat \
      split \
      syb \
      sexp \
      text-format-simple

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

# install emacs
RUN wget http://proofgeneral.inf.ed.ac.uk/releases/ProofGeneral-4.2.tgz && \
    tar xpzf ProofGeneral-4.2.tgz
ADD emacs /root/.emacs
RUN emacs --batch --script ~/.emacs

# add Makefile
# ADD Makefile /Makefile
# ADD src /x86sem
# RUN make
