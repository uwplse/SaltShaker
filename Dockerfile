FROM ubuntu:14.04.2
MAINTAINER Konstantin Weitz <konstantin.weitz@gmail.com>

RUN apt-get update; \
    apt-get install -y \
      binutils \
      default-jre \
      git \
      g++ \
      haskell-platform \
      make \
      python \
      python-pip \
      python-yaml \
      wget

# install z3
RUN git clone https://github.com/Z3Prover/z3.git
RUN cd z3; python scripts/mk_make.py
RUN cd z3/build; make; make install
RUN rm -r z3

# install racket
RUN wget http://mirror.racket-lang.org/installers/6.1.1/racket-6.1.1-x86_64-linux-ubuntu-precise.sh -O install.sh
RUN chmod +x install.sh
RUN ./install.sh --in-place --create-links /usr --dest /usr/racket
RUN rm install.sh

# install rosette
RUN git clone https://github.com/emina/rosette.git
RUN cd rosette; raco link rosette
RUN cd rosette; raco setup -l rosette
RUN ln -s /usr/bin/z3 rosette/bin/

# install some haskell packets that we think will be useful
RUN cabal update; \
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

RUN apt-get update; \
    apt-get install -y \
      binutils \
      camlp5 \
      curl \
      libpcre-ocaml-dev \
      libpcre3-dev \
      libreadline-dev \
      libz-dev \
      make \
      pkg-config \
      vim

# install coq
RUN curl -O https://coq.inria.fr/distrib/8.4pl3/files/coq-8.4pl3.tar.gz
RUN tar -xvf coq-8.4pl3.tar.gz
RUN cd coq-8.4pl3; ./configure \
  -bindir /usr/local/bin \
  -libdir /usr/local/lib/coq \
  -configdir /etc/xdg/coq \
  -datadir /usr/local/share/coq \
  -mandir /usr/local/share/man \
  -docdir /usr/local/share/doc/coq \
  -emacs /usr/local/share/emacs/site-lisp \
  -coqdocdir /usr/local/share/texmf/tex/latex/misc
RUN cd coq-8.4pl3; make -j4; make install

# install x86 semantics
ADD CPUmodels /src/CPUmodels
RUN cd /src/CPUmodels/x86model/Model/flocq-2.1.0; ./configure
RUN cd /src/CPUmodels/x86model/Model/flocq-2.1.0; make -j4
RUN cd /src/CPUmodels/x86model/Model/flocq-2.1.0; make install
RUN cd /src/CPUmodels/x86model/Model; make -j4

# install emacs
RUN apt-get update && apt-get install -y emacs24-nox
RUN wget http://proofgeneral.inf.ed.ac.uk/releases/ProofGeneral-4.2.tgz
RUN tar xpzf ProofGeneral-4.2.tgz
ADD emacs /root/.emacs
RUN emacs --batch --script ~/.emacs
