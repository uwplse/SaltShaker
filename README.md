Running
=======

Checkout the project with:

    git clone --recursive git@github.com:uwplse/x86semantics
    cd x86semantics/lib; git clone git@github.com:konne88/stoke

Build with: 

    docker build -t x86sem .

Run with:

    docker run x86sem

Development
===========

Run development environment console:
    
    docker rm -f x86sem; docker run --name x86sem -v $(pwd):/x86sem --entrypoint /bin/bash -ti x86sem

Build project in development environment console:
    
    make -C /src

Connect emacs to development environment locally:

    emacs /docker:x86sem:/src/coq/Compare.v

Connect emacs to development environment remotely:

    emacs "/ssh:user@machine|docker:x86sem:/src/coq/Compare.v"

Make sure your emacs has `ProofGeneral` and `docker-tramp` installed, and
`enable-remote-dir-locals` must be set.

