Running
=======

Checkout the project with:

    git clone --recursive git@github.com:uwplse/x86semantics

Build with: 

    docker build -t x86sem .

Run with:

    docker run x86sem

Development
===========

Run development environment console:
    
    docker rm -f x86sem; docker run --name x86sem --entrypoint /bin/bash -v $(pwd):/x86sem -ti x86sem

If you like the `fish` shell (i do) run:

    docker rm -f x86sem; docker run --name x86sem --entrypoint /usr/bin/fish -v (pwd):/x86sem -ti x86sem

Build project in development environment console:
    
    make -C /x86sem

Connect emacs to development environment locally:

    emacs /docker:x86sem:/x86sem/src/coq/Compare.v

Connect emacs to development environment remotely:

    emacs "/ssh:user@machine|docker:x86sem:/x86sem/src/coq/Compare.v"

Make sure your emacs has `ProofGeneral` and `docker-tramp` installed, and
`enable-remote-dir-locals` must be set.

