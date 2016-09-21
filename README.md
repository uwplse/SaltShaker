Running
=======

Checkout the project with:

    git clone --recursive https://github.com/uwplse/x86semantics

Build with: 

    docker build -t x86sem .

Run with:

    docker run x86sem

Development
===========

Run development environment console:
    
    docker rm -f x86sem; docker run --name x86sem -v $(pwd)/src:/src/extract -v $(pwd)/CPUmodels:/CPUmodels --entrypoint /bin/bash -ti x86sem

Build project in development environment console:

    cd /CPUmodels/x86model/Model/flocq-2.1.0; ./configure; make -j4; make install
    cd /CPUmodels/x86model/Model; make -j4
    make -C /src/extract

Connect emacs to development environment locally:

    emacs /docker:x86sem:/src/extract/coq/X86.v

Connect emacs to development environment remotely:

    emacs "/ssh:user@machine|docker:x86sem:/src/extract/coq/X86.v"

