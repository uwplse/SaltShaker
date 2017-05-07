SaltShaker is a solver-aided tool that checks, for all possible machine states, that an x86 instruction executed by [RockSalt’s Coq x86 semantics][rocksalt] behaves according to its instruction specifications extracted from [STOKE][stoke]. SaltShaker verified the RockSalt semantics of over 15,000 instruction instantiations in under 2h, found 7 bugs in RockSalt, and found 1 bug in STOKE. We reported these bugs, and they were subsequently fixed by the respective developers.

[stoke]: http://stoke.stanford.edu/
[rocksalt]: https://github.com/gangtan/CPUmodels

Running
=======

Checkout the project with:

    git clone --recursive git@github.com:uwplse/SaltShaker

Build with: 

    docker build -t x86sem .

Verify a couple of instruction variants with:

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

