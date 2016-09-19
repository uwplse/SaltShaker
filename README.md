git submodule init
git submodule update

Build Environment

    docker build -t x86sem .

Run Environment
    
    docker rm -f x86sem; docker run --name x86sem -v $(pwd)/src:/src/extract -v $(pwd)/CPUmodels:/CPUmodels -ti x86sem

Build Project

    cd /CPUmodels/x86model/Model/flocq-2.1.0; ./configure; make -j4; make install
    cd /CPUmodels/x86model/Model; make -j4
    make -C /src/extract

Develop with emacs locally

    emacs /docker:x86sem:/src/extract/coq/X86.v

Develop with emacs remotely

    emacs "/ssh:user@machine|docker:x86sem:/src/extract/coq/X86.v"

Remove all old docker containers with:

    docker rm -f $(docker ps -aq)


Currently, adding all combincations of 0 and 300 takes about 1min to find the
bug:

    (Some (Pair (Pair 
      (Zpos (XO (XO (XI (XI (XO (XI (XO (XO (XH))))))))))    ; 300
      (Zpos (XO (XO (XI (XI (XO (XI (XO (XO (XH)))))))))))   ; 300
      (Inr (Zpos (XO (XO (XO (XI (XI (XO (XH)))))))))))      ; 88 (512+88 = 600)

    real    1m12.140s
    user    1m11.948s
    sys 0m0.168s


Runtime in the list monad (not rosette):

inputs                           |  runtime
---------------------------------+------------
(p `(S ,`(S ,`(S ,`(S ,`(O)))))) |  2m39.229s 
(p `(S ,`(S ,`(S ,`(O)))))       |  0m19.035s
(p `(S ,`(S ,`(O))))             |  0m02.371s
(p `(S ,`(O)))                   |          ?

Runtime in rosette:

inputs                           |  runtime
---------------------------------+------------
(p `(S ,`(S ,`(S ,`(S ,`(O)))))) |          ?
(p `(S ,`(S ,`(S ,`(O)))))       | 69m40.698s
(p `(S ,`(S ,`(O))))             |  1m16.316s
(p `(S ,`(O)))                   |  0m04.389s

