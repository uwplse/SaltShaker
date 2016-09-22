.PHONY: main clean

racket/compare.rkt: racket/x86sem.rkt racket/stoke
	raco make racket/compare.rkt
	chmod +x racket/compare.rkt 

clean:
	make -C coq clean
	rm -f coq/Makefile
	rm -f coq/x86sem.scm racket/x86sem.rkt
	rm -rf racket/compiled 
	rm -rf racket/stoke

racket/x86sem.rkt: coq/*.v racket/header.rkt
	cd coq; find . -name '*.v' -exec coq_makefile -R . "Main" -I /CPUmodels/x86model/Model -o Makefile {} +
	make -j4 -Ccoq
	cp racket/header.rkt racket/x86sem.rkt
	tail -n +4 coq/x86sem.scm >> racket/x86sem.rkt
	sed -i.bak "s/(define __ (lambda (_) __))/(define __ 'underscore)/g" racket/x86sem.rkt
	sed -i.bak 's/(error "AXIOM TO BE REALIZED")/void/g' racket/x86sem.rkt
	rm racket/x86sem.rkt.bak

racket/stoke:
	mkdir racket/stoke
	python/instr2racket.py "notl %eax" > racket/stoke/not-eax.rkt
	python/instr2racket.py "andl %ebx, %eax" > racket/stoke/and-eax-ebx.rkt

