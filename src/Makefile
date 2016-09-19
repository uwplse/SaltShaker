BUILD=.build
COQ_SRC=coq
RKT_SRC=racket
MAIN=main.rkt

.PHONY: main clean

main: $(BUILD)/x86sem.rkt
	cp $(RKT_SRC)/*.rkt $(BUILD)
	raco make $(BUILD)/$(MAIN)
	chmod +x $(BUILD)/$(MAIN)

clean:
	rm -r $(BUILD)

$(BUILD)/x86sem.rkt: $(COQ_SRC)/*.v $(RKT_SRC)/header.rkt
	mkdir $(BUILD) 2>/dev/null || true
	find $(COQ_SRC) -name '*.v' -exec cp -a --parents -t $(BUILD) {} +
	cd $(BUILD); find . -name '*.v' -exec coq_makefile -R $(COQ_SRC) "Main" -I /CPUmodels/x86model/Model -o Makefile {} +
	make -j4 -C$(BUILD)
	cp $(RKT_SRC)/header.rkt $(BUILD)/x86sem.rkt
	tail -n +4 $(BUILD)/x86sem.scm >> $(BUILD)/x86sem.rkt
	sed -i.bak "s/(define __ (lambda (_) __))/(define __ (void))/g" $(BUILD)/x86sem.rkt
	sed -i.bak 's/(error "AXIOM TO BE REALIZED")/(void)/g' $(BUILD)/x86sem.rkt

