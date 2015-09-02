BUILD=build
SRC=.

.PHONY: main clean

main:
	mkdir $(BUILD) 2>/dev/null || true
	find $(SRC) -path ./$(BUILD) -prune -o -name '*.v' -print | xargs cp -a --parents -t $(BUILD)
	cd $(BUILD); find . -name '*.v' | xargs coq_makefile -R $(SRC) "Main" -I /CPUmodels/x86model/Model -o Makefile; cd -
	make -j4 -C$(BUILD)
	# cp Test/header.rkt $(BUILD)/bgpv.rkt
	# tail -n +4 $(BUILD)/bgpv.scm >> $(BUILD)/bgpv.rkt
	# sed -i.bak "s/(define __ (lambda (_) __))/(define __ 'unused)/g" $(BUILD)/bgpv.rkt

clean:
	rm -r $(BUILD)
