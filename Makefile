MODULES    := Process Refinement ModelCheck Examples SecurityExamples PiCalculus PiCalculus2 FunctionApp
VS         := $(MODULES:%=%.v)

.PHONY: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile $(VS) -R . Apps -o Makefile.coq

-include Makefile.coq
