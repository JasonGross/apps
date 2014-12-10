OCAMLFIND = ocamlfind
OCAMLPKGS = extlib netclient equeue-ssl
MYOCAMLLIBS = $(shell $(OCAMLFIND) query -i-format -recursive $(OCAMLPKGS))

.PHONY: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

-include Makefile.coq

Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject $(MYOCAMLLIBS) -o Makefile.coq


all: pwmgr
ExamplePwMgr.mli ExamplePwMgr.ml ExamplePwMgrRuntime.ml.d: ExamplePwMgr.vo
pwmgr: big.cmx Runtime.cmx ExamplePwMgr.cmx ExamplePwMgrRuntime.cmx
	$(OCAMLFIND) $(CAMLOPTLINK) -linkpkg $(OCAMLPKGS:%=-package %) nums.cmxa $(ZDEBUG) -o $@ $^

clean: my-clean
my-clean:
	rm -f ExamplePwMgr.ml ExamplePwMgr.mli pwmgr
