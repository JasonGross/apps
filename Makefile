OCAMLFIND = ocamlfind
OCAMLPKGS = extlib netclient equeue-ssl
MYOCAMLLIBS = $(shell $(OCAMLFIND) query -i-format -recursive $(OCAMLPKGS))

.PHONY: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

-include Makefile.coq

# we need to hack around https://coq.inria.fr/bugs/show_bug.cgi?id=2950 for Coq 8.4pl4 on Windows
Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject $(MYOCAMLLIBS) | sed s'/ $$(COQLIB)/ "$$(COQLIB)"/g' > Makefile.coq


all: pwmgr
ExamplePwMgr.mli ExamplePwMgr.ml ExamplePwMgrRuntime.ml.d: ExamplePwMgr.vo
pwmgr: big.cmx Runtime.cmx ExamplePwMgr.cmx ExamplePwMgrRuntime.cmx
	$(OCAMLFIND) $(CAMLOPTLINK) -linkpkg $(OCAMLPKGS:%=-package %) nums.cmxa $(ZDEBUG) -o $@ $^

all: pwmgr-ssb
ExamplePwMgrWithSSBFull.mli ExamplePwMgrWithSSBFull.ml ExamplePwMgrWithSSBFullRuntime.ml.d: ExamplePwMgrWithSSBFull.vo
pwmgr-ssb: big.cmx Runtime.cmx ExamplePwMgrWithSSBFull.cmx ExamplePwMgrWithSSBFullRuntime.cmx
	$(OCAMLFIND) $(CAMLOPTLINK) -linkpkg $(OCAMLPKGS:%=-package %) nums.cmxa $(ZDEBUG) -o $@ $^

clean: my-clean
my-clean:
	rm -f ExamplePwMgr.ml ExamplePwMgr.mli pwmgr
	rm -f ExamplePwMgrWithSSBFull.ml ExamplePwMgrWithSSBFull.mli pwmgr-ssb
