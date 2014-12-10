OCAMLFIND = ocamlfind
OCAMLPKGS = extlib netclient equeue-ssl
MYOCAMLLIBS = $(shell $(OCAMLFIND) query -i-format -recursive $(OCAMLPKGS))

.PHONY: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

-include Makefile.coq

# we need to hack around https://coq.inria.fr/bugs/show_bug.cgi?id=2950 for Coq 8.4pl4 on Windows
Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject $(MYOCAMLLIBS) -o Makefile.coq.old
	sed s'/ $$(COQLIB)/ "$$(COQLIB)"/g' Makefile.coq.old > Makefile.coq


all: pwmgr

# we paste in .ml.d and .mli.d files that were generated from .vo
# files, because we don't want the clean target to depend on .vo files
ExamplePwMgr.cmo : big.cmo ExamplePwMgr.cmi
ExamplePwMgr.cmx : big.cmx ExamplePwMgr.cmi
ExamplePwMgr.cmi : big.cmo
ExamplePwMgrRuntime.cmo : Runtime.cmo ExamplePwMgr.cmi
ExamplePwMgrRuntime.cmx : Runtime.cmx ExamplePwMgr.cmx

pwmgr: big.cmx Runtime.cmx ExamplePwMgr.cmx ExamplePwMgrRuntime.cmx
	$(OCAMLFIND) $(CAMLOPTLINK) -linkpkg $(OCAMLPKGS:%=-package %) nums.cmxa $(ZDEBUG) -o $@ $^


ExamplePwMgrWithSSBFull.cmo : big.cmo ExamplePwMgrWithSSBFull.cmi
ExamplePwMgrWithSSBFull.cmx : big.cmx ExamplePwMgrWithSSBFull.cmi
ExamplePwMgrWithSSBFull.cmi : big.cmo
ExamplePwMgrWithSSBFullRuntime.cmo : Runtime.cmo ExamplePwMgrWithSSBFull.cmi
ExamplePwMgrWithSSBFullRuntime.cmx : Runtime.cmx ExamplePwMgrWithSSBFull.cmx

ExamplePwMgr.cmi ExamplePwMgrWithSSBFull.cmi: %.cmi: %.vo
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $*.mli

ExamplePwMgr.cmo ExamplePwMgrWithSSBFull.cmo: %.cmo: %.vo
	$(CAMLC) $(ZDEBUG) $(ZFLAGS) $*.ml

ExamplePwMgr.cmx ExamplePwMgrWithSSBFull.cmx: %.cmx: %.vo
	$(CAMLOPTC) $(ZDEBUG) $(ZFLAGS) $*.ml

all: pwmgr-ssb
pwmgr-ssb: big.cmx Runtime.cmx ExamplePwMgrWithSSBFull.cmx ExamplePwMgrWithSSBFullRuntime.cmx
	$(OCAMLFIND) $(CAMLOPTLINK) -linkpkg $(OCAMLPKGS:%=-package %) nums.cmxa $(ZDEBUG) -o $@ $^

clean: my-clean
my-clean:
	rm -f ExamplePwMgr.ml ExamplePwMgr.mli pwmgr
	rm -f ExamplePwMgrWithSSBFull.ml ExamplePwMgrWithSSBFull.mli pwmgr-ssb
