.PHONY: all clean

all: proj-final.tar.gz

VFILES := $(addprefix ../,$(filter %.v,$(shell cat ../_CoqProject)))

proj-final.pdf : %.pdf : %.tex
	pdflatex -interaction=batchmode -synctex=1 $< || true
	pdflatex -synctex=1 $<

clean:
	rm -f *.log *.synctex.gz proj-final.tar.gz proj-final.pdf proj-final.aux

proj-final.tar.gz: proj-final.pdf ../Makefile ../_CoqProject $(VFILES)
	tar -czvf $@ proj-final.pdf proj-final.tex ../Makefile ../_CoqProject $(VFILES)
