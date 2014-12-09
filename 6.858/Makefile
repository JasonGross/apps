.PHONY: all clean

TEX_SOURCE := proj-final proj-final-presentation
PDFS := $(addsuffix .pdf,$(TEX_SOURCE))
TEXS := $(addsuffix .tex,$(TEX_SOURCE))
IMAGES := coq-logo.png waze.png

all: proj-final.tar.gz

VFILES := $(addprefix ../,$(filter %.v,$(shell cat ../_CoqProject)))

proj-final-presentation.pdf: coq-logo.png waze.png

$(PDFS) : %.pdf : %.tex
	pdflatex -interaction=batchmode -synctex=1 $< || true
	pdflatex -synctex=1 $<

clean:
	rm -f *.log *.synctex.gz proj-final.tar.gz $(PDFS) *.aux *.toc *.snm *.nav

proj-final.tar.gz: $(PDFS) $(TEXS) $(IMAGES) ../Makefile ../_CoqProject $(VFILES)
	tar -czvf $@ $(PDFS) $(TEXS) $(IMAGES) ../Makefile ../_CoqProject $(VFILES)
