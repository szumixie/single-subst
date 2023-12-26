LAGDAS := \
  Intro.lagda \
  SSC.lagda \
  AlphaNorm.lagda \
  Iso.lagda

TEXS := $(addsuffix .tex,$(basename $(LAGDAS)))

all: main.pdf

%.tex: %.lagda
	@echo "Checking lagda files.."
	agda --latex $< --latex-dir=.

main.pdf : main.tex ${TEXS}
	echo ${TEXS} | sed 's/ /\n/g' | sed 's/.*/\\input\{\0\}/' >inputs.tex
	@echo "Compiling tex..."
	xelatex main
	bibtex main
	xelatex main
	xelatex main

clean:
	rm -f *.aux *.bbl *.blg *.fdb_latexmk *.fls *.log *.out *.nav *.snm *.toc *~ *.ptb *.idx *.pdf
	mv main.tex main.tex1
	rm -f inputs.tex *.tex */*.tex agda.sty
	mv main.tex1 main.tex
