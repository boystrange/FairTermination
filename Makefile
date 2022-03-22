NULL =

SOURCES = \
  lmcs.cls \
  agda.sty \
  mathpartir.sty \
  prooftree.sty \
  main.bib \
  main.bbl \
  abstract.tex \
  agda.tex \
  compliance.tex \
  conclusion.tex \
  introduction.tex \
  is-macros.tex \
  is.tex \
  macros.tex \
  main.tex \
  subtyping.tex \
  termination.tex \
  types.tex \
  $(NULL)

all:
	agda --html --html-highlight=code FairTermination.lagda.md

CicconePadovani21.zip: $(SOURCES)
	zip $@ $^

clean:
	rm -f *.zip
