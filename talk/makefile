TMP=tmp
REPORT=talk
BIBDEPS=talk.bib
DEPS=talk.tex talk.bib

$(REPORT).pdf: $(DEPS)
	mkdir -p $(TMP)
	pdflatex -output-directory $(TMP) $(REPORT).tex
	cp $(BIBDEPS) $(TMP) && cd $(TMP) && bibtex $(REPORT).aux
	pdflatex -output-directory $(TMP) $(REPORT).tex
	pdflatex -output-directory $(TMP) $(REPORT).tex
	mv $(TMP)/$(REPORT).pdf .

clean:
	rm -r $(TMP)
