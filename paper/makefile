TMP=tmp
REPORT=paper
BIBDEPS=paper.bib
DEPS=paper.tex paper.bib

$(REPORT).pdf: $(DEPS)
	mkdir -p $(TMP)
	pdflatex -output-directory $(TMP) $(REPORT).tex
	cp $(BIBDEPS) $(TMP) && cd $(TMP) && bibtex $(REPORT).aux
	pdflatex -output-directory $(TMP) $(REPORT).tex
	pdflatex -output-directory $(TMP) $(REPORT).tex
	if [ ! -f $(REPORT).pdf ]; then ln -s $(TMP)/$(REPORT).pdf $(REPORT).pdf; fi

clean:
	rm -r $(TMP)
