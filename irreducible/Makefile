.PHONY: pdf audit clean

pdf: paper.pdf

paper.pdf: paper.tex
	pdflatex -interaction=nonstopmode paper.tex
	pdflatex -interaction=nonstopmode paper.tex

audit:
	python3 -u tools/audit_irreducible_torus.py

clean:
	rm -f paper.aux paper.log paper.out
