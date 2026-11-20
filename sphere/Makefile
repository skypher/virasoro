PYTHON ?= python3 -u

.PHONY: audit pdf clean

audit:
	cd .. && PYTHONPATH=. $(PYTHON) sphere/tools/exact_sphere_block.py --max-level 7
	cd .. && PYTHONPATH=. $(PYTHON) sphere/tools/audit_large_delta.py --max-z 7 --max-level 5
	cd .. && PYTHONPATH=. $(PYTHON) sphere/tools/audit_sphere_confluence.py --max-level 7
	cd .. && PYTHONPATH=. $(PYTHON) sphere/tools/audit_sphere_top_layer.py --max-level 7

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex

clean:
	rm -f paper.aux paper.log paper.out paper.toc
