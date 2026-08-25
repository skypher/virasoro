PYTHON ?= python3 -u

.PHONY: audit audit-deep pdf

audit:
	$(PYTHON) tools/audit_first_resonances.py
	$(PYTHON) tools/audit_low_levels.py
	$(PYTHON) tools/audit_grade10_direct.py --crossing-only
	$(PYTHON) tools/audit_grade10_confluence.py
	$(PYTHON) tools/audit_confluent_recursion.py
	$(PYTHON) tools/audit_direct_principal_parts.py
	$(PYTHON) tools/audit_stocco_comparison.py
	$(PYTHON) tools/audit_ising_characters.py

audit-deep: audit
	$(PYTHON) tools/audit_grade10_direct.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
