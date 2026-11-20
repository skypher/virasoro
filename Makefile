PYTHON ?= python3 -u

.PHONY: audit audit-deep audit-irreducible pdf arxiv-bundle

audit:
	$(PYTHON) tools/audit_first_resonances.py
	$(PYTHON) tools/audit_low_levels.py
	$(PYTHON) tools/audit_regular_families.py
	$(PYTHON) tools/audit_grade10_direct.py --crossing-only
	$(PYTHON) tools/audit_grade10_confluence.py
	$(PYTHON) tools/audit_confluent_recursion.py
	$(PYTHON) tools/audit_direct_principal_parts.py
	$(PYTHON) tools/audit_stocco_comparison.py
	$(PYTHON) tools/audit_top_layer.py
	$(PYTHON) tools/audit_one_screening.py

audit-deep: audit
	$(PYTHON) tools/audit_grade10_direct.py
	$(PYTHON) tools/audit_minimal_models.py
	$(PYTHON) tools/audit_layer_coefficients.py
	$(PYTHON) tools/audit_kl_certificate.py

# Sections 9-14 (irreducible traces); imports tools/direct_reconstruction.py and tools/exact_shapovalov.py
audit-irreducible:
	$(PYTHON) irreducible/tools/audit_irreducible_torus.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex

arxiv-bundle:
	bash tools/build_arxiv_bundle.sh
