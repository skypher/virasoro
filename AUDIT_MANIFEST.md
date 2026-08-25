# Exact-arithmetic audit manifest

This manifest describes the ancillary checks for `paper.tex`.  The ordinary
suite is run with

```sh
python3 -m pip install -r requirements-audit.txt
make audit
```

The direct level-ten reconstruction is added with

```sh
make audit-deep
```

The tested environment is CPython 3.12 with SymPy 1.12.  A successful run
exits with status 0.  Each completed identity is printed with a `PASS`
prefix; any failed identity raises an assertion or prints `FAIL` and exits
nonzero.  Timing and `reconstructed F_N` progress lines are informational.

The ordinary suite runs, in order:

1. `tools/audit_first_resonances.py` — level-three data, the energy crossing
   form, and the level-seven embedding diamond.
2. `tools/audit_low_levels.py` — level-four Gram data, null vectors, torus
   polynomials, and the spin crossing form.
3. `tools/audit_grade10_direct.py --crossing-only` — intrinsic construction
   of the level-ten second crossing form from the exact 42-by-42 Gram matrix,
   without generic-residue or confluence input.
4. `tools/audit_grade10_confluence.py` — exact level-ten confluence and the
   displayed finite-part polynomial.
5. `tools/audit_confluent_recursion.py` — low-level collision moments from
   the shifted recursion.
6. `tools/audit_direct_principal_parts.py` — direct inverse-Shapovalov checks
   of the displayed principal parts at the exact sample external weights
   `d = 3/7` and `d = 23`.
7. `tools/audit_stocco_comparison.py` — comparison through level four with
   Stocco's formulas.
8. `tools/audit_ising_characters.py` — BGG numerators and independent
   free-fermion character counts through level 30.

The deep target additionally runs `tools/audit_grade10_direct.py`, which
reconstructs the inverse-Shapovalov coefficients through level ten at the
exact sample external weight `d = 3/7` and checks the second level-ten
principal part directly there.  The intrinsic crossing-form check is repeated
as part of that full run.

## SHA-256

The hashes below identify the submitted audit sources.

```text
b3e84ff35635be68d83808e51653d939207c6da12859083db8d22ffff3d7af00  Makefile
8347daed02ebf7b3c3cfa494e97049b7e0ab15b9af00a5addd843ed44381a64a  requirements-audit.txt
701649d93a313c2853a9ecd4d3106ff1957a97c2ff802e4e57612e9ed6e4c84c  tools/audit_confluent_recursion.py
240545d5e84d292f360bf8d55d18de0e4dbe28ccbf3526f551fd8db4a1a81f9e  tools/audit_direct_principal_parts.py
90218c120e892157507e9167fbc9033ba85c6c25fbf2bde3269806ffced26185  tools/audit_first_resonances.py
978df56dce0c8be9389c8fe8b3d7dfd93170b2ea7a74fec47d1cdd3a8c809d29  tools/audit_grade10_confluence.py
bd8b7ef2bf64e68ea7c822fa2a77c1d52e57c617456066a8438fc800e978f517  tools/audit_grade10_direct.py
26a0c7b5a325f3eacc7a900facff9e411354e39d752be7f24a66a10fbfab4448  tools/audit_ising_characters.py
440b1a744cae37788512e6db19f41c132e8d42e0a813ad9101b217bc54946c38  tools/audit_low_levels.py
f979190e290b2e57649d01dc6ba0fcaf225ff21fb085e92431c370a2b4f0aeb8  tools/audit_stocco_comparison.py
002af113d98520e3b0049b7e4c918f404f9459395f5af0d80ae80da36f360ced  tools/direct_reconstruction.py
3f69e0f5a782cf9e23037907dbf38467fa7c5550750c5faf587cbddffc75b519  tools/exact_shapovalov.py
```
