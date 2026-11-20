# Exact-arithmetic ancillary replays

This directory accompanies *Exact algebraic confluence for torus one-point
Virasoro blocks and irreducible minimal-model traces*. It contains thirteen
audit scripts and two shared libraries for Sections 2-8 (Verma blocks), and
one audit script for Sections 9-14 (irreducible traces). All reported
calculations use exact arithmetic.

From this directory, install the pinned dependency and run the standard suite:

```sh
python3 -u -m pip install -r requirements-audit.txt
make audit
```

The deeper direct level-ten reconstruction is:

```sh
make audit-deep
```

The examples of Sections 9-14 are replayed by:

```sh
make audit-irreducible
```

That script, `irreducible/tools/audit_irreducible_torus.py`, imports the two
shared libraries `tools/direct_reconstruction.py` and `tools/exact_shapovalov.py`
from this directory, so run it from here.

`AUDIT_MANIFEST.md` describes the scope, independence, success markers, and
SHA-256 hashes of the checks. The versioned repository is
<https://github.com/skypher/virasoro>.
