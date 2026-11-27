# Exact-arithmetic ancillary replays

This directory accompanies *Colliding poles of Virasoro conformal blocks at
rational central charge* and its companion *A generalized Rocha--Caridi
formula for torus one-point traces in minimal models*. It contains thirteen
audit scripts and two shared libraries for Part I of the first paper (torus
Verma blocks), and one audit script for the second paper (irreducible
traces). All reported
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

(`make check` and `make check-long`, the names used in the paper, run the same two suites.)

The examples of the traces paper are replayed by:

```sh
make audit-irreducible
```

That script, `irreducible/tools/audit_irreducible_torus.py`, imports the two
shared libraries `tools/direct_reconstruction.py` and `tools/exact_shapovalov.py`
from this directory, so run it from here.

`AUDIT_MANIFEST.md` describes the scope, independence, success markers, and
SHA-256 hashes of the checks. The versioned repository is
<https://github.com/skypher/virasoro>.
