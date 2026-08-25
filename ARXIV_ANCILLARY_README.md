# Exact-arithmetic ancillary replays

This directory accompanies *Exact algebraic confluence for torus one-point
Virasoro-block recursions*. It contains eight audit scripts and two shared
libraries. All reported calculations use exact arithmetic.

From this directory, install the pinned dependency and run the standard suite:

```sh
python3 -u -m pip install -r requirements-audit.txt
make audit
```

The deeper direct level-ten reconstruction is:

```sh
make audit-deep
```

`AUDIT_MANIFEST.md` describes the scope, independence, success markers, and
SHA-256 hashes of the checks. The versioned repository is
<https://github.com/skypher/virasoro>.
