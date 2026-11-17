# Handover: torus Virasoro blocks at minimal-model charges

Written 2026-11-17T02:31Z (10:31 Taiwan time). Paper state: commit `a7946fa` plus this file;
`paper.tex` / `paper.pdf`, 25 pages. Results are cited by their LaTeX labels; numbers in
parentheses refer to the current PDF.

## 1. Where the work stands

The open target is the sharpness of the Jantzen bound:

> **TOP1.** At a minimal-model charge `c⋆` (`b⋆² = −p'/p`, `p, p' ≥ 2` coprime) and an interior Kac
> weight `λ = h_{r,s}` (labelled so that `n₁ = p'r + ps < pp'`, `n₀ = p'r − ps`), the block
> coefficient `H_N(c⋆, Δ, d)` has a pole of order exactly `j_N(λ)` at `Δ = λ` for every level `N`.

By `thm:top-layer` (5.10), on the window `ℓ_k ≤ N < ℓ_{k+1}` the leading coefficient is
`P_N(d) = Σ_± (τ^±_k/γ^±_k) H_{N−ℓ^±_k}(c⋆, λ+ℓ^±_k, d)`, the sum over the signs with
`ℓ^±_k ≤ N`. TOP1 says that `P_N ≢ 0` in `d`.

**Proved in the paper.** These are candidates, and none has had an independent review.
- `cor:top-layer-sharp` (5.11) shows that `P_N ≢ 0` at the following levels. Write `M = N − ℓ_k` and
  let `m` be the momentum of `λ + ℓ_k`.
  - **Single-vector levels** (`N < max ℓ^±_k`): when `min(p,p')M < m + max(p,p')` (sign/σ argument);
    when `M ≤ 40` (exact certificate, `tools/audit_kl_certificate.py`); or when `M` has at most
    five divisors (by hand, with a Diophantine step for four divisors and for `q⁴`).
  - **The level `N = max ℓ^±_k`.**
  - **Two-vector levels** (`N > max ℓ^±_k`): when `max(p,p')M^± < m^±_k + min(p,p')` for both
    signs. For odd `k` the `(d−1)^{k+1}` coefficient is a positive combination there. For even `k`
    both `d = 0` derivatives are negative there.
- `prop:layer-coefficients` (6.7) was added on 2026-11-17. For every layer `k`,
  `[d^k](τ^±_k/γ^±_k) = c_k(±ρ)^k` and
  `[(d−1)^k](τ^±_k/γ^±_k) = (±1)^{k+1} c_k σ^{k−1} m^±_k/(2(p+p'))`, where
  - `ρ = −n₀/(2(p'−p))`, `σ = n₀/(2(p+p'))`;
  - `c_k = (−1)^{⌊k/2⌋} C(k−1, ⌊(k−1)/2⌋)`, which runs 1, −1, −2, 3, 6, −10, ….

  Proof outline:
  1. Take the scaling limit of the generic recursion along `(b² − b⋆², Δ − λ, d) ~ τ`. Every residue
     is `O(τ)`.
  2. Degree-0 homogeneity makes the lower moments vanish over the `k` first steps.
  3. Lagrange interpolation reduces the sum to one explicit chain.

  It replaces the former Lemma 6.7 (`lem:tau-order`) and the second-layer Proposition 7.8
  (`prop:second-layer`), which were removed to keep 25 pages.
- `lem:d-derivatives` (6.5) gives closed forms of `∂_d H_N` at `d = 0` and `d = 1`, the sums
  `K` and `L` below. `lem:regular-everywhere` (6.6) states that the normalized singular vectors
  are regular at every `b⋆`.

**Still open.** `rem:top-layer-beyond` (5.12) states these ranges precisely.
- **(a) Single-vector levels** with `M ≥ 41`, at least six divisors, outside the sign range.
  Attainment fails only if `Σ_{uv=M} u/D = Σ_{uv=M} v/D = 0`, where `D = (p'u − pv)² − m²`.
- **(b) Two-vector levels** outside the sign range. Attainment fails only if both
  `K⁺ + (−1)^k K⁻ = 0` and `m⁺_k L⁺ − (−1)^k m⁻_k L⁻ = 0`, where `K^±` and `L^±` are the derivatives
  of `H_{M^±}(c⋆, λ+ℓ^±_k, d)` at `d = 0` and `d = 1`.
- **Exact enumeration** finds no failure:
  - (a) for `k ≤ 3`, `M ≤ 60`, at every model with `pp' ≤ 60`;
  - (b) for `k ≤ 6`, `pp' ≤ 60`: 219072 cases.

## 2. Attempts on the open ranges (all 2026-11-17)

| Attempt | Outcome |
|---|---|
| Divisor families for (a), one by one | Done up to five divisors. Six or more need eliminations of degree 8–48 per family, so this was stopped. |
| Uniform locus for (a) (`Ω = W/t + 2M = −M(t+1/t)`) | Contains the four-divisor zeros and one of the two `M = 12` components, but not the other `M = 12` component or the `M = 16` component. |
| One-sign combination of the two first-order conditions in (b) | Exists in only 2280 of the 10320 cases outside the sign range (`pp' < 31`, `k ≤ 4`). Smallest failure: (2,3), `λ = 0`, `N = 11`. |
| Second-order conditions in (b) | Not defined term by term. At (2,3), `N = 11`, the chain (1,1)→(1,4) has a zero denominator at `c = 0`. |
| Isolating one branch at a fusion root of `τ⁺` | At (2,3), layer 2, `d = h₁,₃` is a root of both `τ^±₂`, so it gives nothing. |
| Interlacing of `L = Σ g/(m² − f²)` (all residues positive) | `L ≠ 0` in all 18702 uncovered (a)-cases (`pp' ≤ 60`, `k ≤ 3`, `M ≤ 200`). Sign decides 5770 and a dominant term 7140; 5792 remain. |
| Structural: `H_M(c,h,·) ≢ 0` off the Kac curves | Holds at every `c` for each `M` with at most four divisors (checked numerically at M = 6, 8, 10). Untested for six or more divisors. |
| `d = h₁,₃` (only labels `(u,1)` survive) | `H_M ≠ 0` in all 3556 uncovered cases tested; the terms are never of one sign. |
| `ℓ`-adic certificates for `L` | 5782 of 5788 cases are certified by some prime `≤ 200`, but no single structural prime works; 6 cases have none. |

The most promising next step is to prove `L ≠ 0` on the 5792 remaining (a)-cases. The positive
residues give exactly one zero per gap between Kac weights. The open question is whether a
layer weight can sit exactly at that zero, given that layer weights and Kac weights lie on the
same lattice `(n² − (p'−p)²)/(4pp')`.

## 3. Tools

**Audits (tracked).** `make audit` runs the standard suite in about 1.5 minutes. `make audit-deep`
adds four more scripts:
- the direct level-10 run;
- `audit_minimal_models.py`, the pole orders at eight models;
- `audit_layer_coefficients.py`, an exact Laurent expansion of the generic recursion against
  `prop:layer-coefficients` (52 checks, about 10 minutes);
- `audit_kl_certificate.py`, the `M ≤ 40` certificate (about 20 minutes).

Commands and hashes are in `AUDIT_MANIFEST.md`. All audits passed at `a7946fa`.

**Exploration scripts (local, untracked, in `runs/toplayer/`).**
- `laurent_rk.py`: the leading pole coefficient mod `d^{D+1}` from the generic recursion, using
  modular arithmetic and CRT; `--at1` expands at `d = 1`. It reaches levels around 45.
- `linmodel.py`, `linsplit.py`, `linres.py`: the dimensionless chain model behind
  `prop:layer-coefficients`. It gives `c_k` up to `k = 9`.
- `agt_scaling.py`, `agt_maxres.py`: the Nekrasov (AGT) scaling formula. It reproduces `r_k` up to
  `k = 4`, and individual terms do exceed `j_N` in resonant boxes.
- `twoterm_comb.py`, `interlace.py`, `struct_test.py`, `h13_test.py`, `padic_L.py`: the tests
  in the table above. Their logs (`*.log`) sit next to them.
- `k3_window.py`, `gamma3*.py`: Gram-matrix values at (2,3), layer 3.

The working receipt `receipt.md` (local, untracked) has the full history of the hard step.

## 4. Before the paper is shared

- **Review.** Nothing added since `803f1aa` has been independently reviewed. That covers
  `prop:layer-coefficients`, `lem:d-derivatives`, `lem:regular-everywhere`, the extensions of
  `cor:top-layer-sharp` and its certificate, and the Diophantine steps.
- **Disclosure.** The AI-use disclosure says the author checked the final arguments. That needs
  the author's own reading first.
- **Lean.** `lean/` covers the `803f1aa` version; `lean/STATUS.md` maps the revisions.
- **arXiv bundle.** The bundle in `dist/` is stale; rebuild it with `tools/build_arxiv_bundle.sh`.
