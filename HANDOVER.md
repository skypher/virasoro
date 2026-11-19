# Handover: torus Virasoro blocks at minimal-model charges

Updated 2026-11-19T14:57Z (22:57 Taiwan time). Paper pin: commit `eb519e08f707926985c3f0b8474f7d3d47cb8579`
(`paper.tex` / `paper.pdf`, 25 pages, 0 warnings, 0 undefined references, 0 missing characters,
0 overfull hboxes). Results are cited by their LaTeX labels; numbers in parentheses refer to the
current PDF.

## 1. Current status

All three milestones of the manuscript (`CONF`, `TOP_LAYER`, and `TOP1`) have complete,
computer-free proofs in `paper.tex` and have received independent reviewer `PASS` verdicts at
commit `eb519e08`:

- **TOP1 (`cor:top-layer-sharp`, Cor 5.11) — PASS:** At every minimal-model charge `c⋆`
  (`b⋆² = −p'/p`, `p, p' ≥ 2` coprime), every interior Kac weight `λ = h_{r,s}(b⋆)`
  (`0 < r < p`, `0 < s < p'`, `n₁ = p'r + ps < pp'`), and every level `N ≥ 1`, the eta-reduced
  block coefficient `H_N(c⋆, Δ, d)` has a pole of order **exact** `j_N(λ)` at `Δ = λ`;
  equivalently the top-layer polynomial `P_N(d)` in `eq:top-layer` is not identically zero on
  every window `ℓ_k ≤ N < ℓ_{k+1}`.
  - `prop:h13-nonvanishing` (Prop 6.8): unified two-point machinery at `d₁ = h_{1,3}(b) = −1 − 2/t`
    and `d₂ = h_{1,−3}(b) = 2 − 2/t` (replacing the former single-point `lem:one-screening` and
    eliminating the `M ≤ 40` certificate and `≤ 5`-divisor arguments):
    (i) odd-prime integrality `P_M^{(ν)}(t, Y) ∈ ℤ[½][t, Y]`, `P_M^{(2)}(0, Y) = P_M^{(1)}(0, Y)`,
    `P_M^{(ν)}(0, 0) = 4^M` via Feigin–Fuchs Fock factorization
    `G_M = B_M(q₀, 2q₀ − α)^T D_M B_M(q₀, α)` and Lagrange's theorem for centralizers in `S_M`;
    (ii) exact level polynomiality `c_{i,j}^{(ν)}(M) ∈ ℚ[M]` of degree `≤ 2i + 2j` for all `M ≥ 0`
    via `G̃, ρ̃` expansion, Leibniz rule, non-negative-mode count, and `sl₂` identities;
    (iii) exact `ℓ`-adic valuation `eq:h13-valuation` and Mahler/Legendre `ℓ`-adic Lipschitz ratio
    bound `eq:second-screening-lip`.
  - `prop:two-term-criteria` (Prop 6.9): settles every two-vector level `max(ℓ^+_k, ℓ^-_k) < N < ℓ_{k+1}`
    across three exhaustive cases (WLOG odd prime `ℓ | p'` with `a = v_ℓ(p') ≥ 1`):
    Case 1 (`s ∈ {1, p'−1}`): vanishing-order separation at `d₁`;
    Case 2 (`2 ≤ s ≤ p'−2`, `s ≢ ±1 mod ℓ`): exact pairing cancellation (`ℓ ≥ 5`) and triple-partition
    cancellation (`ℓ = 3`, `3 | s`, where both branches shift by `−k v_3(p' − 3p)` and cancel in
    `V_3^+ − V_3^-`);
    Case 3 (`2 ≤ s ≤ p'−2`, `s ≡ ±1 mod ℓ`): exact `ε`-telescoping formula
    `T_k = −m^-_k((m^-_k)² − p²) / (m^+_k((m^+_k)² − p²))`, giving `v_ℓ(T_k) ≠ 0` or
    `v_ℓ(T_k − 1) ≤ v_ℓ(k) + a − 1`, contradicting `v_ℓ(H_rat − 1) ≥ v_ℓ(k) + a` from
    `prop:h13-nonvanishing`(iii).
  - `prop:layer-coefficients` (Prop 6.7): exact `d^k` and `(d−1)^k` Taylor coefficients of
    `τ^±_k / γ^±_k` for every layer `k ≥ 1`.
- **TOP_LAYER (`thm:top-layer`, Thm 5.10) & JANTZEN (`thm:jantzen-smith`, Thm 5.8) — PASS.**
- **CONF (`thm:general-confluence`, Thm 4.3, `cor:ising-confluence`, Cor 4.4, Section 7 through
  `prop:two-branch`, Prop 7.7, and Section 4 & 6 foundations) — PASS.**

## 2. Independent review record (all on `paper.tex` at `eb519e08`)

| Scope | Reviewer | Verdict | UTC time | Envelope ID | Notes |
|---|---|---|---|---|---|
| `Prop 6.8`, `Prop 6.9` (at `d845af5`) | `yang2` | FIX → repaired at `eb519e08` | 2026-11-19T12:39Z | `yang2-20261119T123932Z-virasoro-top1-result` | Two display fixes (`2d_Δ+d_c=ℓ(λ)+ℓ(μ)` in Prop 6.8(i); removed extraneous sign in Prop 6.9 Case 2) + two clarity precisions; cores & audits confirmed. |
| `Prop 6.7`, `Cor 5.11` | `yang2` | **PASS** | 2026-11-19T12:48Z | `yang2-20261119T124803Z-virasoro-top1-rest-result` | Unchanged between `d845af5` and `eb519e08`. |
| `Thm 5.8`, `Thm 5.10`, `Lem 5.1, 5.3–5.5, 5.7` | `yang2` | **PASS** | 2026-11-19T13:41Z | `yang2-20261119T134115Z-virasoro-toplayer-result` | Astashkevich arXiv PDF verified directly; replayed `tools/audit_top_layer.py --max-level 8`. |
| `Prop 6.8`, `Prop 6.9` repairs (at `eb519e08`) | `jander` | **PASS** | 2026-11-19T13:45Z | `jander-20261119T134530Z-virasoro-top1-repair-result` | Independent other-reviewer re-check of all repairs at `eb519e08`. |
| `Thm 4.3`, `Cor 4.4`, `Sec 7` (`Def 7.1`–`Prop 7.7`) | `yang2` | **PASS** | 2026-11-19T14:40Z | `yang2-20261119T144009Z-virasoro-conf2-result` | Replayed `tools/audit_confluent_recursion.py`. |
| `Lem 2.7, 4.1, 6.3, 6.5, 6.6`, `Thm 4.2`, `Prop 6.2, 6.4` | `jander` | **PASS** | 2026-11-19T14:49Z | `jander-20261119T144949Z-virasoro-conf1-result` | Directly verified HJS arXiv:0911.2353 §§3 eqs (7)–(9). |

Citation scope notes from the reviewers:
- Astashkevich (`arXiv:hep-th/9511032`) and Hadasz–Jaskólski–Suchanek (`arXiv:0911.2353`) were
  verified directly against their PDFs.
- Springer previews of Iohara–Koga Chapters 4–6 were not accessible in full, so exact IK11 theorem
  and equation numbers remain uncertified by the external reviewers; `jander` supplied independent
  PBW/determinant deductions and `yang2` verified the Jantzen layer structure independently via
  Astashkevich Theorem B(e).
- Section 8 (Ising level-7 and level-10 embedding diamonds) is unchanged and audited by 8 of the 10
  scripts in `make audit`.

## 3. Audits, build, and bundle

- `make audit` (all 10 exact rational/symbolic scripts, including the upgraded
  `tools/audit_one_screening.py` with 8 exact checks covering Fock factorization, symbolic
  `P_M^(1,2)`, direct Shapovalov cross-check at `d₁` and `d₂`, `sl₂` identities, level
  polynomiality, valuation/Lipschitz bounds, and Cases 1–3) exited 0.
- `AUDIT_MANIFEST.md` SHA-256 hashes verified (`sha256sum -c`).
- `dist/virasoro-arxiv-v1.tar.gz` rebuilt from `eb519e08` and verified to compile standalone cleanly
  at 25 pages with 0 warnings and 0 overfull hboxes.
- `receipt.md` (local, untracked) updated and validated via `python3 -I ~/cockpit/tree.py virasoro`
  with 0 problem flags; all three milestones (`CONF`, `TOP_LAYER`, `TOP1`) are marked `established`.

## 4. Before the paper is shared

- **Author reading:** The author should read the final `paper.pdf` (in particular Sections 5–6 and
  the AI-use disclosure) and, if desired, spot-check the Iohara–Koga Chapter 4–6 pinpoint references
  against a full copy of `[IK11]`.
- **Lean:** `lean/` still corresponds to `803f1aa` (`lean/STATUS.md`); Lean formalization is
  currently untouched unless explicitly requested.
