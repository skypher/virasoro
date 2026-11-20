# Current state (2026-11-20, tmp session)

Two manuscripts now (user, tmp terminal, 2026-11-20 14:5x Taiwan: "merge torus and traces paper."):

- `paper.tex` (42 pp): torus paper, Sections 1-8 as reviewed at 299e8a0 (numbers unchanged, the sphere
  paper cites them), Sections 9-14 = the traces paper merged from `irreducible/paper.tex` at 4607fde
  (merge commits 84d8f15, cf9078e; repairs 21f5305). `irreducible/paper.tex` is kept only as the reviewed
  source of those sections.
- `sphere/paper.tex` (25 pp): sphere paper, separate (repairs 179e04c, c8ae6af, 5040b6d).

Review state, open items and the packet log are in `receipt.md` (hard step FULL). Audits:
`make audit`, `make audit-deep`, `make audit-irreducible`, `make -C sphere audit`; bundle `make arxiv-bundle`
(now includes the Part II audit). Before outside distribution: the papers cite the torus paper and the code
at github.com/skypher/virasoro, which is private.

The section below is Neon's handover of 05:52Z and describes the three papers before the merge.

# Handover to tmp session (all three Virasoro papers complete)

Updated 2026-11-20T05:52:11Z (13:52 Taiwan time; Neon session handing the repository back to the
tmp Claude Code session per user instruction, 2026-11-20 13:4x Taiwan: "once neon finishes it hands
over the ptojrct bsck t9 you."). Repository `skypher/virasoro`, branch `main`, HEAD at
`5df4cd7801f33a103bd986b028314460dd8f4c35` (pushed to `origin/main` before this handover commit).
No background tasks, computations, or watchers are running.

## Summary of the three manuscripts

1. **Verma torus one-point block** (`paper.tex`, `paper.pdf`)
   - Final commit touching `paper.tex`: `299e8a0576575c65ceb4bf2d1caded30617b3a9a`
     (blob `70a2993bd231f6ce843d986774b084af315c3919`, untouched since before this brief).
   - Length and build: **22 pages**, 0 LaTeX warnings, 0 overfull hboxes.
   - Review record:
     - Pre-shortening 25-page manuscript (`eb519e08`): all milestones (`CONF`, `TOP_LAYER`, `TOP1`,
       top-node assembly, and Section 8) received independent reviewer `PASS` / scoped `PASS` from
       `yang2` and `jander` (2026-11-19T12:48Z–15:47Z; full table in Section 2 below).
     - Shortened 22-page manuscript (`5d457f6`): `yang2` returned **PASS** on items 1–3 at
       `2026-11-20T00:24:37Z` (`yang2-20261120T002437Z-virasoro-shorten-result`), with abstract and
       Prop. 8.1 notes applied in `5d457f6`.
     - Citation-only update (`299e8a05`): added `[IK11, Props. 5.1, 5.2, Cor. 5.2]` in Prop. 6.2
       (see Open items below).

2. **Verma sphere four-point block** (`sphere/paper.tex`, `sphere/paper.pdf`; primary target `S`)
   - Final commit touching `sphere/paper.tex`: `5df4cd7801f33a103bd986b028314460dd8f4c35`
     (blob `d917612de455df747769397f98392f68a41fb3e9`).
   - Length and build: **24 pages**, 0 LaTeX warnings, 0 overfull hboxes, 0 non-ASCII characters.
   - Contents: self-contained algebraic proof of Zamolodchikov's large-Δ asymptotics
     `lim_{Δ→∞} H_N(c, Δ, Δ_i) = δ_{N,0}` for all `(c, Δ_1, ..., Δ_4) ∈ ℂ^5` (Theorem 3.1,
     Lemmas 3.2–3.7), fixed-`b⋆` all-order exact algebraic confluence for `H_N` and `B_N`
     (Theorem 4.7), and minimal-model Jantzen pole-order bound, top-layer formula, and unconditional
     attainment for indeterminate external weights for both `B_N` and `H_N` (Theorems 5.1, 5.3,
     5.4, 5.5), plus Section 6 examples (`(2,3)` `N=5` and Ising `N=7, 10, 11`).
   - Review record:
     - Packet 1 (`78adcfdb`): `yang2` FIX on `S1_CONF` (`02:30:08Z`, `yang2-20261120T023008Z-virasoro-s1-conf-result`);
       `jander` FIX on `S1_ASYMP` (`02:37:57Z`, `jander-20261120T023757Z-virasoro-s1-asymp-result`).
       All repairs landed at `024c5fc7` and `495ef9e4`.
     - Packet 2 (`495ef9e4`, swapped reviewers):
       - `S1_ASYMP` (Sections 2–3, Theorem 3.1, Lemmas 3.2–3.7 + `audit_large_delta.py` replay):
         `yang2` **PASS** at `2026-11-20T03:30:56Z` (`yang2-20261120T033056Z-virasoro-p2a-asymp-result`).
       - `S2_TOP`, `S2_SHARP`, Section 6 (`exact_sphere_block.py` and `audit_sphere_top_layer.py` replay):
         `yang2` **PASS** at `2026-11-20T03:32:09Z` (`yang2-20261120T033209Z-virasoro-p2b-s2-result`).
       - `S1_CONF` (Section 4, Zamolodchikov 2004 / HJS 2010 / Ribault 2019 citations verified):
         `jander` **PASS** at `2026-11-20T03:34:50Z` (`jander-20261120T033450Z-virasoro-s1-conf-recheck-result`).
     - Packet 3a (`5dd2934b`/`899cee4d`): `S_POLISH` (8 local text/citation polish edits + replay of
       `audit_sphere_confluence.py --max-level 7`, `audit_sphere_top_layer.py --max-level 7`, and
       24-page PDF build): `yang2` **PASS** at `2026-11-20T04:36:36Z`
       (`yang2-20261120T043636Z-virasoro-p3a-result`).
     - Packet 4a Item 2 (`4607fde4`, two related-work citations from
       `~/agy-advice/checks/virasoro_large_delta_lit.md`): `jander` (`2026-11-20T05:45:26Z`,
       `jander-20261120T054526Z-virasoro-p4a-result`) verified byte-for-byte preservation of all
       mathematical text and confirmed `Artemev–Khromov` (`Phys. Rev. D 114, 045002 (2026)`,
       `10.1103/9y4x-9b4p`, `arXiv:2603.08194`), requesting one citation-scope qualification for
       `Ghosal–Rémy–Sun–Sun` (external-momentum range of Theorem 1.2 and dated 1 November 2022
       draft URL). Applied verbatim at `5df4cd78` (see Open items below).

3. **Irreducible minimal-model torus one-point traces** (`irreducible/paper.tex`, `irreducible/paper.pdf`; secondary target `T_IRR`)
   - Final commit touching `irreducible/paper.tex`: `4607fde4cb5585f25b40c8956e58bf9bce593b9a`
     (blob `0745ea1a274183deccc644923bb4efa49b919819`, unchanged at `5df4cd78`).
   - Length and build: **19 pages**, 0 LaTeX warnings, 0 overfull hboxes, 0 non-ASCII characters.
   - Contents: exact iff characterization of primary-operator descent (`d ∈ F_{p,p'}(r,s)`) vs
     all-order Verma regularity (`d ∈ F^±_{p,p'}(r,s)`), Jantzen vertex filtration, and joint
     `(b, Δ)`-regularity (Theorem 1.1, Lemmas 2.1, 2.3, 3.1, 3.3, Propositions 2.2, 3.2);
     two-weight fusion product rule for the first-layer Jantzen vertex ratio and Gamma-potential
     BGG cocycle (Theorem 1.2, Proposition 4.1); two-layer `τ`-Jantzen telescoping, generalized
     Rocha–Caridi alternating BGG identity with exact fixed-`b⋆` confluence, higher-layer Jantzen
     ratios, and collision-free single-index truncated recursion (Lemma 5.1, Theorem 1.3,
     Corollary 1.4), plus Section 6 minimal-model examples (Ising, Lee–Yang, Tricritical Ising).
   - Review record:
     - Packet 3a (`899cee4d`): `yang2` FIX on `T_IRR_CORE` §§1–3 (`04:36:36Z`,
       `yang2-20261120T043636Z-virasoro-p3a-result`); Packet 3b (`899cee4d`): `jander` FIX on
       `T_IRR_COCYCLE_BGG` §§4–6 (`04:45:48Z`, `jander-20261120T044548Z-virasoro-p3b-result`).
       All 10 findings repaired at `714568e2`, with author/bibliography alignment at `4607fde4`.
     - Packet 4b (`4607fde4`, swapped to `yang2`): `T_IRR_BGG` (Sections 4–6, bibliography,
       author/disclosure metadata, and isolated replay of `audit_irreducible_torus.py` + 19-page
       PDF build): `yang2` **PASS** at `2026-11-20T05:36:43Z`
       (`yang2-20261120T053643Z-virasoro-p4b-result`).
     - Packet 4a Item 1 (`4607fde4`, swapped to `jander`): `T_IRR_CORE` (Abstract, Sections 1–3,
       slope carry-through in Lemma 5.1, companion citations Props. 6.2/6.4/Lem. 6.6, HJS §3, JSF
       article 183, Ribault v4, disclosures): `jander` **PASS** at `2026-11-20T05:45:26Z`
       (`jander-20261120T054526Z-virasoro-p4a-result`).

## Open items (unreviewed edits, pending verdicts, questions)

- **Pending review verdicts:** none. No open review claims exist on ntfy or `agent-messages`.
- **Unreviewed minor edits (citation/wording only; zero mathematical changes):**
  1. `sphere/paper.tex` at `5df4cd78`: 3-line citation-scope update for `GhosalRemySunSun2022` in
     Section 1 item 1 and `\begin{thebibliography}` (exact replacement requested by `jander` in
     `jander-20261120T054526Z-virasoro-p4a-result`). Can be confirmed in any future batch if a
     formal confirmation on the final pin is desired.
  2. `paper.tex` at `299e8a05`: citation-only addition `[IK11, Props. 5.1, 5.2, Cor. 5.2]` in
     Proposition 6.2 (unchanged since `2026-11-20T00:41Z`).
  3. `irreducible/paper.tex` at `4607fde4`: **no unreviewed edits** (exact blob `0745ea1a` passed
     by both `yang2` and `jander`). One minor optional wording suggestion from `yang2` at lines
     1445–1449 ("start with 'Through level 30'") was intentionally not applied so the passed blob
     remains frozen; apply only if the manuscript is reopened later.
- **`[yours]` questions:** none open. Before outside distribution or submission, standard author
  reading of all three PDFs (`paper.pdf`, `sphere/paper.pdf`, `irreducible/paper.pdf`), their
  AI-use disclosures, and any packaging/arXiv bundling decisions belong to the user.

## How to run each build and audit

- **Torus paper (root):**
  - `make pdf` (builds `paper.pdf`, 22 pp)
  - `make audit` (runs all exact rational/symbolic audit scripts in `tools/`)
- **Sphere paper (`sphere/`):**
  - `make -C sphere pdf` (builds `sphere/paper.pdf`, 24 pp)
  - `make -C sphere audit` (runs `exact_sphere_block.py --max-level 7`,
    `audit_large_delta.py --max-z 7 --max-level 5`,
    `audit_sphere_confluence.py --max-level 7`, and
    `audit_sphere_top_layer.py --max-level 7`)
- **Irreducible torus paper (`irreducible/`):**
  - `make -C irreducible pdf` (builds `irreducible/paper.pdf`, 19 pp)
  - `make -C irreducible audit` (runs `python3 -u irreducible/tools/audit_irreducible_torus.py`,
    covering all 4 exact rational/symbolic stages: Lemma 2.3(iv) + Theorem 1.1, Theorem 1.2 +
    Proposition 4.1, Theorem 1.3 quotient-Gram vs BGG sum on Lee–Yang/Ising/Tricritical Ising,
    and Corollary 1.4 single-index recursion on Ising `N ≤ 30` and Lee–Yang `N ≤ 25`)
- **Receipt check:** `python3 -I ~/cockpit/tree.py virasoro` (currently reports all four
  milestones `S1`, `S2`, `T_IRR`, `T_TORUS` and root `ST` as `PASS` / `established`, 0 flags).

---

# Earlier handover: torus Virasoro blocks at minimal-model charges

Updated 2026-11-19T15:59Z (23:59 Taiwan time; session wound down cleanly at the 00:00 Taiwan
timebox). Paper pin: commit `eb519e08f707926985c3f0b8474f7d3d47cb8579`
(`paper.tex` blob `8bba870ae47db96513a03a59690c39749ccd18c9`, unchanged in `HEAD`; `paper.pdf`
25 pages, 0 warnings, 0 undefined references, 0 missing characters, 0 overfull hboxes). Results are
cited by their LaTeX labels; numbers in parentheses refer to the current PDF.

## 0. Update 2026-11-20 (shortened version, awaiting review)

User, 2026-11-20 (tmp terminal), answering "unshelve virasoro, make the ½-page cuts, cut the Ising part
to a half-page example, and work on the ℓ | k case?": "yes". The paper is now 22 pages (0 LaTeX
warnings); `make audit` exit 0 (2026-11-20T00:14Z start). Changes:
- Section 8 is Prop 8.1 (`prop:ising-double-poles`): first double poles at levels 7, 10, 11 with
  coefficients τ/γ, γ from Prop 6.7 (γ₁₁ = −2477917160468750/6561 is new; γ₇, γ₁₀ unchanged).
- Removed: Prop 7.7 (two-branch closure) and Cor 7.6, Cor 3.3 and Cor 4.4 (Ising classes and
  specialization), Appendix A, Remarks 5.9 and 5.12, and the d = 1 halves of Lemma 6.5 and
  Prop 6.7 (old numbers); the Astashkevich B(e) route in Thm 5.8 is one sentence.
- Iohara–Koga [IK11] page references were checked against the full book (private Pdfs2 copy) on
  2026-11-20; record in `~/agy-advice/checks/virasoro_IK11_pinpoints.md` (author-side, not a review).
- Prop 6.8(ii) stays: the ℓ | k subcase of Case 3 has no proof without it (`receipt.md`, memo SHORT).
- Sections 1–4 below describe the pre-shortening version; the PASS record in section 2 is for `eb519e08`.

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
| Top-node `T` assembly (`CONF`, `TOP_LAYER`, `TOP1`, Sec 8 interface) | `yang2` | **PASS** | 2026-11-19T15:41Z | `yang2-20261119T154113Z-virasoro-assembly-result` | End-to-end dependency and interface assembly check at `eb519e08`. |
| Section 8 & Appendix A (`Prop 8.1`–`Prop 8.6`, `eq:theta7-expanded`, `eq:theta10-expanded`) | `jander` | **Scoped PASS** (+ audit FIX applied) | 2026-11-19T15:47Z | `jander-20261119T154730Z-virasoro-sec8-result` | All structural proofs and derivative-defined principal parts PASS; audit-coverage finding on symbolic `Theta_7(d)` closed in `tools/audit_first_resonances.py` without modifying `paper.tex`. |

Citation scope notes from the reviewers:
- Astashkevich (`arXiv:hep-th/9511032`) and Hadasz–Jaskólski–Suchanek (`arXiv:0911.2353`) were
  verified directly against their PDFs.
- Springer previews of Iohara–Koga Chapters 4–6 were not accessible in full, so exact IK11 theorem
  and equation numbers remain uncertified by the external reviewers; `jander` supplied independent
  PBW/determinant deductions and `yang2` verified the Jantzen layer structure independently via
  Astashkevich Theorem B(e).
- Section 8 (Ising level-7 and level-10 embedding diamonds) passed static review by `jander`;
  Appendix A's expanded numerical coefficients are verified symbolically in `ℚ[d]` by
  `tools/audit_first_resonances.py` (`Theta_7`) and `tools/audit_grade10_confluence.py` (`Theta_10`)
  inside `make audit` (not independently machine-replayed by the static reviewer).

## 3. Audits, build, and bundle

- `make audit` (all 10 exact rational/symbolic scripts, including the upgraded
  `tools/audit_first_resonances.py` — now symbolically certifying `Theta_7(d)` in `ℚ[d]` under a
  raising assertion — and `tools/audit_one_screening.py` with 8 exact checks covering Fock
  factorization, symbolic `P_M^(1,2)`, direct Shapovalov cross-check at `d₁` and `d₂`, `sl₂`
  identities, level polynomiality, valuation/Lipschitz bounds, and Cases 1–3) exited 0.
- `AUDIT_MANIFEST.md` SHA-256 hashes verified (`sha256sum -c`).
- `dist/virasoro-arxiv-v1.tar.gz` rebuilt with the updated audit script and manifest (while keeping
  `paper.tex` byte-for-byte identical to `eb519e08`), verified to compile standalone cleanly at 25
  pages with 0 warnings and 0 overfull hboxes.
- `receipt.md` (local, untracked) updated and validated via `python3 -I ~/cockpit/tree.py virasoro`
  with 0 problem flags; all three milestones (`CONF`, `TOP_LAYER`, `TOP1`) and top-node `T` are
  marked `established`.

## 4. Open steps, running computations, and how to resume

- **Running computations / watchers:** None. All background computations and `yang_watch.py`
  watchers have exited cleanly.
- **Open mathematical steps:** None on the manuscript (`CONF`, `TOP_LAYER`, `TOP1`, top-node `T`
  assembly, and Section 8 structural proofs all hold independent reviewer `PASS` / scoped `PASS`
  at `eb519e08`, and `Theta_7(d)` is now symbolically certified in `tools/audit_first_resonances.py`).
- **Before the paper is shared:**
  - **Author reading:** The author should read the final `paper.pdf` (in particular Sections 5–6
    and the AI-use disclosure) and, if desired, spot-check the Iohara–Koga Chapter 4–6 pinpoint
    references against a full copy of `[IK11]` and optionally replay `make audit` / `make audit-deep`
    on the updated `tools/audit_first_resonances.py`.
  - **Lean:** `lean/` still corresponds to `803f1aa` (`lean/STATUS.md`); Lean formalization is
    untouched unless explicitly requested.
- **How to resume:** Verify `git status` is clean on `main`, check `receipt.md` (`python3 -I
  ~/cockpit/tree.py virasoro`), and run `make pdf` / `make audit` / `make arxiv-bundle` if any
  author-requested edits are made.
