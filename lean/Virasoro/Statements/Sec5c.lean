import Virasoro.Statements.Sec5b
import Virasoro.JantzenForm
import Virasoro.Orbit

/-!
# Frozen statements: Section 5 of `paper.tex` at 70bac53 (changed and new results)

Lemma 5.1 (restated), Lemma 5.4, Lemma 5.7, Theorem 5.9, Corollary 5.10.  The statements of
Lemma 5.3, Lemma 5.5, Lemma 5.6 and Theorem 5.8 are unchanged and stay in `Statements/Sec5a`
(there numbered 5.6, 5.9, 5.10, 5.7).
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial Module

namespace V2

/-- Lemma 5.1 (`lem:smith`), paper.tex l.553–559.  Let `R = ℂ[[x]]`, `G(x) ∈ M_m(R)` with nonzero
determinant and Smith exponents `0 ≤ e₁ ≤ ⋯ ≤ e_m`.  Then `ord_x det G = ∑ e_i`,
`dim ker G(0) = #{i : e_i > 0}`, and `G(x)⁻¹` has pole order `e_m`.  In particular, if
`ord_x det G = dim ker G(0)`, every positive Smith exponent equals `1`.

Demand sheet.
- matrix size `m` arbitrary, entries in `ℂ[[x]]` (l.554);
- `det G ≠ 0` (l.554); exponents as a multiset `s` with `IsSmith G s`, `e_m = s.sup` (l.555);
- three identities, not bounds (l.556–557);
- last clause: hypothesis `ord det = dim ker G(0)`, conclusion on the positive exponents only
  (l.557–558).  The earlier statement `Virasoro.Stmt_lem_smith` also concluded that `G⁻¹` has at
  most a simple pole; the paper no longer states this. -/
def Stmt_lem_smith : Prop :=
  ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) (PowerSeries ℂ)) (s : Multiset ℕ),
    G.det ≠ 0 → IsSmith G s →
      G.det.order = ((s.sum : ℕ) : ℕ∞) ∧
      finrank ℂ (ker0 G) = (s.filter fun e => 0 < e).card ∧
      poleOrderInv G = s.sup ∧
      (G.det.order = ((finrank ℂ (ker0 G) : ℕ) : ℕ∞) → ∀ e ∈ s, 0 < e → e = 1)

end V2

/-- Lemma 5.4 (`lem:top-coefficient`), paper.tex l.605–625.  Fix `(c,h)`.  For `i ≥ 1` and
`u, v ∈ J^i_N(c,h)` with families `u(x), v(x)`, `B^i(u,v) = [x^i] v(x)ᵀ G_N(c,h+x) u(x)`.
(i) `B^i` is a well-defined symmetric form, and `B^i(L_{-n}u, v) = B^i(u, L_n v)` for `n > 0`,
`u ∈ J^i_{N-n}`, `v ∈ J^i_N`.
(ii) If `det G_N(c,h+x) ≢ 0` and `k ≥ 1` is the largest local Smith exponent at `x = 0`, then
`B^k` is nondegenerate on `J^k_N(c,h)` and `[x^{-k}] G_N(c,h+x)⁻¹ = ι (B^k)⁻¹ ι^*`.
(iii) With `G_N(c,h+x) = G₀ + xG₁ + x²G₂ + O(x³)`: `B¹(u,v) = vᵀG₁u`, and
`B²(u,v) = vᵀ(G₂u + G₁u₁)` for every `u₁` with `G₀u₁ = -G₁u`.

Demand sheet.
- `(c,h)` complex, all levels `N`, all `i ≥ 1` (l.607);
- (i) well-defined: the value `jformFam` of every pair of families equals `jform` (which is
  defined with chosen families); symmetric; bilinear ("form"), stated as linearity in the first
  argument, which with symmetry gives the second (l.611);
- (i) contravariance: `n > 0`, `u` at level `M = N - n`, `v` at level `N = M + n`; `L_{-n}u` and
  `L_nv` are given by their coordinates `u'`, `v'`; their membership in the layers is part of
  the conclusion (l.612–613);
- (ii) hypothesis `det ≠ 0`; `k ≥ 1` is the maximum of the Smith multiset (l.614–615);
  `S = ι (B^k)⁻¹ ι^*` is read as in the earlier `Stmt_prop_transverse_residue`: `S w ∈ J^k_N`
  and `B^k(u, S w) = uᵀw` for all `u ∈ J^k_N`, which determines `S` when `B^k` is nondegenerate
  (l.616–619);
- (iii) `u, v ∈ J¹_N` for `B¹`, `u, v ∈ J²_N` for `B²`; every `u₁` with `G₀u₁ = -G₁u`
  (l.620–623). -/
def Stmt_lem_top_coefficient : Prop :=
  ∀ c h : ℂ,
    (∀ (N i : ℕ), 1 ≤ i →
      (∀ (u v : Nat.Partition N → ℂ) (wu wv : Nat.Partition N → ℂ[X]),
        IsJFamily c h N i u wu → IsJFamily c h N i v wv →
          jformFam c h N i wu wv = jform c h N i u v) ∧
      (∀ u ∈ jantzenLayer c h N i, ∀ v ∈ jantzenLayer c h N i,
        jform c h N i u v = jform c h N i v u) ∧
      (∀ (a : ℂ), ∀ u ∈ jantzenLayer c h N i, ∀ u' ∈ jantzenLayer c h N i,
        ∀ v ∈ jantzenLayer c h N i,
          jform c h N i (a • u + u') v = a * jform c h N i u v + jform c h N i u' v)) ∧
    (∀ (M n i : ℕ), 1 ≤ i → 0 < n →
      ∀ u ∈ jantzenLayer c h M i, ∀ v ∈ jantzenLayer c h (M + n) i,
        ∀ (u' : Nat.Partition (M + n) → ℂ) (v' : Nat.Partition M → ℂ),
          Verma.pbwCoord (c := c) (h := h) (M + n) u' =
            Verma.L (-(n : ℤ)) (Verma.pbwCoord (c := c) (h := h) M u) →
          Verma.pbwCoord (c := c) (h := h) M v' =
            Verma.L (n : ℤ) (Verma.pbwCoord (c := c) (h := h) (M + n) v) →
          u' ∈ jantzenLayer c h (M + n) i ∧ v' ∈ jantzenLayer c h M i ∧
            jform c h (M + n) i u' v = jform c h M i u v') ∧
    (∀ (N k : ℕ), 1 ≤ k → (gramLocal c h N).det ≠ 0 →
      (∃ s : Multiset ℕ, IsSmith (gramLocal c h N) s ∧ s.sup = k) →
        (∀ v ∈ jantzenLayer c h N k,
          (∀ u ∈ jantzenLayer c h N k, jform c h N k u v = 0) → v = 0) ∧
        ∀ w : Nat.Partition N → ℂ,
          (invCoeff (gramLocal c h N) (-(k : ℤ))).mulVec w ∈ jantzenLayer c h N k ∧
          ∀ u ∈ jantzenLayer c h N k,
            jform c h N k u ((invCoeff (gramLocal c h N) (-(k : ℤ))).mulVec w) = u ⬝ᵥ w) ∧
    (∀ N : ℕ,
      (∀ u ∈ jantzenLayer c h N 1, ∀ v ∈ jantzenLayer c h N 1,
        jform c h N 1 u v = cross1 (gramLocal c h N) v u) ∧
      (∀ u ∈ jantzenLayer c h N 2, ∀ v ∈ jantzenLayer c h N 2, ∀ u₁ : Nat.Partition N → ℂ,
        (coeffMat 0 (gramLocal c h N)).mulVec u₁ = -(coeffMat 1 (gramLocal c h N)).mulVec u →
          jform c h N 2 u v = cross2 (gramLocal c h N) v u u₁))

/-- Lemma 5.7 (`lem:singular-degree`), paper.tex l.711–716.  Let `w ∈ M(c,h)` be a nonzero
singular vector of level `ℓ ≥ 1`.  Then the coefficient `a_w` of `L_{-1}^ℓ|h⟩` in `w` is nonzero,
and `⟨w|V_d(1)|w⟩` is a polynomial in `d` of degree exactly `2ℓ` with leading coefficient `a_w²`.

Demand sheet.
- `c, h` complex, `ℓ ≥ 1` (l.712);
- `w` is given by its level-`ℓ` coordinates `p`; a singular vector of level `ℓ` has
  `L₀`-weight `h + ℓ` and so lies in the level-`ℓ` space; `IsSingular` contains `w ≠ 0` (l.712);
- conclusion: `a_w ≠ 0`; degree exactly `2ℓ` (identity, `natDegree`); leading coefficient equal
  to `a_w²` (l.713–715). -/
def Stmt_lem_singular_degree : Prop :=
  ∀ (c h : ℂ) (ℓ : ℕ), 1 ≤ ℓ → ∀ p : Nat.Partition ℓ → ℂ,
    Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) ℓ p) ℓ →
      p (onesPartition ℓ) ≠ 0 ∧
      (torusPolyForm c h p).natDegree = 2 * ℓ ∧
      (torusPolyForm c h p).leadingCoeff = p (onesPartition ℓ) ^ 2

/-- The summand `τ(d)/γ · H_{N-ℓ}(c⋆, λ+ℓ, d)` of equation (5.1) for a singular vector of level
`ℓ` with coordinates `x`, where `τ = ⟨w|V_d(1)|w⟩` and `γ = B^k(w,w)`; it is `0` when `ℓ > N`. -/
noncomputable def topTerm (c lam : ℂ) (N ℓ k : ℕ) (x : Nat.Partition ℓ → ℂ) : Kd :=
  if ℓ ≤ N then
    algebraMap ℂ[X] Kd (torusPolyForm c lam x) * RatFunc.C (jform c lam ℓ k x x)⁻¹ *
      RatFunc.eval (RingHom.id Kd) (pt (lam + (ℓ : ℂ))) (HN c (N - ℓ))
  else 0

/-- Theorem 5.9 (`thm:top-layer`), paper.tex l.820–834.  In the setting of Theorem 5.8, put
`ℓ_k = min(ℓ⁺_k, ℓ⁻_k)`, `μ^±_k = λ + ℓ^±_k`, `γ^±_k = B^k(w^±_k, w^±_k)`,
`τ^±_k(d) = ⟨w^±_k|V_d(1)|w^±_k⟩`.  Let `k ≥ 1` and `ℓ_k ≤ N < ℓ_{k+1}`.  Then `j_N(λ) = k`; for
each sign with `ℓ^±_k ≤ N`: `γ^±_k ≠ 0`, `det G_M(c⋆, μ^±_k) ≠ 0` for `M ≤ N - ℓ^±_k`,
`deg_d τ^±_k = 2ℓ^±_k`; and
`lim_{Δ→λ} (Δ-λ)^k H_N(c⋆,Δ,d) = ∑_{±: ℓ^±_k ≤ N} τ^±_k(d)/γ^±_k · H_{N-ℓ^±_k}(c⋆, μ^±_k, d)`.

Demand sheet.
- setting of Theorem 5.8: `MinimalSetting` (l.769–771) and any family `w^±_k` with the
  properties Theorem 5.8 states, `TopLayerSetting` (l.775–778); the vectors are used through
  their coordinates `xp`, `xm` at the levels `ℓ^±_k`;
- `k ≥ 1`, `ℓ_k ≤ N < ℓ_{k+1}` (l.825);
- `j_N(λ) = k`: identity (l.825);
- per sign, only when `ℓ^±_k ≤ N`: `γ ≠ 0`; `det G_M ≠ 0` for all `M ≤ N - ℓ^±_k`; degree
  exactly `2ℓ^±_k` (l.826–828);
- the limit: `d` indeterminate (`Kd = ℂ(d)`); read as pole order at most `k` and coefficient of
  `(Δ-λ)^{-k}` equal to the right side (l.830–832).  `H_{N-ℓ}` is evaluated at `μ^±_k`, where it
  is regular because of the determinant clause. -/
def Stmt_thm_top_layer : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      ∀ k N : ℕ, 1 ≤ k → ellMin p p' r s k ≤ N → N < ellMin p p' r s (k + 1) →
        jDepth p p' r s N = k ∧
        (∀ xp : Nat.Partition (ellPlus p p' r s k) → ℂ,
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k → ellPlus p p' r s k ≤ N →
            jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp ≠ 0 ∧
            (∀ M : ℕ, M ≤ N - ellPlus p p' r s k →
              (gram (kacC b) (kacH r s b + (ellPlus p p' r s k : ℂ)) M).det ≠ 0) ∧
            (torusPolyForm (kacC b) (kacH r s b) xp).natDegree = 2 * ellPlus p p' r s k) ∧
        (∀ xm : Nat.Partition (ellMinus p p' r s k) → ℂ,
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k → ellMinus p p' r s k ≤ N →
            jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm ≠ 0 ∧
            (∀ M : ℕ, M ≤ N - ellMinus p p' r s k →
              (gram (kacC b) (kacH r s b + (ellMinus p p' r s k : ℂ)) M).det ≠ 0) ∧
            (torusPolyForm (kacC b) (kacH r s b) xm).natDegree = 2 * ellMinus p p' r s k) ∧
        (∀ (xp : Nat.Partition (ellPlus p p' r s k) → ℂ)
            (xm : Nat.Partition (ellMinus p p' r s k) → ℂ),
          Verma.pbwCoord (ellPlus p p' r s k) xp = wp k →
          Verma.pbwCoord (ellMinus p p' r s k) xm = wm k →
            poleOrder (HN (kacC b) N) (pt (kacH r s b)) ≤ k ∧
            ppCoeff (HN (kacC b) N) (pt (kacH r s b)) k =
              topTerm (kacC b) (kacH r s b) N (ellPlus p p' r s k) k xp +
                topTerm (kacC b) (kacH r s b) N (ellMinus p p' r s k) k xm)

/-- Corollary 5.10 (`cor:top-layer-sharp`), paper.tex l.892–898.  In the setting of
Theorem 5.9, for every coprime pair `p, p' ≥ 2`, every interior Kac weight `λ = h_{r,s}(b⋆)` and
every level `N ≥ 1`, `H_N(c⋆,Δ,d)` has a pole of order exactly `j_N(λ)` at `Δ = λ`.

Demand sheet.
- `MinimalSetting` (interior weight labelled with `n₁ < pp'`, the labelling of Theorem 5.8);
- every `N ≥ 1` (l.896);
- `d` indeterminate: pole order over `ℂ(d)` (Remark 2.5, l.397–399);
- identity `poleOrder = j_N(λ)`, including the case `j_N(λ) = 0` (l.896–897). -/
def Stmt_cor_top_layer_sharp : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ N : ℕ, 1 ≤ N →
    poleOrder (HN (kacC b) N) (pt (kacH r s b)) = jDepth p p' r s N

end Virasoro
