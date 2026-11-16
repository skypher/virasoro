import Virasoro.Statements.Prelude
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Frozen statements: Section 5, general part (Lemma 5.1 – Lemma 5.10)
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial Module

/-- The first crossing form `β₁` is nondegenerate on `K₁ = ker G(0)`. -/
def Cross1Nondeg {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι (PowerSeries ℂ)) : Prop :=
  ∀ v ∈ ker0 G, (∀ u ∈ ker0 G, cross1 G u v = 0) → v = 0

/-- The second crossing form `β₂` is nondegenerate on `K₂`. -/
def Cross2Nondeg {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι (PowerSeries ℂ)) : Prop :=
  ∀ v ∈ ker2 G,
    (∀ u ∈ ker2 G, ∀ v₁ : ι → ℂ,
      (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v → cross2 G u v v₁ = 0) → v = 0

/-- Lemma 5.1 (`lem:smith`).  Let `R = ℂ[[x]]` and let `G(x) ∈ M_m(R)` have nonzero determinant
and Smith exponents `0 ≤ e₁ ≤ ⋯ ≤ e_m`.  Then `ord_x det G = ∑ e_i`,
`dim ker G(0) = #{i : e_i > 0}`, and the pole order of `G(x)⁻¹` is `e_m`.  In particular, if
`ord_x det G = dim ker G(0) = k`, then every positive Smith exponent equals `1` and `G⁻¹` has at
most a simple pole.
The exponents are recorded as the multiset `s`; `e_m` is its maximum `s.sup`. -/
def Stmt_lem_smith : Prop :=
  ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) (PowerSeries ℂ)) (s : Multiset ℕ),
    G.det ≠ 0 → IsSmith G s →
      G.det.order = ((s.sum : ℕ) : ℕ∞) ∧
      finrank ℂ (ker0 G) = (s.filter fun e => 0 < e).card ∧
      poleOrderInv G = s.sup ∧
      ∀ k : ℕ, G.det.order = (k : ℕ∞) → finrank ℂ (ker0 G) = k →
        (∀ e ∈ s, 0 < e → e = 1) ∧ poleOrderInv G ≤ 1

/-- Proposition 5.2 (`prop:transverse-residue`).  Let `G(x)` be a symmetric matrix over
`ℂ[[x]]` with nonzero determinant, `K = ker G(0)`, and `β(u,v) = uᵀ G'(0) v` on `K`.  If `β` is
nondegenerate, then `G(x)⁻¹` has at most a simple pole and `Res_{x=0} G(x)⁻¹ = ι β⁻¹ ι^*`.
Moreover `β` is nondegenerate iff `ord_x det G = dim K`.
Reading convention: `R = ι β⁻¹ ι^*` means that for every `w`, `R w ∈ K` and
`β(u, R w) = uᵀ w` for all `u ∈ K`; for nondegenerate `β` this determines `R`. -/
def Stmt_prop_transverse_residue : Prop :=
  ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) (PowerSeries ℂ)), G.IsSymm → G.det ≠ 0 →
    (Cross1Nondeg G →
      poleOrderInv G ≤ 1 ∧
      ∀ w : Fin m → ℂ, (invCoeff G (-1)).mulVec w ∈ ker0 G ∧
        ∀ u ∈ ker0 G, cross1 G u ((invCoeff G (-1)).mulVec w) = u ⬝ᵥ w) ∧
    (Cross1Nondeg G ↔ G.det.order = ((finrank ℂ (ker0 G) : ℕ) : ℕ∞))

/-- Proposition 5.3 (`prop:two-step-residue`).  Let `G(x) = G₀ + x G₁ + x² G₂ + O(x³)` be as in
Proposition 5.2, `K₁ = ker G₀`, `β₁(u,v) = uᵀ G₁ v`, `K₂ = ker(β₁ : K₁ → K₁^*)`.  For `v ∈ K₂`
choose `v₁` with `G₀ v₁ = - G₁ v` and put `β₂(u,v) = uᵀ (G₂ v + G₁ v₁)` on `K₂`.  Then `v₁`
exists, `β₂` is independent of its choice, and `β₂` is symmetric.  Without any nondegeneracy
assumption, `#{i : e_i ≥ 1} = dim K₁` and `#{i : e_i ≥ 2} = dim K₂`.  `β₂` is nondegenerate iff
all Smith exponents are at most `2`, and in that case `[x⁻²] G(x)⁻¹ = ι₂ β₂⁻¹ ι₂^*`.
Reading convention for `ι₂ β₂⁻¹ ι₂^*` as in `Stmt_prop_transverse_residue`. -/
def Stmt_prop_two_step_residue : Prop :=
  ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) (PowerSeries ℂ)), G.IsSymm → G.det ≠ 0 →
    (∀ v ∈ ker2 G, ∃ v₁ : Fin m → ℂ, (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v) ∧
    (∀ v ∈ ker2 G, ∀ v₁ v₁' : Fin m → ℂ,
      (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v →
      (coeffMat 0 G).mulVec v₁' = -(coeffMat 1 G).mulVec v →
      ∀ u ∈ ker2 G, cross2 G u v v₁ = cross2 G u v v₁') ∧
    (∀ u ∈ ker2 G, ∀ v ∈ ker2 G, ∀ u₁ v₁ : Fin m → ℂ,
      (coeffMat 0 G).mulVec u₁ = -(coeffMat 1 G).mulVec u →
      (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec v →
      cross2 G u v v₁ = cross2 G v u u₁) ∧
    (∀ s : Multiset ℕ, IsSmith G s →
      (s.filter fun e => 1 ≤ e).card = finrank ℂ (ker0 G) ∧
      (s.filter fun e => 2 ≤ e).card = finrank ℂ (ker2 G) ∧
      (Cross2Nondeg G ↔ ∀ e ∈ s, e ≤ 2)) ∧
    (Cross2Nondeg G →
      ∀ w : Fin m → ℂ, (invCoeff G (-2)).mulVec w ∈ ker2 G ∧
        ∀ u ∈ ker2 G, ∀ v₁ : Fin m → ℂ,
          (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec ((invCoeff G (-2)).mulVec w) →
          cross2 G u ((invCoeff G (-2)).mulVec w) v₁ = u ⬝ᵥ w)

/-- Corollary 5.4 (`cor:det-overcounts`).  At a collided Kac weight `λ` (a weight of
`Λ_N(b⋆)` carried by at least two labels of level at most `N`), the multiplicity of the factor
`Δ - λ` in `det G_N` is the sum of the positive local Smith exponents, and the inverse Shapovalov
pole order is their maximum. -/
def Stmt_cor_det_overcounts : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ (N : ℕ) (lam : ℂ), 2 ≤ (collClass N b lam).card →
    ∀ s : Multiset ℕ, IsSmith (gramLocal (kacC b) lam N) s →
      (gramPoly (kacC b) N).det.rootMultiplicity lam = (s.filter fun e => 0 < e).sum ∧
      poleOrderInv (gramLocal (kacC b) lam N) = s.sup

/-- Lemma 5.6 (`lem:jantzen-smith`).  Suppose `det G_N(c,h+x) ≢ 0`, with local Smith exponents
`e₁, …, e_{p(N)}` at `x = 0`.  Then `dim J^i_N(c,h) = #{j : e_j ≥ i}` for `i ≥ 1` and
`∑_{i≥1} dim J^i_N(c,h) = ord_x det G_N(c,h+x)`.  Each `J^i(c,h)` is a submodule of `M(c,h)`,
and `J¹(c,h)` is the radical of the Shapovalov form. -/
def Stmt_lem_jantzen_smith : Prop :=
  ∀ c h : ℂ,
    (∀ (N : ℕ) (s : Multiset ℕ), (gramLocal c h N).det ≠ 0 → IsSmith (gramLocal c h N) s →
      (∀ i : ℕ, 1 ≤ i → finrank ℂ (jantzenLayer c h N i) = (s.filter fun e => i ≤ e).card) ∧
      (((∑ᶠ i : ℕ, if 1 ≤ i then finrank ℂ (jantzenLayer c h N i) else 0 : ℕ) : ℕ∞) =
        (gramLocal c h N).det.order)) ∧
    ((∀ N : ℕ, (gramLocal c h N).det ≠ 0) →
      (∀ i : ℕ, Verma.IsVirSubmodule (jantzen c h i)) ∧
      ∀ B : Verma ℂ c h →ₗ[ℂ] Verma ℂ c h →ₗ[ℂ] ℂ, Verma.IsShapovalov B →
        (jantzen c h 1 : Set (Verma ℂ c h)) = {v | ∀ u, B u v = 0})

/-- The level `ℓ⁺_k` of Theorem 5.7: `ℓ⁺_{2j} = j (j p p' + n₀)`, `n₀ = p' r - p s`, and
`ℓ⁺_{2j+1} = (r + j p)(s + j p')`. -/
def ellPlus (p p' r s k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (((k / 2 : ℕ) : ℤ) * (((k / 2 : ℕ) : ℤ) * p * p' + ((p' : ℤ) * r - (p : ℤ) * s))).toNat
  else (r + (k / 2) * p) * (s + (k / 2) * p')

/-- The level `ℓ⁻_k` of Theorem 5.7: `ℓ⁻_{2j} = j (j p p' - n₀)` and
`ℓ⁻_{2j+1} = ((j+1) p - r)((j+1) p' - s)`. -/
def ellMinus (p p' r s k : ℕ) : ℕ :=
  if k % 2 = 0 then
    (((k / 2 : ℕ) : ℤ) * (((k / 2 : ℕ) : ℤ) * p * p' - ((p' : ℤ) * r - (p : ℤ) * s))).toNat
  else ((k / 2 + 1) * p - r) * ((k / 2 + 1) * p' - s)

/-- The Jantzen depth `j_N(λ) = max({0} ∪ {k ≥ 1 : min(ℓ⁺_k, ℓ⁻_k) ≤ N})`.  Since
`ℓ^±_k ≥ k`, the maximum is taken over `1 ≤ k ≤ N`. -/
def jDepth (p p' r s N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter fun k => min (ellPlus p p' r s k) (ellMinus p p' r s k) ≤ N).sup id

/-- Theorem 5.7 (`thm:jantzen-smith`).  Let `p, p' ≥ 2` be coprime, `b⋆² = -p'/p`,
`λ = h_{r,s}(b⋆)` with `0 < r < p`, `0 < s < p'`, labelled so that `n₁ = p' r + p s < p p'`.
Then `M(c⋆,λ)` has, for every `k ≥ 1`, singular vectors `w^±_k` of levels `ℓ^±_k`, and with
`W^±_k = U(Vir_-) w^±_k`, `J^i(c⋆,λ) = W⁺_i + W⁻_i` for `i ≥ 1`.  Consequently, at every level
`N`, the number of local Smith exponents of `G_N(c⋆,λ+x)` that are at least `i` is
`dim (W⁺_i + W⁻_i)_N`; `G_N(c⋆,Δ)⁻¹` has a pole of order exactly `j_N(λ)` at `Δ = λ`, and
`F_N(c⋆,Δ,d)`, `H_N(c⋆,Δ,d)` have poles of order at most `j_N(λ)` there. -/
def Stmt_thm_jantzen_smith : Prop :=
  ∀ p p' r s : ℕ, 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → 0 < r → r < p → 0 < s → s < p' →
    p' * r + p * s < p * p' →
    ∀ b : ℂ, b ^ 2 = -(p' : ℂ) / p →
      ∃ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b),
        (∀ k : ℕ, 1 ≤ k →
          Verma.IsSingular (wp k) (ellPlus p p' r s k) ∧
          Verma.IsSingular (wm k) (ellMinus p p' r s k)) ∧
        (∀ i : ℕ, 1 ≤ i →
          jantzen (kacC b) (kacH r s b) i = Verma.negSpan (wp i) ⊔ Verma.negSpan (wm i)) ∧
        (∀ (N : ℕ) (e : Multiset ℕ), IsSmith (gramLocal (kacC b) (kacH r s b) N) e →
          ∀ i : ℕ, 1 ≤ i →
            (e.filter fun x => i ≤ x).card =
              finrank ℂ ↥((Verma.negSpan (wp i) ⊔ Verma.negSpan (wm i)) ⊓ Verma.level N)) ∧
        (∀ N : ℕ,
          poleOrderInv (gramLocal (kacC b) (kacH r s b) N) = jDepth p p' r s N ∧
          poleOrder (FN (kacC b) N) (pt (kacH r s b)) ≤ jDepth p p' r s N ∧
          poleOrder (HN (kacC b) N) (pt (kacH r s b)) ≤ jDepth p p' r s N)

/-- Lemma 5.9 (`lem:singular-factorization`).  Let `χ ∈ M(c,h)` be a singular vector of level
`ℓ` and `P_χ(d) = ⟨χ|V_d(1)|χ⟩`.  For partitions `Y, Y'` of the same integer `m`,
`⟨χ| L_Y V_d(1) L_{-Y'} |χ⟩ = P_χ(d) ρ_m(c,h+ℓ,d)_{Y,Y'}`.
Reading convention: `⟨χ| L_Y V_d(1) L_{-Y'} |χ⟩ = T(L_{-Y} χ, L_{-Y'} χ)` for the pairing
`T(u,v) = ⟨u|V_d(1)|v⟩`; the identity is stated for every complex value of `d`. -/
def Stmt_lem_singular_factorization : Prop :=
  ∀ (c h d : ℂ) (T : Verma ℂ c h →ₗ[ℂ] Verma ℂ c h →ₗ[ℂ] ℂ), Verma.IsPrimaryPairing d T →
    ∀ (χ : Verma ℂ c h) (ℓ : ℕ), Verma.IsSingular χ ℓ →
      ∀ (m : ℕ) (Y Y' : Nat.Partition m),
        T (VirEnv.negOp c Y.word • χ) (VirEnv.negOp c Y'.word • χ) =
          T χ χ * torus c (h + (ℓ : ℂ)) d m Y Y'

/-- Lemma 5.10 (`lem:singular-crossing`).  Fix `c` and let `χ = P|h₀⟩ ∈ M(c,h₀)` be singular
of level `ℓ`, where the PBW operator `P ∈ U(Vir_-)` is held fixed as `h` varies, and
`β_χ = d/dh ⟨h|ω(P)P|h⟩ |_{h=h₀}`.  For partitions `Y, Y'` of `m`,
`d/dh ⟨h| ω(P) L_Y L_{-Y'} P |h⟩ |_{h=h₀} = β_χ G_m(c,h₀+ℓ)_{Y,Y'}`.
Here `P = ∑_Z p_Z L_{-Z}` with fixed coefficients `p`, and
`⟨h| L_Z L_Y L_{-Y'} L_{-Z'} |h⟩` is `gramWord` on the concatenated words. -/
def Stmt_lem_singular_crossing : Prop :=
  ∀ (c h₀ : ℂ) (ℓ : ℕ) (p : Nat.Partition ℓ → ℂ),
    Verma.IsSingular (Verma.pbwCoord (c := c) (h := h₀) ℓ p) ℓ →
      ∀ (m : ℕ) (Y Y' : Nat.Partition m),
        (derivative (∑ Z : Nat.Partition ℓ, ∑ Z' : Nat.Partition ℓ,
            C (p Z) * C (p Z') *
              gramWord (C c) (X : ℂ[X]) (Y.word ++ Z.word) (Y'.word ++ Z'.word))).eval h₀ =
          crossScalar c h₀ p * gram c (h₀ + (ℓ : ℂ)) m Y Y'

end Virasoro
