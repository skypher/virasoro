import Virasoro.Proofs.TopLayerArith
import Virasoro.Proofs.Naturality
import Virasoro.JantzenForm
import Virasoro.Orbit

/-!
# Arithmetic and base change for Corollary 5.10

* `jDepth_range`: `k = j_N(λ) ≥ 1` gives `ℓ_k ≤ N < ℓ_{k+1}` (paper.tex l.901–902);
* `ellPlus_momentum`, `ellMinus_momentum`: `λ + ℓ^±_k = (m² - (p'-p)²)/(4pp')` for an integer `m`,
  the form in which Proposition 6.8(iii) takes the weight `μ` (l.1193);
* `HpolyD_map`: `H_M(c,Δ,d)` as a polynomial in `d` commutes with a field embedding.
-/

namespace Virasoro

open Polynomial

section Depth

variable {p p' r s : ℕ}

theorem jDepth_range (hp : 2 ≤ p) (hp' : 2 ≤ p') (hr : 0 < r) (hrp : r < p) (hs : 0 < s)
    (hsp : s < p') {N : ℕ} (hk : 1 ≤ jDepth p p' r s N) :
    ellMin p p' r s (jDepth p p' r s N) ≤ N ∧ N < ellMin p p' r s (jDepth p p' r s N + 1) := by
  have hmem : jDepth p p' r s N ∈ (Finset.Icc 1 N).filter fun k =>
      min (ellPlus p p' r s k) (ellMinus p p' r s k) ≤ N := by
    have hne : ((Finset.Icc 1 N).filter fun k =>
        min (ellPlus p p' r s k) (ellMinus p p' r s k) ≤ N).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      unfold jDepth at hk
      rw [h0, Finset.sup_empty] at hk
      exact absurd hk (by simp)
    obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup _ hne id
    unfold jDepth
    rw [hsup]
    exact hi
  refine ⟨(Finset.mem_filter.1 hmem).2, ?_⟩
  by_contra hcon
  have h1 : ellMin p p' r s (jDepth p p' r s N + 1) ≤ N := not_lt.1 hcon
  have h3 := le_ellPlus (r := r) (k := jDepth p p' r s N + 1) hp hp' hr hs hsp (by omega)
  have h4 := le_ellMinus (r := r) (k := jDepth p p' r s N + 1) hp hp' hrp hs hsp (by omega)
  have h5 : jDepth p p' r s N + 1 ≤ ellMin p p' r s (jDepth p p' r s N + 1) := le_min h3 h4
  have h6 : jDepth p p' r s N + 1 ≤ jDepth p p' r s N :=
    Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, h1⟩)
  omega

theorem ellPlus_momentum (hsp : s < p') (k : ℕ) :
    ∃ m : ℤ, m ^ 2 = ((p' : ℤ) * r - (p : ℤ) * s) ^ 2 +
      4 * p * p' * (ellPlus p p' r s k : ℤ) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · refine ⟨2 * j * p * p' + ((p' : ℤ) * r - (p : ℤ) * s), ?_⟩
    rw [ellPlus_even_cast hsp j]
    ring
  · refine ⟨2 * j * p * p' + ((p' : ℤ) * r + (p : ℤ) * s), ?_⟩
    rw [ellPlus_odd_cast j]
    ring

theorem ellMinus_momentum (hrp : r < p) (hsp : s < p') (k : ℕ) :
    ∃ m : ℤ, m ^ 2 = ((p' : ℤ) * r - (p : ℤ) * s) ^ 2 +
      4 * p * p' * (ellMinus p p' r s k : ℤ) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · refine ⟨2 * j * p * p' - ((p' : ℤ) * r - (p : ℤ) * s), ?_⟩
    rw [ellMinus_even_cast hrp j]
    ring
  · refine ⟨2 * (j + 1) * p * p' - ((p' : ℤ) * r + (p : ℤ) * s), ?_⟩
    rw [ellMinus_odd_cast hrp hsp j]
    ring

end Depth

section Minimal

variable {p p' : ℕ} {b : ℂ}

theorem inv_sq_min (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) :
    b ≠ 0 ∧ b⁻¹ ^ 2 = -(p : ℂ) / p' := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, eq_comm, div_eq_zero_iff, neg_eq_zero] at hb
    tauto
  refine ⟨hb0, ?_⟩
  rw [inv_pow, hb]
  field_simp

/-- `c⋆ = 1 - 6(p'-p)²/(pp')`. -/
theorem kacC_min (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) :
    kacC b = ((1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p') : ℚ) : ℂ) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  obtain ⟨hb0, hbi⟩ := inv_sq_min hp hp' hb
  have h1 : (b + b⁻¹) ^ 2 = b ^ 2 + 2 + b⁻¹ ^ 2 := by
    field_simp
    ring
  rw [kacC, h1, hb, hbi]
  push_cast
  field_simp
  ring

/-- `h_{r,s}(b⋆) + ℓ = (m² - (p'-p)²)/(4pp')` when `m² = n₀² + 4pp'ℓ`. -/
theorem kacH_min_add (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (r s ℓ : ℕ) {m : ℤ}
    (hm : m ^ 2 = ((p' : ℤ) * r - (p : ℤ) * s) ^ 2 + 4 * p * p' * (ℓ : ℤ)) :
    kacH r s b + (ℓ : ℂ) = ((((m : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p') : ℚ) : ℂ) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  obtain ⟨hb0, hbi⟩ := inv_sq_min hp hp' hb
  have h1 : (b + b⁻¹) ^ 2 = b ^ 2 + 2 + b⁻¹ ^ 2 := by
    field_simp
    ring
  have h2 : ((r : ℂ) * b + (s : ℂ) * b⁻¹) ^ 2 =
      (r : ℂ) ^ 2 * b ^ 2 + 2 * r * s + (s : ℂ) ^ 2 * b⁻¹ ^ 2 := by
    field_simp
    ring
  have hmc : (m : ℂ) ^ 2 = ((p' : ℂ) * r - (p : ℂ) * s) ^ 2 + 4 * p * p' * (ℓ : ℂ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hm
  rw [kacH]
  push_cast
  rw [h1, h2, hb, hbi, hmc]
  field_simp
  ring

end Minimal

section BaseChange

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] (φ : K →+* L)

theorem gram_inv_map (c Δ : K) (M : ℕ) :
    (gram (φ c) (φ Δ) M)⁻¹ = ((gram c Δ M)⁻¹).map φ := by
  have hdet : ((gram c Δ M).map φ).det = φ (gram c Δ M).det :=
    (RingHom.map_det φ (gram c Δ M)).symm
  have hadj : ((gram c Δ M).map φ).adjugate = ((gram c Δ M).adjugate).map φ :=
    (RingHom.map_adjugate φ (gram c Δ M)).symm
  rw [gram_map φ c Δ M, Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv',
    hdet, hadj]
  ext Y Y'
  simp [Matrix.smul_apply, map_inv₀]

theorem FpolyD_map (c Δ : K) (M : ℕ) : FpolyD (φ c) (φ Δ) M = (FpolyD c Δ M).map φ := by
  have ht : torus (C (φ c)) (C (φ Δ)) (X : L[X]) M =
      (torus (C c) (C Δ) (X : K[X]) M).map (mapRingHom φ) := by
    have := torus_map (mapRingHom φ) (C c) (C Δ) (X : K[X]) M
    simp only [coe_mapRingHom, map_C, map_X] at this
    exact this
  unfold FpolyD
  rw [gram_inv_map, ht, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [Polynomial.map_mul, map_C, Matrix.map_apply, Matrix.map_apply, coe_mapRingHom]

theorem HpolyD_map (c Δ : K) (N : ℕ) : HpolyD (φ c) (φ Δ) N = (HpolyD c Δ N).map φ := by
  unfold HpolyD
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, FpolyD_map, Polynomial.map_intCast]

end BaseChange

end Virasoro
