import Virasoro.Proofs.Sec4Irr
import Virasoro.Proofs.SubringCoeff

/-!
# The partial-fraction coefficients lie in `ℚ(b⋆²)[d]`, and Theorem 4.3 from the generic recursion
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

/-- The ring homomorphism `k[d] → ℂ(d)` for a subfield `k ⊆ ℂ`. -/
noncomputable def polyHom (k : Subfield ℂ) : (↥k)[X] →+* Kd :=
  (algebraMap ℂ[X] Kd).comp (Polynomial.mapRingHom k.subtype)

theorem isPolyOver_of_mem {k : Subfield ℂ} {A : Kd} (h : A ∈ (polyHom k).range) :
    IsPolyOver k A := by
  obtain ⟨p, rfl⟩ := h
  exact ⟨p.map k.subtype, fun n => by simp [Polynomial.coeff_map], rfl⟩

theorem polyHom_C (k : Subfield ℂ) (x : ↥k) : polyHom k (C x) = RatFunc.C (x : ℂ) := by
  simp [polyHom, RatFunc.algebraMap_C]

theorem polyHom_X (k : Subfield ℂ) : polyHom k X = dvar := by
  simp [polyHom, RatFunc.algebraMap_X]

theorem kacH_mem (b : ℂ) (hb : b ≠ 0) (r s : ℤ) : kacH r s b ∈ Qb2 b := by
  have hb2 : b ^ 2 ∈ Qb2 b := Subfield.subset_closure (Set.mem_singleton _)
  have e : kacH r s b = (((1 - r ^ 2 : ℤ) : ℂ) * b ^ 2 + ((2 - 2 * r * s : ℤ) : ℂ) +
      ((1 - s ^ 2 : ℤ) : ℂ) * (b ^ 2)⁻¹) * (((4 : ℕ) : ℂ))⁻¹ := by
    unfold kacH
    push_cast
    field_simp
    ring
  rw [e]
  exact (Qb2 b).mul_mem ((Qb2 b).add_mem ((Qb2 b).add_mem
    ((Qb2 b).mul_mem (intCast_mem _ _) hb2) (intCast_mem _ _))
    ((Qb2 b).mul_mem (intCast_mem _ _) ((Qb2 b).inv_mem hb2))) ((Qb2 b).inv_mem (natCast_mem _ _))

theorem kacC_mem (b : ℂ) (hb : b ≠ 0) : kacC b ∈ Qb2 b := by
  have hb2 : b ^ 2 ∈ Qb2 b := Subfield.subset_closure (Set.mem_singleton _)
  have e : kacC b = ((13 : ℕ) : ℂ) + ((6 : ℕ) : ℂ) * b ^ 2 + ((6 : ℕ) : ℂ) * (b ^ 2)⁻¹ := by
    unfold kacC
    push_cast
    field_simp
    ring
  rw [e]
  exact (Qb2 b).add_mem ((Qb2 b).add_mem (natCast_mem _ _)
    ((Qb2 b).mul_mem (natCast_mem _ _) hb2))
    ((Qb2 b).mul_mem (natCast_mem _ _) ((Qb2 b).inv_mem hb2))

theorem lcoeff_sum {K : Type*} [Field K] {α : Type*} (s : Finset α) (f : α → RatFunc K) (μ : K)
    (n : ℤ) : lcoeff (∑ i ∈ s, f i) μ n = ∑ i ∈ s, lcoeff (f i) μ n := by
  unfold lcoeff
  rw [expandAt_eq, map_sum, HahnSeries.coeff_sum]
  rfl

theorem lcoeff_intCast_mul {K : Type*} [Field K] (η : ℤ) (f : RatFunc K) (μ : K) (n : ℤ) :
    lcoeff ((η : RatFunc K) * f) μ n = (η : K) * lcoeff f μ n := by
  unfold lcoeff
  rw [expandAt_eq, map_mul, map_intCast]
  have : ((η : K⸨X⸩)) = HahnSeries.single 0 (η : K) :=
    (map_intCast (HahnSeries.C : K →+* K⸨X⸩) η).symm
  rw [this, HahnSeries.coeff_single_zero_mul]
  rfl

/-- Every Laurent coefficient of `F_M(c⋆,Δ,d)` at a point of `ℚ(b⋆²)` lies in `ℚ(b⋆²)[d]`. -/
theorem lcoeff_FN_mem (b : ℂ) (hb : b ≠ 0) (M : ℕ) {lam : ℂ} (hlam : lam ∈ Qb2 b) (n : ℤ) :
    lcoeff (FN (kacC b) M) (pt lam) n ∈ (polyHom (Qb2 b)).range := by
  set k := Qb2 b with hk
  have : CharZero ↥k := RingHom.charZero k.subtype
  let c' : ↥k := ⟨kacC b, kacC_mem b hb⟩
  let j₀ : ↥k →+* Kd := (RatFunc.C : ℂ →+* Kd).comp k.subtype
  have hj₀ : ∀ x : ↥k, j₀ x = polyHom k (C x) := fun x => (polyHom_C k x).symm
  -- numerator: coefficients in `k[d]`
  have hnum : ∀ i, (numR (C (RatFunc.C (kacC b) : Kd)) X (C dvar) M).coeff i ∈ (polyHom k).range := by
    intro i
    have h := map_numR (Polynomial.mapRingHom (polyHom k)) (C (C c')) (X : (↥k)[X][X]) (C X) M
    simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X, polyHom_C, polyHom_X] at h
    have hc : ((c' : ↥k) : ℂ) = kacC b := rfl
    rw [hc] at h
    rw [← h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  -- denominator: coefficients in `k`
  have hden : ∀ i, (detR (C (RatFunc.C (kacC b) : Kd)) X M).coeff i ∈ j₀.fieldRange := by
    intro i
    have h := map_detR (Polynomial.mapRingHom j₀) (C c') (X : (↥k)[X]) M
    simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at h
    have hc : j₀ c' = RatFunc.C (kacC b) := rfl
    rw [hc] at h
    rw [← h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  have hsub : ∀ x ∈ j₀.fieldRange, x ∈ (polyHom k).range := by
    rintro x ⟨y, rfl⟩
    exact ⟨C y, (hj₀ y).symm⟩
  have hμ : pt lam ∈ j₀.fieldRange := ⟨⟨lam, hlam⟩, rfl⟩
  have hQ0 : detR (C (RatFunc.C (kacC b) : Kd)) X M ≠ 0 := gramPoly_det_ne_zero _ M
  have := lcoeff_div_mem (polyHom k).range j₀.fieldRange hsub hnum hden hQ0 hμ n
  rw [FN, Frat_eq]
  exact this

/-- The partial-fraction coefficients `A⋆_{λ,k,N}(d)` lie in `ℚ(b⋆²)[d]`. -/
theorem astar_isPolyOver {b : ℂ} (hb : b ≠ 0) {N : ℕ} {lam : ℂ} (hlam : lam ∈ Lam N b) (k : ℕ) :
    IsPolyOver (Qb2 b) (Astar b N lam k) := by
  classical
  apply isPolyOver_of_mem
  have hlam' : lam ∈ Qb2 b := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hlam
    exact kacH_mem b hb _ _
  unfold Astar ppCoeff HN Hrat
  rw [lcoeff_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [lcoeff_intCast_mul]
  refine Subring.mul_mem _ (intCast_mem _ _) ?_
  exact lcoeff_FN_mem b hb (N - j) hlam' _

/-- Theorem 4.3 from the generic recursion in the form consumed by its proof
(`GenericRecursionUniform`, Proposition 6.5 for the formal germ `b = b⋆ + t`). -/
theorem thm_general_confluence (hrec : GenericRecursionUniform) : Stmt_thm_general_confluence := by
  intro b hb
  refine ⟨fun N hN => ⟨confluence_eq hrec hb hN, fun lam hlam k hk => ?_,
      fun lam hlam => (confluence_moments hrec hb hN hlam).2⟩,
    lem_precision_budget b hb, confluence_series hrec hb,
    fun hq N hN => confluence_irrational hrec hb hq hN⟩
  have h := (confluence_moments hrec hb hN hlam).1 k hk
  exact ⟨h, by rw [h]; exact astar_isPolyOver hb hlam k⟩

example (hrec : GenericRecursionUniform) : Stmt_thm_general_confluence :=
  thm_general_confluence hrec

end Virasoro
