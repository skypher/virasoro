import Virasoro.Sphere.Proofs.Sec3LamMinor
import Virasoro.Sphere.Proofs.Sec3LamOps
import Virasoro.Sphere.Proofs.Sec3FockLevel

/-!
# Sphere paper Lemma 3.3(i): the level-`m` system `𝒟_m(λ)S_m = R_m` (proof of Lemma 3.3(i))

At oscillator level `m - k` the terms of (3.3) that involve `S_m` are
`D_k(λ)S_m = (i + μk/λ)∂_k S_m + ∑ nσ_n∂_{n+k}S_m - (1/4λ²)∑∂_n∂_{k-n}S_m`
(`linLamL k a b` with `a = i + μk/λ`, `b = 1/(4λ²)`).  The coefficient of `σ^β`, `lvl β = m - k`,
of `linLamL k a b T` reads only the level-`m` coefficients of `T` (`coeff_linLam_level`), so the
equations at all `(k, β)` form a rectangular linear system in the level-`m` coefficients.
Its value at `λ⁻¹ = 0` is `𝒟_m(∞)`, `D_k(∞) = i∂_k + ∑ nσ_n∂_{n+k}`, which is injective by the
lowest-degree argument (`Dinf_injective`).

Consumer: `regular_of_pde` (`Sec3LamRegular.lean`).
-/

namespace Virasoro.Sphere

open Finset

section Lin

variable {A : Type*} [CommRing A]

/-- `∂/∂σ_n` as an `A`-linear map. -/
noncomputable def pdL (n : ℕ) : MvPowerSeries ℕ+ A →ₗ[A] MvPowerSeries ℕ+ A :=
  (MvPowerSeries.pderiv A n.toPNat').toLinearMap

/-- `∑ nσ_n ∂_{n+k}` as an `A`-linear map. -/
noncomputable def shiftL (k : ℕ) : MvPowerSeries ℕ+ A →ₗ[A] MvPowerSeries ℕ+ A where
  toFun := shiftA k
  map_add' := shiftA_add k
  map_smul' := shiftA_smul k

/-- `D_k = a∂_k + ∑ nσ_n∂_{n+k} - b∑_{n<k}∂_n∂_{k-n}`. -/
noncomputable def linLamL (k : ℕ) (a b : A) : MvPowerSeries ℕ+ A →ₗ[A] MvPowerSeries ℕ+ A :=
  a • pdL k + shiftL k - b • ∑ n ∈ Icc 1 (k - 1), (pdL n).comp (pdL (k - n))

theorem linLamL_apply (k : ℕ) (a b : A) (T : MvPowerSeries ℕ+ A) :
    linLamL k a b T =
      a • pdA k T + shiftA k T - b • ∑ n ∈ Icc 1 (k - 1), pdA n (pdA (k - n) T) := by
  simp [linLamL, LinearMap.sum_apply, pdL, shiftL, pdA]

theorem lvl_sub_single {β : ℕ+ →₀ ℕ} {n : ℕ+} (hn : n ∈ β.support) :
    lvl (β - Finsupp.single n 1) + (n : ℕ) = lvl β := by
  have e := congrArg lvl (sub_add_single hn)
  rw [lvl_add, lvl_single] at e
  exact e

/-- The coefficient of `σ^β`, `lvl β + k = m`, of `D_k T` vanishes when all level-`m`
coefficients of `T` vanish. -/
theorem coeff_linLam_eq_zero {k m : ℕ} (hk : 1 ≤ k) (a b : A) (U : MvPowerSeries ℕ+ A)
    (hU : ∀ α, lvl α = m → MvPowerSeries.coeff α U = 0) (β : ℕ+ →₀ ℕ) (hβ : lvl β + k = m) :
    MvPowerSeries.coeff β (linLamL k a b U) = 0 := by
  rw [linLamL_apply]
  simp only [map_sub, map_add, MvPowerSeries.coeff_smul, map_sum]
  have hk' : ((k.toPNat' : ℕ+) : ℕ) = k := PNat.toPNat'_coe hk
  have t1 : MvPowerSeries.coeff β (pdA k U) = 0 := by
    rw [coeff_pdA, hU _ (by rw [lvl_add, lvl_single, hk']; exact hβ), zero_mul]
  have t2 : MvPowerSeries.coeff β (shiftA k U) = 0 := by
    rw [coeff_shiftA]
    refine sum_eq_zero fun n hn => ?_
    have hn' := lvl_sub_single hn
    have hnk : ((((n : ℕ) + k).toPNat' : ℕ+) : ℕ) = (n : ℕ) + k := PNat.toPNat'_coe (by omega)
    rw [coeff_pdA, hU _ (by rw [lvl_add, lvl_single, hnk]; omega), zero_mul, mul_zero]
  have t3 : ∀ n ∈ Icc 1 (k - 1), MvPowerSeries.coeff β (pdA n (pdA (k - n) U)) = 0 := by
    intro n hn
    have hn' := mem_Icc.1 hn
    have h1 : ((n.toPNat' : ℕ+) : ℕ) = n := PNat.toPNat'_coe hn'.1
    have h2 : (((k - n).toPNat' : ℕ+) : ℕ) = k - n := PNat.toPNat'_coe (by omega)
    rw [coeff_pdA, coeff_pdA,
      hU _ (by rw [lvl_add, lvl_add, lvl_single, lvl_single, h1, h2]; omega), zero_mul, zero_mul]
  rw [t1, t2, sum_eq_zero t3]
  simp

/-- The coefficient of `σ^β`, `lvl β + k = m`, of `D_k T` is a linear combination of the
level-`m` coefficients of `T`. -/
theorem coeff_linLam_level {k m : ℕ} (hk : 1 ≤ k) (a b : A) (T : MvPowerSeries ℕ+ A)
    [Fintype {α : ℕ+ →₀ ℕ // lvl α = m}] (β : ℕ+ →₀ ℕ) (hβ : lvl β + k = m) :
    MvPowerSeries.coeff β (linLamL k a b T) =
      ∑ α : {α : ℕ+ →₀ ℕ // lvl α = m},
        MvPowerSeries.coeff α.1 T *
          MvPowerSeries.coeff β (linLamL k a b (MvPowerSeries.monomial α.1 1)) := by
  classical
  set Tm : MvPowerSeries ℕ+ A :=
    ∑ α : {α : ℕ+ →₀ ℕ // lvl α = m}, MvPowerSeries.coeff α.1 T • MvPowerSeries.monomial α.1 1
    with hTm
  have hU : ∀ α, lvl α = m → MvPowerSeries.coeff α (T - Tm) = 0 := by
    intro α hα
    rw [map_sub, hTm, map_sum, Fintype.sum_eq_single ⟨α, hα⟩]
    · simp [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_monomial]
    · intro a ha
      rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_monomial, if_neg, mul_zero]
      intro h
      exact ha (Subtype.ext h.symm)
  have h0 := coeff_linLam_eq_zero hk a b (T - Tm) hU β hβ
  rw [map_sub, map_sub, sub_eq_zero] at h0
  rw [h0, hTm, map_sum, map_sum]
  refine sum_congr rfl fun α _ => ?_
  rw [map_smul, MvPowerSeries.coeff_smul]

end Lin

/-! ### `𝒟_m(∞)` is injective -/

theorem coeff_pdA_monomial (k : ℕ) (α β : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff β (pdA k (MvPowerSeries.monomial α (1 : ℂ))) =
      if α = β + Finsupp.single k.toPNat' 1 then (β k.toPNat' : ℂ) + 1 else 0 := by
  classical
  rw [coeff_pdA, MvPowerSeries.coeff_monomial]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

/-- `∑ nσ_n∂_{n+k}` preserves the polynomial degree. -/
theorem degree_of_coeff_shiftA_monomial {k : ℕ} {α β : ℕ+ →₀ ℕ}
    (h : MvPowerSeries.coeff β (shiftA k (MvPowerSeries.monomial α (1 : ℂ))) ≠ 0) :
    α.degree = β.degree := by
  classical
  rw [coeff_shiftA] at h
  obtain ⟨n, hn, hne⟩ := exists_ne_zero_of_sum_ne_zero h
  rw [coeff_pdA, MvPowerSeries.coeff_monomial] at hne
  split_ifs at hne with heq
  · have e1 := congrArg Finsupp.degree heq
    have e2 := congrArg Finsupp.degree (sub_add_single hn)
    rw [map_add, Finsupp.degree_single] at e1 e2
    omega
  · simp at hne

/-- The lowest-degree argument: a vector `v` of level-`m` coefficients (`m ≥ 1`) with
`[σ^β] D_k(∞)(∑ v_α σ^α) = 0` for all `k ≥ 1`, `lvl β + k = m`, is zero. -/
theorem Dinf_injective {m : ℕ} (hm : 1 ≤ m) [Fintype {α : ℕ+ →₀ ℕ // lvl α = m}]
    (v : {α : ℕ+ →₀ ℕ // lvl α = m} → ℂ)
    (hv : ∀ k : ℕ, 1 ≤ k → ∀ β : ℕ+ →₀ ℕ, lvl β + k = m →
      ∑ α, v α * MvPowerSeries.coeff β
        (linLamL k Complex.I 0 (MvPowerSeries.monomial α.1 (1 : ℂ))) = 0) :
    v = 0 := by
  classical
  by_contra hne
  have hsn : (univ.filter fun α => v α ≠ 0).Nonempty := by
    obtain ⟨α, hα⟩ := Function.ne_iff.1 hne
    exact ⟨α, mem_filter.2 ⟨mem_univ _, hα⟩⟩
  obtain ⟨α0, hα0, hmin⟩ := exists_min_image _ (fun α => α.1.degree) hsn
  have hv0 : v α0 ≠ 0 := (mem_filter.1 hα0).2
  have hα0ne : α0.1 ≠ 0 := by
    intro h
    have := α0.2
    rw [h] at this
    simp [lvl] at this
    omega
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.2 hα0ne
  set β := α0.1 - Finsupp.single k 1 with hβdef
  have hβ := lvl_sub_single hk
  have hkm : 1 ≤ (k : ℕ) := k.pos
  have hlv : lvl β + (k : ℕ) = m := by rw [hβ]; exact α0.2
  have h := hv k hkm β hlv
  have hkk : (k : ℕ).toPNat' = k := PNat.coe_toPNat' k
  have hsplit : ∀ α : {α : ℕ+ →₀ ℕ // lvl α = m}, v α * MvPowerSeries.coeff β
      (linLamL k Complex.I 0 (MvPowerSeries.monomial α.1 (1 : ℂ))) =
      if α = α0 then v α0 * (Complex.I * ((β k : ℂ) + 1)) else 0 := by
    intro α
    rw [linLamL_apply]
    simp only [zero_smul, sub_zero, map_add, MvPowerSeries.coeff_smul, smul_eq_mul]
    rw [coeff_pdA_monomial, hkk]
    by_cases hα : α = α0
    · subst hα
      rw [if_pos (sub_add_single hk).symm, if_pos rfl]
      have hsh : MvPowerSeries.coeff β (shiftA k (MvPowerSeries.monomial α.1 (1 : ℂ))) = 0 := by
        by_contra hs
        have := degree_of_coeff_shiftA_monomial hs
        have e := congrArg Finsupp.degree (sub_add_single hk)
        rw [map_add, Finsupp.degree_single] at e
        rw [← hβdef] at e
        omega
      rw [hsh]
      ring
    · rw [if_neg hα]
      have hpd : ¬ α.1 = β + Finsupp.single k 1 := by
        intro h'
        apply hα
        exact Subtype.ext (h'.trans (sub_add_single hk))
      rw [if_neg hpd, mul_zero, zero_add]
      by_cases hvα : v α = 0
      · rw [hvα, zero_mul]
      · by_contra hs
        have hs' : MvPowerSeries.coeff β
            (shiftA k (MvPowerSeries.monomial α.1 (1 : ℂ))) ≠ 0 := by
          intro h0
          apply hs
          rw [h0, mul_zero]
        have e1 := degree_of_coeff_shiftA_monomial hs'
        have e2 := congrArg Finsupp.degree (sub_add_single hk)
        rw [map_add, Finsupp.degree_single, ← hβdef] at e2
        have := hmin α (mem_filter.2 ⟨mem_univ _, hvα⟩)
        omega
  rw [sum_congr rfl fun α _ => hsplit α, sum_ite_eq' univ α0, if_pos (mem_univ _)] at h
  have hc : Complex.I * ((β k : ℂ) + 1) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Nat.succ_ne_zero (β k))
  exact hv0 (by simpa [hc] using h)

end Virasoro.Sphere
