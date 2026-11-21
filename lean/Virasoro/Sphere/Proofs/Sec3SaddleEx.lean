import Virasoro.Sphere.Proofs.Sec3SaddleA

/-!
# Sphere paper Lemma 3.4(iii): `σ_*` is a saddle point (`sphere/paper.tex` l.727–728, l.789–798)

Substitution of a family `σ_m ∈ z^m ℂ[[z]]` into a series in the `σ_m`: the coefficient of
`z^k` only involves the monomials of level `≤ k`.  For a linear series `∑ c_m σ_m` it is
`∑_{m≤k} c_m [z^k]σ_m`.  The saddle-point equations at `σ = σ_*`, `σ̄ = -σ_*` are the recursion
`a_m = h_m - ∑_n (B_{m,n}/n) z^n a_n` of `Sec3SaddleA.lean`.

Consumer: the saddle-point claims in part (iii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem pcoeff_eq (f : PowerSeries ℂ) (d : Unit →₀ ℕ) :
    MvPowerSeries.coeff d f = PowerSeries.coeff (d ()) f := by
  show MvPowerSeries.coeff d f = MvPowerSeries.coeff (Finsupp.single () (d ())) f
  congr 2
  ext u
  simp

theorem hasSubst_of_dvd (σ : ℕ+ → PowerSeries ℂ)
    (hord : ∀ m : ℕ+, (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ σ m) :
    MvPowerSeries.HasSubst σ := by
  refine ⟨fun s => ?_, fun d => ?_⟩
  · have h := (PowerSeries.X_pow_dvd_iff.1 (hord s)) 0 s.pos
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at h
    have h' : MvPowerSeries.constantCoeff (σ s) = 0 := h
    rw [h']
    exact IsNilpotent.zero
  · refine Set.Finite.subset
      (Set.Finite.preimage PNat.coe_injective.injOn (Set.finite_Iic (d ()))) ?_
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    show (s : ℕ) ∈ Set.Iic (d ())
    by_contra hlt
    apply hs
    rw [pcoeff_eq]
    exact (PowerSeries.X_pow_dvd_iff.1 (hord s)) _ (by simpa using hlt)

theorem prod_dvd (σ : ℕ+ → PowerSeries ℂ)
    (hord : ∀ m : ℕ+, (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ σ m) (d : ℕ+ →₀ ℕ) :
    (PowerSeries.X : PowerSeries ℂ) ^ (Finsupp.weight fockWeight d) ∣
      d.prod fun s e => σ s ^ e := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_dvd_prod_of_dvd
  intro s _
  rw [smul_eq_mul, mul_comm, pow_mul]
  exact pow_dvd_pow_of_dvd (hord s) _

/-- The coefficient of `z^k` of `g(σ(z))` vanishes when `g` has no monomial of level `≤ k`. -/
theorem coeff_subst_eq_zero (σ : ℕ+ → PowerSeries ℂ)
    (hord : ∀ m : ℕ+, (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ σ m)
    (g : MvPowerSeries ℕ+ ℂ) (k : ℕ)
    (hg : ∀ d : ℕ+ →₀ ℕ, Finsupp.weight fockWeight d ≤ k → MvPowerSeries.coeff d g = 0) :
    PowerSeries.coeff k (MvPowerSeries.subst σ g) = 0 := by
  show MvPowerSeries.coeff (Finsupp.single () k) (MvPowerSeries.subst σ g) = 0
  rw [MvPowerSeries.coeff_subst (hasSubst_of_dvd σ hord)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hw : Finsupp.weight fockWeight d ≤ k
  · rw [hg d hw, zero_smul]
  · have h := (PowerSeries.X_pow_dvd_iff.1 (prod_dvd σ hord d)) k (by omega)
    rw [show MvPowerSeries.coeff (Finsupp.single () k) (d.prod fun s e => σ s ^ e) = 0 from h,
      smul_zero]

/-- `[z^k] ∑_m c_m σ_m = ∑_{m≤k} c_m [z^k]σ_m`. -/
theorem coeff_subst_linSeries (σ : ℕ+ → PowerSeries ℂ)
    (hord : ∀ m : ℕ+, (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ σ m)
    (c : ℕ → ℂ) (k : ℕ) :
    PowerSeries.coeff k (MvPowerSeries.subst σ (linSeries c)) =
      ∑ n ∈ Icc 1 k, c n * PowerSeries.coeff k (σ n.toPNat') := by
  have hσ := hasSubst_of_dvd σ hord
  set p : MvPowerSeries ℕ+ ℂ := ∑ n ∈ Icc 1 k, c n • MvPowerSeries.X n.toPNat' with hp
  have hsub : MvPowerSeries.subst σ p = ∑ n ∈ Icc 1 k, c n • σ n.toPNat' := by
    rw [hp, ← MvPowerSeries.coe_substAlgHom hσ, map_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [map_smul, MvPowerSeries.substAlgHom_X]
  have hz : PowerSeries.coeff k (MvPowerSeries.subst σ (linSeries c - p)) = 0 := by
    apply coeff_subst_eq_zero σ hord
    intro d hd
    rw [map_sub, hp, map_sum]
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_X, smul_eq_mul]
    by_cases h1 : d.degree = 1
    · obtain ⟨s, rfl⟩ := exists_single_of_degree_one d h1
      have hs : (s : ℕ) ≤ k := by
        rw [Finsupp.weight_single] at hd
        simpa [fockWeight] using hd
      rw [coeff_eq_apply, linSeries_single, sum_eq_single (s : ℕ)]
      · rw [PNat.coe_toPNat', if_pos rfl]
        ring
      · intro n hn hns
        rw [if_neg, mul_zero]
        intro h
        apply hns
        have h2 := Finsupp.single_left_injective (one_ne_zero) h
        have h3 := congrArg (fun t : ℕ+ => (t : ℕ)) h2
        simp only [Nat.toPNat'_coe] at h3
        rw [if_pos (by have := (mem_Icc.1 hn).1; omega)] at h3
        exact h3.symm
      · intro h
        exact absurd (mem_Icc.2 ⟨s.pos, hs⟩) h
    · rw [coeff_eq_apply, linSeries_of_degree_ne c d h1, zero_sub, neg_eq_zero]
      refine sum_eq_zero fun n _ => ?_
      rw [if_neg, mul_zero]
      rintro rfl
      exact h1 (Finsupp.degree_single _ 1)
  have hsplit : linSeries c = p + (linSeries c - p) := by ring
  rw [hsplit, MvPowerSeries.subst_add hσ, map_add, hz, add_zero, hsub, map_sum]
  exact sum_congr rfl fun n _ => by rw [PowerSeries.coeff_smul]; rfl

theorem coeff_sigmaStar (m : ℕ+) (k : ℕ) :
    PowerSeries.coeff k (sigmaStar m) = Complex.I * (1 / ((m : ℕ) : ℂ)) *
      (if (m : ℕ) ≤ k then ((PowerSeries.coeff (k - (m : ℕ)) (aSer m) : ℚ) : ℂ) else 0) := by
  rw [sigmaStar]
  simp only [PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_map, eq_ratCast]
  split_ifs <;> ring

theorem smul_sigmaStar_dvd (s : ℂ) (m : ℕ+) :
    (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) ∣ s • sigmaStar m := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro j hj
  rw [PowerSeries.coeff_smul, coeff_sigmaStar, if_neg (by omega), mul_zero, smul_zero]

/-- The saddle-point equations at `σ = s σ_*`, `σ̄ = -s σ_*`, `s = ±1`. -/
theorem saddle_eq_sign (s : ℂ) (m : ℕ+) :
    (2 * ((m : ℕ) : ℂ)) • (-(s • sigmaStar m)) =
      (PowerSeries.X : PowerSeries ℂ) ^ (m : ℕ) *
        (PowerSeries.C (s * Acoef m) + 2 * MvPowerSeries.subst (fun n => s • sigmaStar n)
          (linSeries fun n => (Bcoef m n : ℂ))) := by
  have hm0 : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 m.pos.ne'
  ext k
  rw [PowerSeries.coeff_smul, map_neg, PowerSeries.coeff_smul, coeff_sigmaStar,
    PowerSeries.coeff_X_pow_mul']
  by_cases hk : (m : ℕ) ≤ k
  · rw [if_pos hk, if_pos hk, map_add, PowerSeries.coeff_C,
      show (2 : PowerSeries ℂ) = PowerSeries.C 2 from (map_ofNat _ 2).symm,
      PowerSeries.coeff_C_mul, coeff_subst_linSeries _ (smul_sigmaStar_dvd s)]
    set j := k - (m : ℕ) with hj
    have hc := congrArg (fun x : ℚ => (x : ℂ)) (coeff_aSer m j)
    simp only [Rat.cast_sub, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_zero] at hc
    have hsum : ∑ n ∈ Icc 1 j, (Bcoef m n : ℂ) *
        PowerSeries.coeff j (s • sigmaStar n.toPNat') =
        s * Complex.I * ∑ n ∈ Icc 1 j, (Bcoef m n : ℂ) / (n : ℂ) *
          ((PowerSeries.coeff (j - n) (aSer n) : ℚ) : ℂ) := by
      rw [mul_sum]
      refine sum_congr rfl fun n hn => ?_
      have hn1 := mem_Icc.1 hn
      have hcoe : ((n.toPNat' : ℕ+) : ℕ) = n := by rw [Nat.toPNat'_coe, if_pos (by omega)]
      rw [PowerSeries.coeff_smul, coeff_sigmaStar, hcoe, if_pos hn1.2, smul_eq_mul]
      ring
    rw [hsum, hc, Acoef]
    simp only [smul_eq_mul]
    split_ifs with h0
    · field_simp
      ring
    · field_simp
      ring
  · rw [if_neg hk, if_neg hk]
    simp

/-- `σ_*` with `σ̄ = -σ_*` is a saddle point. -/
theorem isSaddle_sigmaStar : IsSaddle sigmaStar (fun m => -sigmaStar m) where
  hasSubst := hasSubst_of_dvd _ (fun m => by simpa using smul_sigmaStar_dvd 1 m)
  hasSubst_bar := hasSubst_of_dvd _ (fun m => by simpa using smul_sigmaStar_dvd (-1) m)
  eq := fun m => by
    have := saddle_eq_sign 1 m
    simpa only [one_smul, one_mul] using this
  eq_bar := fun m => by
    have := saddle_eq_sign (-1) m
    simpa only [neg_smul, one_smul, neg_neg, neg_mul, one_mul] using this

end Virasoro.Sphere
