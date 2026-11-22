import Virasoro.Sphere.Proofs.Sec3C2DiagFinal
import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Lemma 3.7, Step 3: the norms of `exp(-∑_m (m/16^m) u_m²)` (sphere paper)

sphere/paper.tex l.1150–1156.  The coefficient of `u^α` in the Gaussian is a product over the
modes, and so is its weight in the form (3.1):
`16^{|α|} |D_α|² ‖u^α‖² = ∏_m h(α_m)`, `h(2k) = binom(2k,k)/4^k`, `h(odd) = 0`.  At each order
of `q` the generating function of the level norms is the finite product over `m` of
`∑_k binom(2k,k) 4^{-k} q^{2mk}`, whose square times `1 - q^{2m}` is `1`.
-/

namespace Virasoro.Sphere

open Finset

/-! ### Finitely supported exponents -/

theorem erase_add_single' (α : ℕ+ →₀ ℕ) (i : ℕ+) :
    (α + Finsupp.single i 1).erase i = α.erase i := by
  classical
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Finsupp.erase_ne h, Finsupp.single_apply, Ne.symm h]

theorem erase_sub_single' (α : ℕ+ →₀ ℕ) (i : ℕ+) :
    (α - Finsupp.single i 1).erase i = α.erase i := by
  classical
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Finsupp.erase_ne h, Finsupp.single_apply, Ne.symm h]

theorem erase_add_single_val (α : ℕ+ →₀ ℕ) (i : ℕ+) :
    α.erase i + Finsupp.single i (α i) = α := by
  classical
  ext j
  by_cases h : j = i
  · subst h
    simp
  · simp [Finsupp.erase_ne h, Finsupp.single_apply, Ne.symm h]

/-! ### The coefficients of the Gaussian -/

/-- The coefficient of `u_m^e` in `exp(-(m/16^m) u_m²)`. -/
noncomputable def dd (m : ℕ+) (e : ℕ) : ℂ :=
  if Even e then (-(((m : ℕ) : ℂ) / 16 ^ (m : ℕ))) ^ (e / 2) / ((e / 2).factorial : ℂ) else 0

theorem dd_zero (m : ℕ+) : dd m 0 = 1 := by
  simp [dd]

theorem dd_step (m : ℕ+) (e : ℕ) :
    dd m (e + 1) * ((e : ℂ) + 1) =
      (-(2 * ((m : ℕ) : ℂ) * (1 / 16 : ℂ) ^ (m : ℕ))) * (if e = 0 then 0 else dd m (e - 1)) := by
  rcases Nat.even_or_odd' e with ⟨j, rfl | rfl⟩
  · have h1 : ¬ Even (2 * j + 1) := by
      rw [Nat.not_even_iff_odd]
      exact ⟨j, rfl⟩
    rw [dd, if_neg h1, zero_mul]
    by_cases hj : 2 * j = 0
    · rw [if_pos hj, mul_zero]
    · have h2 : ¬ Even (2 * j - 1) := by
        rw [Nat.not_even_iff_odd]
        exact ⟨j - 1, by omega⟩
      rw [if_neg hj, dd, if_neg h2, mul_zero]
  · have h1 : Even (2 * j + 1 + 1) := ⟨j + 1, by ring⟩
    have h2 : Even (2 * j + 1 - 1) := ⟨j, by omega⟩
    have e1 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
    have e2 : (2 * j + 1 - 1) / 2 = j := by omega
    have hf : ((j + 1).factorial : ℂ) = ((j : ℂ) + 1) * (j.factorial : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hj0 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hj1 : (j : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero j
    have ha : -(2 * ((m : ℕ) : ℂ) * (1 / 16 : ℂ) ^ (m : ℕ)) =
        2 * (-(((m : ℕ) : ℂ) / 16 ^ (m : ℕ))) := by
      rw [one_div_pow]
      ring
    rw [ha, dd, if_pos h1, if_neg (by omega), dd, if_pos h2, e1, e2, hf]
    generalize -(((m : ℕ) : ℂ) / 16 ^ (m : ℕ)) = t
    push_cast
    field_simp
    ring

/-- `∏_m` of the one-mode coefficients. -/
noncomputable def Dc : MvPowerSeries ℕ+ ℂ := fun α => α.prod dd

/-- The coefficients of `exp(-∑_m (m/16^m) u_m²)` (sphere/paper.tex l.1148):
`∏_m (-(m/16^m))^{k_m}/k_m!` at `u^{2k}`, zero at the other monomials. -/
theorem Dgs_eq_Dc : Dgs = Dc := by
  classical
  have h0 : IsNilpotent (MvPowerSeries.constantCoeff diagExpo) := by
    rw [constantCoeff_diagExpo]
    exact IsNilpotent.zero
  refine ext_of_pderiv (fun i : ℕ+ =>
    MvPowerSeries.C (-(2 * ((i : ℕ) : ℂ) * (1 / 16 : ℂ) ^ (i : ℕ))) * MvPowerSeries.X i) ?_ ?_ ?_
  · rw [Dgs, constantCoeff_mexp constantCoeff_diagExpo,
      ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show (1 : ℂ) = (0 : ℕ+ →₀ ℕ).prod dd
    rw [Finsupp.prod_zero_index]
  · intro i
    have h := pdA_diagExpo (i : ℕ) i.pos
    rw [pdA, PNat.coe_toPNat'] at h
    rw [Dgs, pderiv_mexp h0, h]
  · intro i
    ext α
    rw [MvPowerSeries.coeff_pderiv,
      show Dc * (MvPowerSeries.C (-(2 * ((i : ℕ) : ℂ) * (1 / 16 : ℂ) ^ (i : ℕ))) *
          MvPowerSeries.X i) =
        MvPowerSeries.C (-(2 * ((i : ℕ) : ℂ) * (1 / 16 : ℂ) ^ (i : ℕ))) *
          (MvPowerSeries.X i * Dc) by ring, MvPowerSeries.coeff_C_mul, coeff_X_mulA]
    have e1 : MvPowerSeries.coeff (α + Finsupp.single i 1) Dc =
        dd i (α i + 1) * (α.erase i).prod dd := by
      show (α + Finsupp.single i 1).prod dd = _
      rw [← Finsupp.mul_prod_erase' (α + Finsupp.single i 1) i dd dd_zero, erase_add_single',
        Finsupp.add_apply, Finsupp.single_eq_same]
    have e2 : MvPowerSeries.coeff (α - Finsupp.single i 1) Dc =
        dd i (α i - 1) * (α.erase i).prod dd := by
      show (α - Finsupp.single i 1).prod dd = _
      rw [← Finsupp.mul_prod_erase' (α - Finsupp.single i 1) i dd dd_zero, erase_sub_single',
        Finsupp.tsub_apply, Finsupp.single_eq_same]
    have hs := dd_step i (α i)
    rw [e1]
    by_cases hi : i ∈ α.support
    · rw [if_pos hi, e2]
      rw [if_neg (Finsupp.mem_support_iff.mp hi)] at hs
      linear_combination (α.erase i).prod dd * hs
    · rw [if_neg hi]
      rw [if_pos (Finsupp.notMem_support_iff.mp hi)] at hs
      linear_combination (α.erase i).prod dd * hs

/-! ### The weights -/

/-- `binom(2k,k)/4^k` at `e = 2k`, zero at odd `e`. -/
noncomputable def hh (e : ℕ) : ℂ := if Even e then (halfBinom (e / 2) : ℂ) else 0

theorem hh_zero : hh 0 = 1 := by
  simp [hh, halfBinom_zero']

theorem wf_alg (A m F cb : ℂ) (k : ℕ) (hA : A ≠ 0) (hm : m ≠ 0) (hF : F ≠ 0) :
    A ^ (2 * k) * ((-(m / A)) ^ k / F) * ((-(m / A)) ^ k / F) * (cb * F * F / (2 * m) ^ (2 * k)) =
      cb / 4 ^ k := by
  have hb : A ^ 2 * ((-(m / A)) * (-(m / A))) / (2 * m) ^ 2 = 1 / 4 := by
    field_simp
    ring
  have key : A ^ (2 * k) * ((-(m / A)) ^ k * (-(m / A)) ^ k) / (2 * m) ^ (2 * k) =
      (1 / 4 : ℂ) ^ k := by
    rw [pow_mul A 2 k, pow_mul (2 * m) 2 k, ← mul_pow (-(m / A)) (-(m / A)) k, ← mul_pow, ← div_pow,
      hb]
  have hM : (2 * m) ^ (2 * k) ≠ 0 := pow_ne_zero _ (mul_ne_zero two_ne_zero hm)
  have h1 : A ^ (2 * k) * ((-(m / A)) ^ k / F) * ((-(m / A)) ^ k / F) *
      (cb * F * F / (2 * m) ^ (2 * k)) =
      A ^ (2 * k) * ((-(m / A)) ^ k * (-(m / A)) ^ k) / (2 * m) ^ (2 * k) * cb := by
    generalize (-(m / A)) ^ k = P
    generalize A ^ (2 * k) = Ak
    generalize (2 * m) ^ (2 * k) = Mk at hM
    field_simp
  rw [h1, key, one_div_pow]
  ring

/-- The one-mode weight (sphere/paper.tex l.1152): `m^{2k}(2k)!/((k!)²(2m)^{2k})`. -/
theorem weight_factor (m : ℕ+) (e : ℕ) :
    (16 : ℂ) ^ ((m : ℕ) * e) * (starRingEnd ℂ) (dd m e) * dd m e *
      ((e.factorial : ℂ) / (2 * ((m : ℕ) : ℂ)) ^ e) = hh e := by
  by_cases he : Even e
  · obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by obtain ⟨r, hr⟩ := he; omega⟩
    have e1 : 2 * k / 2 = k := by omega
    have hm : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.pos.ne'
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hfac : ((2 * k).factorial : ℂ) =
        (Nat.centralBinom k : ℂ) * (k.factorial : ℂ) * (k.factorial : ℂ) := by
      have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
      rw [show 2 * k - k = k by omega] at h
      rw [Nat.centralBinom]
      exact_mod_cast h.symm
    have hconj : (starRingEnd ℂ) (dd m (2 * k)) = dd m (2 * k) := by
      rw [dd, if_pos he]
      simp only [map_div₀, map_pow, map_neg, map_natCast, map_ofNat]
    have hA : ((16 : ℂ) ^ (m : ℕ)) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [hconj, dd, if_pos he, hh, if_pos he, e1, halfBinom_eq, hfac, pow_mul (16 : ℂ)]
    push_cast
    exact wf_alg _ _ _ _ k hA hm hk
  · rw [dd, if_neg he, hh, if_neg he]
    simp

/-- `16^{|α|} |D_α|² ‖u^α‖² = ∏_m h(α_m)`. -/
theorem weight_prod (α : ℕ+ →₀ ℕ) :
    (16 : ℂ) ^ lvl α * (starRingEnd ℂ) (MvPowerSeries.coeff α Dgs) * MvPowerSeries.coeff α Dgs *
      fockNorm α = α.prod fun _ e => hh e := by
  have h16 : (16 : ℂ) ^ lvl α = α.prod fun m e => (16 : ℂ) ^ ((m : ℕ) * e) := by
    rw [lvl, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun m _ => ?_
    simp only [fockWeight, smul_eq_mul]
    rw [mul_comm]
  rw [Dgs_eq_Dc, coeff_eq_apply, h16]
  show _ * (starRingEnd ℂ) (α.prod dd) * α.prod dd * fockNorm α = _
  unfold fockNorm Finsupp.prod
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun m _ => weight_factor m (α m)

/-- `16^n ‖(exp(-∑ (m/16^m) u_m²))_n‖² = ∑_{|α| = n} ∏_m h(α_m)`. -/
theorem diag_norm_eq (n : ℕ) :
    (16 : ℂ) ^ n * fockForm (diagF n) (diagF n) =
      ∑ α ∈ (finite_level n).toFinset, α.prod fun _ e => hh e := by
  classical
  have hsupp : (diagF n).support ⊆ (finite_level n).toFinset := by
    intro α hα
    rw [mem_level_iff]
    have h := lp_mem_level Dgs n
    rw [← diagF_eq_lp] at h
    exact h (MvPolynomial.mem_support_iff.mp hα)
  rw [fockForm_eq _ _ _ hsupp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hl : lvl α = n := (mem_level_iff n α).mp hα
  rw [diagF_eq_lp, coeff_lp, if_pos (by omega), ← weight_prod α, hl]
  ring

/-! ### The product over the modes -/

/-- `∑_k binom(2k,k) 4^{-k} u_i^{2k}` as a series in the `u_m`. -/
noncomputable def Hm (i : ℕ+) : MvPowerSeries ℕ+ ℂ :=
  fun α => if α = Finsupp.single i (α i) then hh (α i) else 0

theorem coeff_mul_Hm (Φ : MvPowerSeries ℕ+ ℂ) (i : ℕ+)
    (hΦ : ∀ β : ℕ+ →₀ ℕ, β i ≠ 0 → MvPowerSeries.coeff β Φ = 0) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (Φ * Hm i) = MvPowerSeries.coeff (α.erase i) Φ * hh (α i) := by
  classical
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (α.erase i, Finsupp.single i (α i))]
  · rw [coeff_eq_apply (Hm i), Hm, Finsupp.single_eq_same, if_pos rfl]
  · rintro ⟨p1, p2⟩ hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only at hp ⊢
    by_cases h1 : p1 i = 0
    · rw [coeff_eq_apply (Hm i), Hm]
      by_cases h2 : p2 = Finsupp.single i (p2 i)
      · exfalso
        apply hne
        have h3 : p2 i = α i := by
          have := congrArg (fun f : ℕ+ →₀ ℕ => f i) hp
          simp only [Finsupp.add_apply, h1, zero_add] at this
          exact this
        have h4 : p2 = Finsupp.single i (α i) := by rw [← h3]; exact h2
        have h5 : p1 = α.erase i := by
          have h6 : p1 + Finsupp.single i (α i) = α.erase i + Finsupp.single i (α i) := by
            rw [erase_add_single_val, ← h4, hp]
          exact add_right_cancel h6
        rw [h4, h5]
      · rw [if_neg h2, mul_zero]
    · rw [hΦ p1 h1, zero_mul]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact erase_add_single_val α i

/-- The coefficients of the finite product `∏_{i ∈ S} ∑_k binom(2k,k) 4^{-k} u_i^{2k}`. -/
theorem coeff_prod_Hm (S : Finset ℕ+) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (∏ i ∈ S, Hm i) =
      if α.support ⊆ S then α.prod fun _ e => hh e else 0 := by
  classical
  induction S using Finset.induction_on generalizing α with
  | empty =>
    rw [Finset.prod_empty, MvPowerSeries.coeff_one]
    by_cases h : α = 0
    · subst h
      rw [if_pos rfl, if_pos (by simp), Finsupp.prod_zero_index]
    · rw [if_neg h, if_neg]
      intro h'
      exact h (Finsupp.support_eq_empty.mp (Finset.subset_empty.mp h'))
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, mul_comm, coeff_mul_Hm _ i (fun β hβ => by
      rw [ih, if_neg]
      intro h'
      exact hi (h' (Finsupp.mem_support_iff.mpr hβ))), ih]
    have hiff : (α.erase i).support ⊆ S ↔ α.support ⊆ insert i S := by
      rw [Finsupp.support_erase, Finset.subset_insert_iff]
    by_cases h : α.support ⊆ insert i S
    · rw [if_pos (hiff.mpr h), if_pos h, mul_comm]
      exact Finsupp.mul_prod_erase' α i (fun _ e => hh e) fun _ => hh_zero
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, zero_mul]

theorem lvl_single_mul (i : ℕ+) (e : ℕ) : lvl (Finsupp.single i e) = e * (i : ℕ) := by
  simp [lvl, Finsupp.weight_single, fockWeight]

/-- `W_m ↦ W_m t^m` on the one-mode series: `∑_k binom(2k,k) 4^{-k} t^{2ik}`. -/
theorem levS_Hm (i : ℕ+) :
    levS (Hm i) = PowerSeries.expand (2 * (i : ℕ)) (by have := i.pos; omega) hserC := by
  classical
  have hi := i.pos
  ext d
  rw [coeff_levS, PowerSeries.coeff_expand]
  by_cases hd : 2 * (i : ℕ) ∣ d
  · obtain ⟨k, rfl⟩ := hd
    have e0 : 2 * (i : ℕ) * k / (2 * (i : ℕ)) = k := Nat.mul_div_cancel_left _ (by omega)
    rw [if_pos (Dvd.intro _ rfl), e0, Finset.sum_eq_single (Finsupp.single i (2 * k))]
    · rw [coeff_eq_apply, Hm, Finsupp.single_eq_same, if_pos rfl, hh, if_pos ⟨k, by ring⟩,
        hserC, PowerSeries.coeff_map, hser, PowerSeries.coeff_mk]
      have e1 : 2 * k / 2 = k := by omega
      rw [e1]
      simp
    · intro α hα hne
      have hl : lvl α = 2 * (i : ℕ) * k := (mem_level_iff _ α).mp hα
      rw [coeff_eq_apply, Hm]
      by_cases h : α = Finsupp.single i (α i)
      · exfalso
        apply hne
        rw [h, lvl_single_mul] at hl
        have h2 : α i = 2 * k := by
          have h3 : α i * (i : ℕ) = (2 * k) * (i : ℕ) := by rw [hl]; ring
          exact Nat.eq_of_mul_eq_mul_right hi h3
        rw [h, h2]
      · rw [if_neg h]
    · intro hnot
      exfalso
      apply hnot
      rw [mem_level_iff, lvl_single_mul]
      ring
  · rw [if_neg hd]
    refine Finset.sum_eq_zero fun α hα => ?_
    have hl : lvl α = d := (mem_level_iff _ α).mp hα
    rw [coeff_eq_apply, Hm]
    by_cases h : α = Finsupp.single i (α i)
    · rw [if_pos h, hh]
      by_cases he : Even (α i)
      · exfalso
        apply hd
        obtain ⟨r, hr⟩ := he
        rw [h, lvl_single_mul] at hl
        exact ⟨r, by rw [← hl, hr]; ring⟩
      · rw [if_neg he]
    · rw [if_neg h]

theorem levS_prod (S : Finset ℕ+) (Φ : ℕ+ → MvPowerSeries ℕ+ ℂ) :
    levS (∏ i ∈ S, Φ i) = ∏ i ∈ S, levS (Φ i) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, levS_one]
  | insert i S hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, levS_mul, ih]

/-- `(∑_k binom(2k,k) 4^{-k} t^k)² (1 - t) = 1` at `t = q^{2i}` (sphere/paper.tex l.1153). -/
theorem expand_hserC_sq (i : ℕ) (hi : 2 * i ≠ 0) :
    (PowerSeries.expand (2 * i) hi hserC) ^ 2 * (1 - PowerSeries.X ^ (2 * i)) = 1 := by
  have h : hserC ^ 2 * (1 - PowerSeries.X) = 1 := by
    have h1 := congrArg (PowerSeries.map (algebraMap ℚ ℂ)) hser_sq
    rw [map_mul, map_pow, map_sub, map_one, PowerSeries.map_X] at h1
    exact h1
  have h2 := congrArg (PowerSeries.expand (2 * i) hi) h
  rw [map_mul, map_pow, map_sub, map_one, PowerSeries.expand_X] at h2
  exact h2

/-- Lemma 3.7, Step 3, second part (sphere/paper.tex l.1150–1156). -/
theorem sub_c2_diag_norm : Stmt_sub_c2_diag_norm := by
  classical
  ext n
  set S : Finset ℕ+ := (Finset.Icc 1 n).image Nat.toPNat' with hS
  set P : PowerSeries ℂ := ∏ i ∈ S, PowerSeries.expand (2 * (i : ℕ))
    (by have := i.pos; omega) hserC with hP
  set E : PowerSeries ℂ := ∏ m ∈ Finset.Icc 1 n, (1 - (PowerSeries.X : PowerSeries ℂ) ^ (2 * m))
    with hE
  have hPE : P ^ 2 * E = 1 := by
    have hE' : E = ∏ i ∈ S, (1 - (PowerSeries.X : PowerSeries ℂ) ^ (2 * (i : ℕ))) := by
      rw [hE, hS, Finset.prod_image]
      · refine Finset.prod_congr rfl fun m hm => ?_
        rw [PNat.toPNat'_coe (Finset.mem_Icc.mp hm).1]
      · intro a ha b hb hab
        exact toPNat'_inj (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1 hab
    rw [hE', hP, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i _ => expand_hserC_sq (i : ℕ) (by have := i.pos; omega)
  have hG : ∀ k ≤ n, PowerSeries.coeff k
      (PowerSeries.mk fun n => (16 : ℂ) ^ n * fockForm (diagF n) (diagF n)) =
      PowerSeries.coeff k P := by
    intro k hk
    have hP' : P = levS (∏ i ∈ S, Hm i) := by
      rw [levS_prod, hP]
      exact Finset.prod_congr rfl fun i _ => (levS_Hm i).symm
    rw [PowerSeries.coeff_mk, diag_norm_eq, hP', coeff_levS]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hl : lvl α = k := (mem_level_iff k α).mp hα
    rw [coeff_prod_Hm, if_pos]
    intro m hm
    have e := congrArg lvl (sub_add_single hm)
    rw [lvl_add, lvl_single] at e
    rw [hS, Finset.mem_image]
    exact ⟨(m : ℕ), Finset.mem_Icc.mpr ⟨m.pos, by omega⟩, PNat.coe_toPNat' m⟩
  have hη : ∀ k ≤ n, PowerSeries.coeff k ((etaSqPow 1).map (algebraMap ℚ ℂ)) =
      PowerSeries.coeff k E := by
    intro k hk
    have h1 : PowerSeries.coeff k ((etaSqPow 1).map (algebraMap ℚ ℂ)) = PowerSeries.coeff k
        (∏ m ∈ Finset.Icc 1 k, (1 - (PowerSeries.X : PowerSeries ℂ) ^ (2 * m))) := by
      rw [PowerSeries.coeff_map, etaSqPow, PowerSeries.coeff_mk, ← PowerSeries.coeff_map,
        map_prod]
      simp only [pow_one, map_sub, map_one, map_pow, PowerSeries.map_X]
    rw [h1]
    refine (mkT_eq_iff _ _).1 ?_ k le_rfl
    rw [hE, map_prod, map_prod]
    refine Finset.prod_subset (Finset.Icc_subset_Icc_right hk) fun m hm hm' => ?_
    rw [Finset.mem_Icc] at hm hm'
    have h0 : mkT k ℂ ((PowerSeries.X : PowerSeries ℂ) ^ (2 * m)) = 0 := by
      rw [mkT_eq_zero_iff]
      intro j hj
      rw [PowerSeries.coeff_X_pow, if_neg (by omega)]
    rw [map_sub, map_one, h0, sub_zero]
  have h1 : mkT n ℂ ((PowerSeries.mk fun n => (16 : ℂ) ^ n * fockForm (diagF n) (diagF n)) ^ 2 *
      (etaSqPow 1).map (algebraMap ℚ ℂ)) = mkT n ℂ (P ^ 2 * E) := by
    rw [map_mul, map_pow, map_mul, map_pow, (mkT_eq_iff _ _).2 hG, (mkT_eq_iff _ _).2 hη]
  rw [hPE] at h1
  exact (mkT_eq_iff _ _).1 h1 n le_rfl

end Virasoro.Sphere
