import Virasoro.Sphere.Proofs.Sec3C2Space
import Virasoro.Sphere.Proofs.Sec3SaddlePdeAll
import Virasoro.Sphere.Proofs.Sec3SaddleDiag
import Virasoro.Sphere.Proofs.Sec3ExtLinear

/-!
# Lemma 3.7, Step 1: the pure Gaussians solve the Ward equations (sphere paper)

sphere/paper.tex l.1029–1035: at `μ = 0`, `Δ₁ = Δ₂ = 1/16`, Lemma 3.3(ii) and Lemma 3.4(i) show
that the exact finite-`λ` Fock Ward equations `l_k F = (l_0 + (k-1)/16) F` are solved
identically by the pure Gaussians `F_1(v) = exp(λ∑A_m v_m + ∑B_{m,n} v_m v_n)` and
`F_2(u) = exp(∑B_{m,n} u_m u_n)`.

The exponent is `E = λ² S^{(0)}(u/λ)`.  The order-`λ⁰` equation of Lemma 3.4(i), rescaled by
`σ ↦ tσ`, holds for every `t`; its parts of degree `0, 1, 2` in `t` and the identity
`-½∑_{n<k} B_{n,k-n} = (k-1)/16` give equation (3.3) for `E` with `μ = 0`, `Δ₁ = Δ₂ = 1/16`
and no higher terms.
-/

namespace Virasoro.Sphere

open Finset

local notation "cC" => (MvPowerSeries.C : ℂ →+* MvPowerSeries ℕ+ ℂ)

/-! ### The rescaling `σ ↦ tσ` -/

/-- The substitution `σ_m ↦ tσ_m`. -/
noncomputable def rsc (t : ℂ) : MvPowerSeries ℕ+ ℂ →+* MvPowerSeries ℕ+ ℂ :=
  MvPowerSeries.rescale fun _ => t

theorem coeff_rsc (t : ℂ) (T : MvPowerSeries ℕ+ ℂ) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (rsc t T) = t ^ α.degree * MvPowerSeries.coeff α T := by
  rw [rsc, MvPowerSeries.coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

theorem rsc_C (t a : ℂ) : rsc t (cC a) = cC a := by
  classical
  ext α
  rw [coeff_rsc, MvPowerSeries.coeff_C]
  split_ifs with h
  · subst h
    simp
  · simp

theorem rsc_lin (t : ℂ) (c : ℕ → ℂ) : rsc t (linSeries c) = cC t * linSeries c := by
  ext α
  rw [coeff_rsc, MvPowerSeries.coeff_C_mul]
  show t ^ α.degree * linSeries c α = t * linSeries c α
  unfold linSeries
  split_ifs with h
  · rw [h, pow_one]
  · simp

theorem shiftA_rsc (k : ℕ) (t : ℂ) (T : MvPowerSeries ℕ+ ℂ) :
    shiftA k (rsc t T) = rsc t (shiftA k T) := by
  ext α
  rw [coeff_shiftA, coeff_rsc, coeff_shiftA, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [coeff_pdA, coeff_pdA, coeff_rsc]
  have h1 := congrArg Finsupp.degree (sub_add_single hn)
  rw [map_add, Finsupp.degree_single] at h1
  have hdeg : (α - Finsupp.single n 1 + Finsupp.single ((n : ℕ) + k).toPNat' 1).degree =
      α.degree := by
    rw [map_add, Finsupp.degree_single]
    exact h1
  rw [hdeg]
  ring

theorem levelA_rsc (t : ℂ) (T : MvPowerSeries ℕ+ ℂ) : levelA (rsc t T) = rsc t (levelA T) := by
  ext α
  simp only [coeff_levelA, coeff_rsc]
  ring

theorem pdA_C_mul (n : ℕ) (a : ℂ) (T : MvPowerSeries ℕ+ ℂ) :
    pdA n (cC a * T) = cC a * pdA n T := by
  rw [← MvPowerSeries.smul_eq_C_mul, pdA_smul, MvPowerSeries.smul_eq_C_mul]

theorem shiftA_C_mul (k : ℕ) (a : ℂ) (T : MvPowerSeries ℕ+ ℂ) :
    shiftA k (cC a * T) = cC a * shiftA k T := by
  rw [← MvPowerSeries.smul_eq_C_mul, shiftA_smul, MvPowerSeries.smul_eq_C_mul]

theorem levelA_C_mul (a : ℂ) (T : MvPowerSeries ℕ+ ℂ) :
    levelA (cC a * T) = cC a * levelA T := by
  rw [← MvPowerSeries.smul_eq_C_mul, levelA_smul, MvPowerSeries.smul_eq_C_mul]

/-! ### The linear and quadratic parts of `S^{(0)}` -/

/-- `∑_m A_m σ_m`. -/
noncomputable def S0L : MvPowerSeries ℕ+ ℂ := linSeries Acoef

/-- `∑_{m,n} B_{m,n} σ_m σ_n`. -/
noncomputable def S0Q : MvPowerSeries ℕ+ ℂ := S0 - S0L

/-- `∑_m (B_{n,m} + B_{m,n}) σ_m = ∂_{σ_n} ∑ B σσ`. -/
noncomputable def ellB (n : ℕ) : MvPowerSeries ℕ+ ℂ :=
  linSeries fun m => (Bcoef n m : ℂ) + (Bcoef m n : ℂ)

theorem pdA_S0L (n : ℕ) (hn : 1 ≤ n) : pdA n S0L = cC (Acoef n) := pdA_linSeries _ n hn

theorem pdA_S0Q (n : ℕ) (hn : 1 ≤ n) : pdA n S0Q = ellB n := by
  rw [S0Q, pdA_sub, pdA_S0L n hn, ← pd_eq_pdA, pd_S0 n hn, add_sub_cancel_left]
  rfl

theorem pdA_ellB (j n : ℕ) (hn : 1 ≤ n) :
    pdA n (ellB j) = cC ((Bcoef j n : ℂ) + (Bcoef n j : ℂ)) := pdA_linSeries _ n hn

theorem S0_of_degree_one (α : ℕ+ →₀ ℕ) (h : α.degree = 1) : S0 α = S0L α := by
  simp only [S0, S0L, linSeries, if_pos h]

theorem S0L_of_degree_ne (α : ℕ+ →₀ ℕ) (h : α.degree ≠ 1) : S0L α = 0 := by
  simp only [S0L, linSeries, if_neg h]

theorem S0_of_degree_ne (α : ℕ+ →₀ ℕ) (h1 : α.degree ≠ 1) (h2 : α.degree ≠ 2) : S0 α = 0 := by
  simp only [S0, if_neg h1, if_neg h2]

theorem rsc_S0 (t : ℂ) : rsc t S0 = cC t * S0L + cC (t ^ 2) * S0Q := by
  ext α
  rw [coeff_rsc, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul, S0Q, map_sub]
  show t ^ α.degree * S0 α = t * S0L α + t ^ 2 * (S0 α - S0L α)
  by_cases h1 : α.degree = 1
  · rw [S0_of_degree_one α h1, h1]
    ring
  · rw [S0L_of_degree_ne α h1]
    by_cases h2 : α.degree = 2
    · rw [h2]
      ring
    · rw [S0_of_degree_ne α h1 h2]
      ring

theorem gaussExpo_eq (lam : ℂ) : gaussExpo lam = cC lam * S0L + S0Q := by
  ext α
  rw [map_add, MvPowerSeries.coeff_C_mul, S0Q, map_sub]
  show gaussExpo lam α = lam * S0L α + (S0 α - S0L α)
  unfold gaussExpo
  by_cases h1 : α.degree = 1
  · rw [if_pos h1, S0_of_degree_one α h1]
    ring
  · rw [if_neg h1, S0L_of_degree_ne α h1]
    ring

/-! ### The three parts of the order-`λ⁰` equation -/

section Parts

variable (k : ℕ)

/-- The part of degree `0`. -/
noncomputable def W0 : MvPowerSeries ℕ+ ℂ :=
  cC Complex.I * cC (Acoef k)
    - cC (1 / 4) * ∑ n ∈ Icc 1 (k - 1), cC (Acoef n) * cC (Acoef (k - n)) - 1

/-- The part of degree `1`. -/
noncomputable def W1 : MvPowerSeries ℕ+ ℂ :=
  cC Complex.I * ellB k + shiftA k S0L - levelA S0L
    - cC (1 / 4) * ∑ n ∈ Icc 1 (k - 1),
        (cC (Acoef n) * ellB (k - n) + ellB n * cC (Acoef (k - n)))

/-- The part of degree `2`. -/
noncomputable def W2 : MvPowerSeries ℕ+ ℂ :=
  shiftA k S0Q - levelA S0Q - cC (1 / 4) * ∑ n ∈ Icc 1 (k - 1), ellB n * ellB (k - n)

theorem sum_expand (T : MvPowerSeries ℕ+ ℂ) (a b c d : ℕ → MvPowerSeries ℕ+ ℂ) (s : Finset ℕ) :
    ∑ n ∈ s, (a n + T * b n) * (c n + T * d n) =
      ∑ n ∈ s, a n * c n + T * ∑ n ∈ s, (a n * d n + b n * c n) + T ^ 2 * ∑ n ∈ s, b n * d n := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

variable {k}

/-- The order-`λ⁰` equation of Lemma 3.4(i) for `S^{(0)}(tσ)`. -/
theorem scaled_pde (hk : 1 ≤ k) (t : ℂ) : W0 k + cC t * W1 k + cC t ^ 2 * W2 k = 0 := by
  have h := congrArg (rsc t) (pdeZero_S0 k hk)
  rw [pdeZero, map_zero] at h
  simp only [map_sub, map_add, map_one, MvPowerSeries.smul_eq_C_mul, map_mul, map_sum, rsc_C]
    at h
  have hpd : ∀ n, 1 ≤ n → rsc t (pd n S0) = cC (Acoef n) + cC t * ellB n := fun n hn => by
    rw [pd_S0 n hn, map_add, rsc_C, rsc_lin]
    rfl
  have hsum : ∑ n ∈ Icc 1 (k - 1), rsc t (pd n S0) * rsc t (pd (k - n) S0) =
      ∑ n ∈ Icc 1 (k - 1), (cC (Acoef n) + cC t * ellB n) *
        (cC (Acoef (k - n)) + cC t * ellB (k - n)) :=
    Finset.sum_congr rfl fun n hn => by
      rw [Finset.mem_Icc] at hn
      rw [hpd n hn.1, hpd (k - n) (by omega)]
  rw [hpd k hk, hsum, shiftOp_eq_shiftA, levelOp_eq_levelA, ← shiftA_rsc, ← levelA_rsc, rsc_S0,
    shiftA_add, shiftA_C_mul, shiftA_C_mul, levelA_add, levelA_C_mul, levelA_C_mul, sum_expand,
    map_pow] at h
  rw [W0, W1, W2]
  linear_combination h

theorem W0_eq (hk : 1 ≤ k) : W0 k = 0 := by
  have h := scaled_pde hk 0
  rw [map_zero] at h
  linear_combination h

theorem W1_eq (hk : 1 ≤ k) : W1 k = 0 := by
  have h1 := scaled_pde hk 1
  have hm := scaled_pde hk (-1)
  rw [map_one] at h1
  rw [map_neg, map_one] at hm
  have h2 : (2 : ℂ) • W1 k = 0 := by
    rw [two_smul]
    linear_combination h1 - hm
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem W2_eq (hk : 1 ≤ k) : W2 k = 0 := by
  have h1 := scaled_pde hk 1
  rw [map_one, W0_eq hk, W1_eq hk] at h1
  linear_combination h1

theorem sum_B_const (hk : 1 ≤ k) :
    cC (1 / 4) * ∑ n ∈ Icc 1 (k - 1), cC ((Bcoef (k - n) n : ℂ) + (Bcoef n (k - n) : ℂ)) +
      cC (((k : ℂ) - 1) / 16) = 0 := by
  rw [← map_sum, ← map_mul, ← map_add]
  have h := congrArg (Rat.cast : ℚ → ℂ) (sum_Bcoef_diag k hk)
  push_cast at h
  have h2 : ∑ n ∈ Icc 1 (k - 1), ((Bcoef (k - n) n : ℂ) + (Bcoef n (k - n) : ℂ)) =
      2 * ∑ n ∈ Icc 1 (k - 1), (Bcoef n (k - n) : ℂ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by
      rw [Bcoef_symm (k - n) n]
      ring
  rw [h2]
  have h3 : (1 / 4 : ℂ) * (2 * ∑ n ∈ Icc 1 (k - 1), (Bcoef n (k - n) : ℂ)) +
      ((k : ℂ) - 1) / 16 = 0 := by
    linear_combination -h
  rw [h3, map_zero]

/-- Equation (3.3) for the exponent `E = λ∑A_m u_m + ∑B_{m,n}u_m u_n` at `μ = 0`,
`Δ₁ = Δ₂ = 1/16`, in the variables `u = λσ`. -/
theorem gaussExpo_pde (lam : ℂ) (hk : 1 ≤ k) :
    shiftA k (gaussExpo lam)
      - cC (1 / 4) * ∑ n ∈ Icc 1 (k - 1),
          (pdA n (gaussExpo lam) * pdA (k - n) (gaussExpo lam) +
            pdA n (pdA (k - n) (gaussExpo lam)))
      + cC (Complex.I * lam) * pdA k (gaussExpo lam) - levelA (gaussExpo lam)
      - cC (lam ^ 2 + ((k : ℂ) - 1) / 16) = 0 := by
  have hpd : ∀ n, 1 ≤ n → pdA n (gaussExpo lam) = cC lam * cC (Acoef n) + ellB n := fun n hn => by
    rw [gaussExpo_eq, pdA_add, pdA_C_mul, pdA_S0L n hn, pdA_S0Q n hn]
  have hpd2 : ∀ n j, 1 ≤ n → 1 ≤ j →
      pdA n (pdA j (gaussExpo lam)) = cC ((Bcoef j n : ℂ) + (Bcoef n j : ℂ)) := fun n j hn hj => by
    rw [hpd j hj, pdA_add, pdA_C_mul, pdA_C, mul_zero, zero_add, pdA_ellB j n hn]
  have hsum : ∑ n ∈ Icc 1 (k - 1),
      (pdA n (gaussExpo lam) * pdA (k - n) (gaussExpo lam) +
        pdA n (pdA (k - n) (gaussExpo lam))) =
      (∑ n ∈ Icc 1 (k - 1), cC (Acoef n) * cC (Acoef (k - n))) * cC lam ^ 2 +
        cC lam * ∑ n ∈ Icc 1 (k - 1),
          (cC (Acoef n) * ellB (k - n) + ellB n * cC (Acoef (k - n))) +
        ∑ n ∈ Icc 1 (k - 1), ellB n * ellB (k - n) +
        ∑ n ∈ Icc 1 (k - 1), cC ((Bcoef (k - n) n : ℂ) + (Bcoef n (k - n) : ℂ)) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    rw [hpd2 n (k - n) hn.1 (by omega), hpd n hn.1, hpd (k - n) (by omega)]
    ring
  have h0 := W0_eq hk
  have h1 := W1_eq hk
  have h2 := W2_eq hk
  have hB := sum_B_const hk
  rw [W0] at h0
  rw [W1] at h1
  rw [W2] at h2
  rw [hsum, hpd k hk]
  rw [gaussExpo_eq, shiftA_add, shiftA_C_mul, levelA_add, levelA_C_mul, map_add, map_pow, map_mul]
  linear_combination cC lam ^ 2 * h0 + cC lam * h1 + h2 - hB

end Parts

/-! ### The Gaussian series -/

theorem constantCoeff_gaussExpo (lam : ℂ) : MvPowerSeries.constantCoeff (gaussExpo lam) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show gaussExpo lam 0 = 0
  simp [gaussExpo, S0]

/-- The Ward equations for the series `e^E`. -/
theorem gaussSer_ward (lam : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    shiftA k (mexp (gaussExpo lam))
      - cC (1 / 4) * ∑ n ∈ Icc 1 (k - 1), pdA n (pdA (k - n) (mexp (gaussExpo lam)))
      + cC (Complex.I * lam) * pdA k (mexp (gaussExpo lam)) - levelA (mexp (gaussExpo lam))
      - cC (lam ^ 2 + ((k : ℂ) - 1) / 16) * mexp (gaussExpo lam) = 0 := by
  have hE0 := constantCoeff_gaussExpo lam
  have hpd : ∀ j, pdA j (mexp (gaussExpo lam)) = mexp (gaussExpo lam) * pdA j (gaussExpo lam) :=
    fun j => pderiv_mexp_zero hE0 _
  have hpd2 : ∀ n j, pdA n (pdA j (mexp (gaussExpo lam))) =
      mexp (gaussExpo lam) * (pdA n (gaussExpo lam) * pdA j (gaussExpo lam) +
        pdA n (pdA j (gaussExpo lam))) := by
    intro n j
    rw [hpd j]
    show MvPowerSeries.pderiv ℂ _ (mexp (gaussExpo lam) * pdA j (gaussExpo lam)) = _
    rw [Derivation.leibniz]
    have e : MvPowerSeries.pderiv ℂ n.toPNat' (mexp (gaussExpo lam)) =
        mexp (gaussExpo lam) * pdA n (gaussExpo lam) := hpd n
    rw [e]
    simp only [smul_eq_mul]
    show _ + pdA j (gaussExpo lam) * (mexp (gaussExpo lam) * pdA n (gaussExpo lam)) = _
    have e2 : MvPowerSeries.pderiv ℂ n.toPNat' (pdA j (gaussExpo lam)) =
        pdA n (pdA j (gaussExpo lam)) := rfl
    rw [e2]
    ring
  rw [shiftA_of_pd k _ _ _ hpd, levelA_of_pd _ _ _ hpd, hpd k,
    Finset.sum_congr rfl fun n _ => hpd2 n (k - n), ← Finset.mul_sum]
  linear_combination mexp (gaussExpo lam) * gaussExpo_pde lam hk

theorem coeff_gaussF (lam : ℂ) (N : ℕ) (γ : ℕ+ →₀ ℕ) :
    MvPolynomial.coeff γ (gaussF lam N) =
      if lvl γ = N then MvPowerSeries.coeff γ (mexp (gaussExpo lam)) else 0 := by
  classical
  simp only [gaussF, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rfl

theorem gaussF_mem_level (lam : ℂ) (N : ℕ) : gaussF lam N ∈ levelSub N := by
  intro γ hγ
  rw [coeff_gaussF] at hγ
  by_contra h
  exact hγ (if_neg h)

theorem coeff_gaussF_of_level (lam : ℂ) {j : ℕ} {δ : ℕ+ →₀ ℕ} (h : lvl δ = j) :
    MvPolynomial.coeff δ (gaussF lam j) = MvPowerSeries.coeff δ (mexp (gaussExpo lam)) := by
  rw [coeff_gaussF, if_pos h]

set_option maxHeartbeats 800000 in
/-- The pure Gaussian `exp(λ∑A_m u_m + ∑B_{m,n}u_m u_n)` solves the Ward equations
`l_k F = (l_0 + (k-1)/16)F` of the Fock module `ℱ_{0,λ}` (sphere/paper.tex l.1029–1035). -/
theorem gaussF_ward (lam : ℂ) : IsWardSeries (0 : ℂ) lam (1 / 16) (1 / 16) (gaussF lam) := by
  classical
  refine ⟨?_, fun m => gaussF_mem_level lam m, ?_⟩
  · ext γ
    rw [coeff_gaussF, MvPolynomial.coeff_one]
    by_cases h : γ = 0
    · subst h
      rw [if_pos (by simp [lvl]), if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        constantCoeff_mexp (constantCoeff_gaussExpo lam)]
    · rw [if_neg (fun h' => h (lvl_eq_zero h')), if_neg (Ne.symm h)]
  · intro k hk m
    ext γ
    by_cases hγ : lvl γ = m
    · subst hγ
      have hS := congrArg (MvPowerSeries.coeff γ) (gaussSer_ward lam hk)
      have hjk : ∀ j : ℕ, 1 ≤ j → ((j.toPNat' : ℕ+) : ℕ) = j := fun j hj => PNat.toPNat'_coe hj
      rw [ffOp_eq_ffOpR, ffOp_eq_ffOpR, coeff_ffOpR_pos _ _ k hk, MvPolynomial.coeff_add,
        coeff_ffOpR_zero, MvPolynomial.coeff_C_mul]
      simp only [MvPolynomial.coeff_pderiv]
      have e1 : ∀ j ∈ γ.support, MvPolynomial.coeff
          (γ - Finsupp.single j 1 + Finsupp.single ((j : ℕ) + k).toPNat' 1)
            (gaussF lam (lvl γ + k)) =
          MvPowerSeries.coeff (γ - Finsupp.single j 1 + Finsupp.single ((j : ℕ) + k).toPNat' 1)
            (mexp (gaussExpo lam)) := fun j hj => coeff_gaussF_of_level lam (by
        have e := congrArg lvl (sub_add_single hj)
        rw [lvl_add, lvl_single] at e
        rw [lvl_add, lvl_single, hjk _ (by omega)]
        omega)
      have e2 : ∀ n ∈ Icc 1 (k - 1), MvPolynomial.coeff
          (γ + Finsupp.single n.toPNat' 1 + Finsupp.single (k - n).toPNat' 1)
            (gaussF lam (lvl γ + k)) =
          MvPowerSeries.coeff (γ + Finsupp.single n.toPNat' 1 + Finsupp.single (k - n).toPNat' 1)
            (mexp (gaussExpo lam)) := fun n hn => coeff_gaussF_of_level lam (by
        have hn' := Finset.mem_Icc.1 hn
        rw [lvl_add, lvl_add, lvl_single, lvl_single, hjk _ hn'.1, hjk _ (by omega)]
        omega)
      have e3 : MvPolynomial.coeff (γ + Finsupp.single k.toPNat' 1) (gaussF lam (lvl γ + k)) =
          MvPowerSeries.coeff (γ + Finsupp.single k.toPNat' 1) (mexp (gaussExpo lam)) :=
        coeff_gaussF_of_level lam (by rw [lvl_add, lvl_single, hjk _ hk])
      rw [Finset.sum_congr rfl fun j hj => by rw [e1 j hj],
        Finset.sum_congr (s₁ := Icc 1 (k - 1)) rfl fun n hn => by rw [e2 n hn], e3,
        coeff_gaussF_of_level lam rfl]
      simp only [map_sub, map_add, map_zero, map_sum, coeff_shiftA, coeff_levelA, coeff_pdA, add_mul,
        MvPowerSeries.coeff_C_mul] at hS
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      linear_combination hS
    · rw [coeff_ffOp_pos_of_level 0 lam hk (gaussF_mem_level lam (m + k)) γ (by omega),
        MvPolynomial.coeff_add, ffOp_eq_ffOpR, coeff_ffOpR_zero, MvPolynomial.coeff_C_mul,
        coeff_gaussF, if_neg hγ]
      ring

end Virasoro.Sphere
