import Virasoro.Sphere.Proofs.Sec3C2Space
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Lemma 3.7, Step 3: the free-boson current (sphere paper)

sphere/paper.tex l.1114–1118.  The current `α(x) = ∑_{n≠0} α_n x^{-n-1}` on `ℱ^{(2)}` is the
family of its modes, `α_n = (i/√2) ∂_{u_n}` and `α_{-n} = -i√2 n u_n` for `n ≥ 1`.  The relation
`[l_{-k}^{(2)}, α(x)] = ∂_x(x^{1-k} α(x))` reads `[l_{-k}^{(2)}, α_N] = -N α_{N-k}` for each mode `N`
(with `α_0 = 0`).
-/

namespace Virasoro.Sphere

open MvPolynomial Finset

/-- `√2` as a complex number. -/
noncomputable def sqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

theorem sqrt2_mul : sqrt2 * sqrt2 = 2 := by
  unfold sqrt2
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem sqrt2_ne : sqrt2 ≠ 0 := fun h => by
  have h2 := sqrt2_mul
  rw [h, mul_zero] at h2
  norm_num at h2

/-- Multiplication by `u_n`. -/
noncomputable def uMul (n : ℕ) : Fock →ₗ[ℂ] Fock := LinearMap.mulLeft ℂ (uVar n)

theorem uMul_apply (n : ℕ) (f : Fock) : uMul n f = uVar n * f := rfl

/-- The modes of the free-boson current (sphere/paper.tex l.1115–1116):
`α_n = (i/√2) ∂_{u_n}`, `α_{-n} = -i√2 n u_n` for `n ≥ 1`, and `α_0 = 0`. -/
noncomputable def alphaOp (N : ℤ) : Fock →ₗ[ℂ] Fock :=
  if 0 < N then (Complex.I / sqrt2) • dVar N.toNat
  else if N < 0 then (-(Complex.I * sqrt2 * ((-N).toNat : ℂ))) • uMul (-N).toNat
  else 0

/-- `∑_{n=1}^{k-1} n(k-n) u_n u_{k-n}`. -/
noncomputable def Qk (k : ℕ) : Fock :=
  ∑ n ∈ Finset.Icc 1 (k - 1), ((n * (k - n) : ℕ) : ℂ) • ((uVar n : Fock) * uVar (k - n))

/-- `l_{-k}` at `μ = λ = 0` with the sum over `n` cut at `B`. -/
noncomputable def negB (k B : ℕ) : Fock →ₗ[ℂ] Fock :=
  ∑ n ∈ Finset.Icc 1 B, ((n + k : ℕ) : ℂ) • (uMul (n + k) ∘ₗ dVar n) -
    LinearMap.mulLeft ℂ (Qk k)

theorem negB_apply (k B : ℕ) (f : Fock) :
    negB k B f = ∑ n ∈ Finset.Icc 1 B, ((n + k : ℕ) : ℂ) • ((uVar (n + k) : Fock) * dVar n f) -
      Qk k * f := by
  simp only [negB, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, uMul_apply, LinearMap.mulLeft_apply]

theorem ffOp_neg_monomial (k : ℕ) (hk : 1 ≤ k) (β : ℕ+ →₀ ℕ) (c : ℂ) (B : ℕ)
    (hB : ∀ m ∈ β.support, (m : ℕ) ≤ B) :
    ffOp (0 : ℂ) 0 (-(k : ℤ)) (monomial β c) = negB k B (monomial β c) := by
  have hm : monomial β c = c • monomial β (1 : ℂ) := by rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul, ffOp_monomial]
  congr 1
  have hk0 : ¬ (-(k : ℤ)) = 0 := by omega
  have hkp : ¬ 0 < (-(k : ℤ)) := by omega
  have hKK : (-(-(k : ℤ))).toNat = k := by simp
  rw [negB_apply]
  unfold ffOpMono
  simp only [if_neg hk0, if_neg hkp, hKK, mul_zero, zero_mul, sub_zero, map_zero, add_zero]
  rw [Qk]
  congr 1
  refine Finset.sum_subset (Finset.Icc_subset_Icc_right (Finset.sup_le hB)) fun n hn hn' => ?_
  have hn1 := (Finset.mem_Icc.1 hn).1
  have hgt : (β.support.sup fun m : ℕ+ => (m : ℕ)) < n := by
    by_contra hle
    exact hn' (Finset.mem_Icc.2 ⟨hn1, not_lt.1 hle⟩)
  have h0 : β n.toPNat' = 0 := by
    by_contra hne
    have hmem : n.toPNat' ∈ β.support := Finsupp.mem_support_iff.mpr hne
    have hle := Finset.le_sup (f := fun m : ℕ+ => (m : ℕ)) hmem
    rw [PNat.toPNat'_coe hn1] at hle
    omega
  have hd : dVar n (monomial β (1 : ℂ)) = 0 := by
    show pderiv n.toPNat' (monomial β (1 : ℂ)) = 0
    rw [pderiv_monomial, h0]
    simp
  rw [hd, mul_zero, smul_zero]

theorem dVar_mul (n : ℕ) (a b : Fock) : dVar n (a * b) = dVar n a * b + a * dVar n b :=
  pderiv_mul

theorem toPNat'_inj {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a.toPNat' = b.toPNat') : a = b := by
  have h1 := congrArg (fun m : ℕ+ => (m : ℕ)) h
  simp only [PNat.toPNat'_coe ha, PNat.toPNat'_coe hb] at h1
  exact h1

theorem dVar_uVar {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    dVar a (uVar b : Fock) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    rw [if_pos rfl]
    exact pderiv_X_self _
  · rw [if_neg h]
    exact pderiv_X_of_ne fun h' => h (toPNat'_inj ha hb h'.symm)

theorem dVar_comm (a b : ℕ) (f : Fock) : dVar a (dVar b f) = dVar b (dVar a f) := by
  show pderiv a.toPNat' (pderiv b.toPNat' f) = pderiv b.toPNat' (pderiv a.toPNat' f)
  by_cases h : a.toPNat' = b.toPNat'
  · rw [h]
  · ext γ
    simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply, if_neg h,
      if_neg (Ne.symm h), add_zero]
    rw [add_right_comm]
    ring

theorem dVar_Qk (k n : ℕ) (hn : 1 ≤ n) :
    dVar n (Qk k) = if n < k then ((2 * n * (k - n) : ℕ) : ℂ) • (uVar (k - n) : Fock) else 0 := by
  have e : ∀ m ∈ Finset.Icc 1 (k - 1),
      dVar n (((m * (k - m) : ℕ) : ℂ) • ((uVar m : Fock) * uVar (k - m))) =
        (if m = n then ((m * (k - m) : ℕ) : ℂ) • (uVar (k - m) : Fock) else 0) +
          (if m = k - n then ((m * (k - m) : ℕ) : ℂ) • (uVar m : Fock) else 0) := by
    intro m hm
    have hm' := Finset.mem_Icc.1 hm
    rw [map_smul, dVar_mul, dVar_uVar hn hm'.1, dVar_uVar hn (by omega), smul_add]
    congr 1
    · by_cases h : m = n
      · rw [if_pos h, if_pos h.symm, one_mul]
      · rw [if_neg h, if_neg (Ne.symm h), zero_mul, smul_zero]
    · by_cases h : m = k - n
      · rw [if_pos h, if_pos (by omega), mul_one]
      · rw [if_neg h, if_neg (by omega), mul_zero, smul_zero]
  rw [Qk, map_sum, Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  by_cases h : n < k
  · rw [if_pos h, if_pos (Finset.mem_Icc.2 ⟨hn, by omega⟩),
      if_pos (Finset.mem_Icc.2 ⟨by omega, by omega⟩), ← add_smul]
    congr 1
    rw [show k - (k - n) = n by omega]
    push_cast
    ring
  · rw [if_neg h, if_neg (fun h' => by have := Finset.mem_Icc.1 h'; omega),
      if_neg (fun h' => by have := Finset.mem_Icc.1 h'; omega), add_zero]

theorem negB_dVar (k B n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) (f : Fock) :
    negB k B (dVar n f) - dVar n (negB k B f) =
      -(if k < n ∧ n - k ≤ B then (n : ℂ) • dVar (n - k) f else 0) + dVar n (Qk k) * f := by
  have hs : ∑ j ∈ Finset.Icc 1 B,
      ((j + k : ℕ) : ℂ) • (dVar n (uVar (j + k) : Fock) * dVar j f) =
      if k < n ∧ n - k ≤ B then (n : ℂ) • dVar (n - k) f else 0 := by
    by_cases h : k < n ∧ n - k ≤ B
    · rw [if_pos h, Finset.sum_eq_single (n - k)]
      · rw [dVar_uVar hn (by omega), if_pos (by omega), one_mul, Nat.sub_add_cancel h.1.le]
      · intro j hj hne
        have hj' := Finset.mem_Icc.1 hj
        rw [dVar_uVar hn (by omega), if_neg (by omega), zero_mul, smul_zero]
      · intro hnot
        exact absurd (Finset.mem_Icc.2 ⟨by omega, h.2⟩) hnot
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_Icc.1 hj
      rw [dVar_uVar hn (by omega), if_neg (by omega), zero_mul, smul_zero]
  have e : ∀ j ∈ Finset.Icc 1 B,
      dVar n (((j + k : ℕ) : ℂ) • ((uVar (j + k) : Fock) * dVar j f)) =
        ((j + k : ℕ) : ℂ) • (dVar n (uVar (j + k) : Fock) * dVar j f) +
          ((j + k : ℕ) : ℂ) • ((uVar (j + k) : Fock) * dVar j (dVar n f)) := by
    intro j _
    rw [map_smul, dVar_mul, dVar_comm n j, smul_add]
  rw [negB_apply, negB_apply, map_sub, map_sum, dVar_mul, Finset.sum_congr rfl e,
    Finset.sum_add_distrib, hs]
  abel

theorem negB_uMul (k B n : ℕ) (hn : 1 ≤ n) (f : Fock) :
    negB k B (uVar n * f) - uVar n * negB k B f =
      if n ≤ B then ((n + k : ℕ) : ℂ) • ((uVar (n + k) : Fock) * f) else 0 := by
  have hs : ∑ j ∈ Finset.Icc 1 B,
      ((j + k : ℕ) : ℂ) • ((uVar (j + k) : Fock) * (dVar j (uVar n : Fock) * f)) =
      if n ≤ B then ((n + k : ℕ) : ℂ) • ((uVar (n + k) : Fock) * f) else 0 := by
    by_cases h : n ≤ B
    · rw [if_pos h, Finset.sum_eq_single n]
      · rw [dVar_uVar hn hn, if_pos rfl, one_mul]
      · intro j hj hne
        have hj' := Finset.mem_Icc.1 hj
        rw [dVar_uVar hj'.1 hn, if_neg hne, zero_mul, mul_zero, smul_zero]
      · intro hnot
        exact absurd (Finset.mem_Icc.2 ⟨hn, h⟩) hnot
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' := Finset.mem_Icc.1 hj
      rw [dVar_uVar hj'.1 hn, if_neg (by omega), zero_mul, mul_zero, smul_zero]
  have e : ∀ j ∈ Finset.Icc 1 B,
      ((j + k : ℕ) : ℂ) • ((uVar (j + k) : Fock) * dVar j (uVar n * f)) =
        ((j + k : ℕ) : ℂ) • ((uVar (j + k) : Fock) * (dVar j (uVar n : Fock) * f)) +
          uVar n * (((j + k : ℕ) : ℂ) • ((uVar (j + k) : Fock) * dVar j f)) := by
    intro j _
    rw [dVar_mul, mul_add, smul_add, mul_smul_comm]
    congr 2
    ring
  rw [negB_apply, negB_apply, Finset.sum_congr rfl e, Finset.sum_add_distrib, hs,
    ← Finset.mul_sum]
  ring

/-- `[l_{-k}^{(2)}, α_N] = -N α_{N-k}` (sphere/paper.tex l.1117:
`[l_{-k}^{(2)}, α(x)] = ∂_x(x^{1-k} α(x))` at each power of `x`). -/
theorem ffOp_alphaOp (k : ℕ) (hk : 1 ≤ k) (N : ℤ) (f : Fock) :
    ffOp (0 : ℂ) 0 (-(k : ℤ)) (alphaOp N f) - alphaOp N (ffOp (0 : ℂ) 0 (-(k : ℤ)) f) =
      -(N : ℂ) • alphaOp (N - k) f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, smul_add] at hp hq ⊢
    rw [← hp, ← hq]
    abel
  | monomial α c =>
    set B := (α.support.sup fun m : ℕ+ => (m : ℕ)) + N.natAbs + k with hBdef
    have hBα : ∀ m ∈ α.support, (m : ℕ) ≤ B := fun m hm => by
      have := Finset.le_sup (f := fun m : ℕ+ => (m : ℕ)) hm
      omega
    rcases lt_trichotomy N 0 with hN | hN | hN
    · -- `N = -n`
      obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, 1 ≤ n ∧ N = -(n : ℤ) := ⟨(-N).toNat, by omega, by omega⟩
      have hA : alphaOp (-(n : ℤ)) = (-(Complex.I * sqrt2 * (n : ℂ))) • uMul n := by
        rw [alphaOp, if_neg (by omega), if_pos (by omega)]
        simp
      have hA' : alphaOp (-(n : ℤ) - k) =
          (-(Complex.I * sqrt2 * ((n + k : ℕ) : ℂ))) • uMul (n + k) := by
        rw [alphaOp, if_neg (by omega), if_pos (by omega)]
        have e : (-(-(n : ℤ) - k)).toNat = n + k := by omega
        rw [e]
      have hmon : (uVar n : Fock) * monomial α c = monomial (Finsupp.single n.toPNat' 1 + α) c := by
        show monomial (Finsupp.single n.toPNat' 1) (1 : ℂ) * monomial α c = _
        rw [monomial_mul, one_mul]
      have hB2 : ∀ m : ℕ+, m ∈ (Finsupp.single n.toPNat' 1 + α).support → (m : ℕ) ≤ B := by
        intro m hm
        rcases Finset.mem_union.1 (Finsupp.support_add hm) with h | h
        · have h1 := Finsupp.support_single_subset h
          rw [Finset.mem_singleton] at h1
          rw [h1, PNat.toPNat'_coe hn]
          omega
        · exact hBα m h
      rw [hA, hA', LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, uMul_apply,
        uMul_apply, map_smul, hmon, ffOp_neg_monomial k hk _ c B hB2,
        ffOp_neg_monomial k hk α c B hBα, ← hmon, ← smul_sub, negB_uMul k B n hn,
        if_pos (by omega), smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    · subst hN
      have hA : alphaOp 0 = 0 := by
        rw [alphaOp, if_neg (by omega), if_neg (by omega)]
      rw [hA]
      simp
    · -- `N = n`
      obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, 1 ≤ n ∧ N = (n : ℤ) := ⟨N.toNat, by omega, by omega⟩
      have hA : alphaOp (n : ℤ) = (Complex.I / sqrt2) • dVar n := by
        rw [alphaOp, if_pos (by omega)]
        simp
      have hmon : dVar n (monomial α c) =
          monomial (α - Finsupp.single n.toPNat' 1) (c * (α n.toPNat' : ℂ)) :=
        pderiv_monomial
      have hB2 : ∀ m : ℕ+, m ∈ (α - Finsupp.single n.toPNat' 1).support → (m : ℕ) ≤ B := by
        intro m hm
        refine hBα m ?_
        rw [Finsupp.mem_support_iff] at hm ⊢
        rw [Finsupp.tsub_apply] at hm
        omega
      rw [hA, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, hmon,
        ffOp_neg_monomial k hk _ _ B hB2, ffOp_neg_monomial k hk α c B hBα, ← hmon, ← smul_sub,
        negB_dVar k B n hk hn, dVar_Qk k n hn]
      rcases lt_trichotomy n k with h | h | h
      · have hA' : alphaOp ((n : ℤ) - k) =
            (-(Complex.I * sqrt2 * ((k - n : ℕ) : ℂ))) • uMul (k - n) := by
          rw [alphaOp, if_neg (by omega), if_pos (by omega)]
          have e : (-((n : ℤ) - k)).toNat = k - n := by omega
          rw [e]
        rw [if_neg (by omega), if_pos h, hA', LinearMap.smul_apply, uMul_apply, neg_zero,
          zero_add, smul_mul_assoc, smul_smul, smul_smul]
        congr 1
        have h2 := sqrt2_mul
        have h3 := sqrt2_ne
        have h4 : Complex.I / sqrt2 = Complex.I * sqrt2 / 2 := by
          rw [div_eq_div_iff h3 two_ne_zero]
          linear_combination (-Complex.I) * h2
        rw [h4]
        push_cast
        ring
      · subst h
        have hA' : alphaOp ((n : ℤ) - n) = 0 := by
          rw [alphaOp, if_neg (by omega), if_neg (by omega)]
        rw [if_neg (by omega), if_neg (by omega), hA']
        simp
      · have hA' : alphaOp ((n : ℤ) - k) = (Complex.I / sqrt2) • dVar (n - k) := by
          rw [alphaOp, if_pos (by omega)]
          have e : ((n : ℤ) - k).toNat = n - k := by omega
          rw [e]
        rw [if_pos ⟨h, by omega⟩, if_neg (by omega), hA', LinearMap.smul_apply, zero_mul,
          add_zero, smul_neg, smul_smul, smul_smul]
        rw [← neg_smul]
        congr 1
        push_cast
        ring

end Virasoro.Sphere
