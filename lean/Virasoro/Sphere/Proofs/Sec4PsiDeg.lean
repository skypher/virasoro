import Virasoro.Sphere.Proofs.Sec4BfromH
import Virasoro.Sphere.Proofs.RegEval

/-!
# Sphere paper equation (2.8): the degrees of the coefficients `ψ_r`

`sphere/paper.tex` l.393–395: `ψ_r(c,Δ,Δ_i) ∈ ℚ[c,Δ,Δ_1,…,Δ_4]` has degree `r` in `Δ`, with
leading term `Δ^r/(2^r r!)` (from `16q(z)/z = 1 + z/2 + O(z²)`).  Here: `[z^r] Φ̃(q(z))` is a
polynomial in `Δ` of degree at most `r` whose coefficient of `Δ^r` is
`(1/r!) · ([q¹](16q/z(q)))^r · ([z¹]q(z))^r ≠ 0`.
-/

namespace Virasoro.Sphere

open PowerSeries

section PolyLe

variable {𝔽 : Type*} [Field 𝔽]

/-- `r ∈ 𝔽(Δ)` is a polynomial in `Δ` of degree at most `n` whose coefficient of `Δ^n` is
`a`. -/
def PolyLe (r : RatFunc 𝔽) (n : ℕ) (a : 𝔽) : Prop :=
  ∃ p : Polynomial 𝔽, r = algebraMap (Polynomial 𝔽) (RatFunc 𝔽) p ∧ p.natDegree ≤ n ∧
    p.coeff n = a

theorem polyLe_C (x : 𝔽) : PolyLe (RatFunc.C x) 0 x :=
  ⟨Polynomial.C x, (RatFunc.algebraMap_C x).symm, by simp, by simp⟩

theorem polyLe_zero (n : ℕ) : PolyLe (0 : RatFunc 𝔽) n 0 :=
  ⟨0, by simp, by simp, by simp⟩

theorem PolyLe.mul {r s : RatFunc 𝔽} {n m : ℕ} {a b : 𝔽} (hr : PolyLe r n a)
    (hs : PolyLe s m b) : PolyLe (r * s) (n + m) (a * b) := by
  obtain ⟨p, rfl, hp, rfl⟩ := hr
  obtain ⟨q, rfl, hq, rfl⟩ := hs
  exact ⟨p * q, (map_mul _ _ _).symm, Polynomial.natDegree_mul_le_of_le hp hq,
    Polynomial.coeff_mul_add_eq_of_natDegree_le hp hq⟩

theorem PolyLe.add {r s : RatFunc 𝔽} {n : ℕ} {a b : 𝔽} (hr : PolyLe r n a)
    (hs : PolyLe s n b) : PolyLe (r + s) n (a + b) := by
  obtain ⟨p, rfl, hp, rfl⟩ := hr
  obtain ⟨q, rfl, hq, rfl⟩ := hs
  exact ⟨p + q, (map_add _ _ _).symm, Polynomial.natDegree_add_le_of_degree_le hp hq,
    Polynomial.coeff_add p q n⟩

theorem PolyLe.weaken {r : RatFunc 𝔽} {d n : ℕ} {a : 𝔽} (hr : PolyLe r d a) (hdn : d ≤ n) :
    PolyLe r n (if d = n then a else 0) := by
  obtain ⟨p, rfl, hp, rfl⟩ := hr
  refine ⟨p, rfl, hp.trans hdn, ?_⟩
  by_cases h : d = n
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

theorem PolyLe.sum {ι : Type*} (s : Finset ι) {f : ι → RatFunc 𝔽} {n : ℕ} {a : ι → 𝔽}
    (h : ∀ i ∈ s, PolyLe (f i) n (a i)) : PolyLe (∑ i ∈ s, f i) n (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact polyLe_zero n
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem PolyLe.sum_weaken {ι : Type*} (s : Finset ι) {f : ι → RatFunc 𝔽} {d : ι → ℕ} {n : ℕ}
    {a : ι → 𝔽} (h : ∀ i ∈ s, PolyLe (f i) (d i) (a i)) (hd : ∀ i ∈ s, d i ≤ n) :
    PolyLe (∑ i ∈ s, f i) n (∑ i ∈ s, if d i = n then a i else 0) :=
  PolyLe.sum s fun i hi => (h i hi).weaken (hd i hi)

end PolyLe

section Coeffs

variable {A : Type*} [Field A]

theorem coeff_pow_self {u : PowerSeries A} (hu : constantCoeff u = 0) (n : ℕ) :
    coeff n (u ^ n) = coeff 1 u ^ n := by
  have h := sub_const_eq_X_mul_shift u
  rw [hu, map_zero, sub_zero] at h
  have h2 : u ^ n = X ^ n * (PowerSeries.mk fun p => coeff (p + 1) u) ^ n := by
    rw [← mul_pow, ← h]
  have h3 := coeff_X_pow_mul ((PowerSeries.mk fun p => coeff (p + 1) u) ^ n) n 0
  rw [zero_add] at h3
  rw [h2, h3, coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply,
    coeff_mk]

theorem coeff_one_mul' (f g : PowerSeries A) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  simp [coeff_mul, Finset.Nat.antidiagonal_succ]

theorem coeff_one_pow' {f : PowerSeries A} (hf : coeff 0 f = 1) (n : ℕ) :
    coeff 1 (f ^ n) = n * coeff 1 f := by
  induction n with
  | zero => simp [PowerSeries.coeff_one]
  | succ n ih =>
    have h0 : coeff 0 (f ^ n) = 1 := by
      rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply, hf,
        one_pow]
    rw [pow_succ, coeff_one_mul', ih, h0, hf]
    push_cast
    ring

theorem coeff_one_nomeRatio : coeff 1 (nomeRatio ℚ) = 8 := by
  have hψ0 : coeff 0 (thPsi ℚ) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_thPsi]
  have hθ0 : coeff 0 (th3 ℚ) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_th3]
  have hψ1 : coeff 1 (thPsi ℚ) = 0 := by
    simp [thPsi, thetaPsiZ, coeff_map, coeff_mk]
  have hθ1 : coeff 1 (th3 ℚ) = 2 := by
    simp [th3, theta3Z, coeff_map, coeff_mk]
  have hc : constantCoeff (thPsi ℚ ^ 4) ≠ 0 := by
    rw [map_pow, constantCoeff_thPsi]
    norm_num
  have h : nomeRatio ℚ * thPsi ℚ ^ 4 = th3 ℚ ^ 4 := by
    rw [nomeRatio, mul_assoc, PowerSeries.inv_mul_cancel _ hc, mul_one]
  have h1 := congrArg (coeff 1) h
  have h0 : coeff 0 (thPsi ℚ ^ 4) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_thPsi, one_pow]
  rw [coeff_one_mul', coeff_one_pow' hψ0, coeff_one_pow' hθ0, hψ1, hθ1, h0] at h1
  norm_num at h1
  linarith

theorem coeff_one_Q0 : coeff 1 Q0 = 1 / 16 := by
  have h := congrArg (coeff 1) zq_subst_Q0
  have hz : zq ℚ = PowerSeries.mk fun k => coeff k (zq ℚ) := by
    ext k
    rw [coeff_mk]
  rw [hz, ← compS_eq_subst _ constantCoeff_Q0, coeff_compS_le constantCoeff_Q0 _ le_rfl,
    Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, PowerSeries.coeff_one,
    if_neg one_ne_zero,
    mul_zero, zero_add, coeff_one_zq, coeff_one_X] at h
  linarith

end Coeffs

section Psi

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

theorem coeff_subst_Qr (f : PowerSeries (RatFunc 𝔽)) {n M : ℕ} (h : n ≤ M) :
    coeff n (f.subst (Qr 𝔽)) =
      ∑ j ∈ Finset.range (M + 1), coeff j f * coeff n (Qr 𝔽 ^ j) := by
  have hf : f = PowerSeries.mk fun m => coeff m f := by
    ext m
    rw [coeff_mk]
  conv_lhs => rw [hf]
  rw [← compS_eq_subst _ constantCoeff_Qr, coeff_compS_le constantCoeff_Qr _ h]

theorem coeff_Qr_pow (n j : ℕ) :
    coeff n (Qr 𝔽 ^ j) = RatFunc.C (algebraMap ℚ 𝔽 (coeff n (Q0 ^ j))) := by
  rw [Qr, ← map_pow, coeff_map, ratCast_eq_C]

theorem coeff_map_sub_one_pow (g : PowerSeries ℚ) (n k : ℕ) :
    coeff n ((PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g - 1) ^ k) =
      RatFunc.C (algebraMap ℚ 𝔽 (coeff n ((g - 1) ^ k))) := by
  have e : (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g - 1) ^ k =
      PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) ((g - 1) ^ k) := by
    rw [map_pow, map_sub, map_one]
  rw [e, coeff_map, ratCast_eq_C]

theorem gbinom_C (x : 𝔽) (k : ℕ) :
    gbinom (RatFunc.C x : RatFunc 𝔽) k = RatFunc.C (gbinom x k) := by
  simp only [gbinom, map_div₀, map_prod, map_sub, map_natCast]

/-- `binom(Δ - κ, k)` is a polynomial in `Δ` of degree at most `k` with top coefficient
`1/k!`. -/
theorem polyLe_gbinom (κ : 𝔽) (k : ℕ) :
    PolyLe (gbinom (RatFunc.X - RatFunc.C κ : RatFunc 𝔽) k) k ((k.factorial : 𝔽)⁻¹) := by
  have hprod : ∀ m : ℕ, PolyLe
      (∏ i ∈ Finset.range m, (RatFunc.X - RatFunc.C κ - (i : RatFunc 𝔽))) m 1 := by
    intro m
    induction m with
    | zero =>
      rw [Finset.prod_range_zero]
      simpa using polyLe_C (1 : 𝔽)
    | succ m ih =>
      rw [Finset.prod_range_succ]
      have h1 : PolyLe (RatFunc.X - RatFunc.C κ - (m : RatFunc 𝔽)) 1 1 := by
        refine ⟨Polynomial.X - Polynomial.C (κ + m), ?_, ?_, ?_⟩
        · simp [RatFunc.algebraMap_X, RatFunc.algebraMap_C]
          ring
        · exact (Polynomial.natDegree_X_sub_C _).le
        · simp
      simpa using ih.mul h1
  have hc := polyLe_C ((k.factorial : 𝔽)⁻¹)
  have h := (hprod k).mul hc
  rw [add_zero, one_mul] at h
  have e : gbinom (RatFunc.X - RatFunc.C κ : RatFunc 𝔽) k =
      (∏ i ∈ Finset.range k, (RatFunc.X - RatFunc.C κ - (i : RatFunc 𝔽))) *
        RatFunc.C ((k.factorial : 𝔽)⁻¹) := by
    rw [gbinom, div_eq_mul_inv, map_inv₀, map_natCast]
  rw [e]
  exact h

/-- `[z^i] (16q(z)/z(q(z)))^{Δ-κ}` is a polynomial in `Δ` of degree at most `i` with top
coefficient `(1/i!) ([q^i](16q/z - 1)^i) ([z^i] q(z)^i)`. -/
theorem polyLe_first (κ : 𝔽) (i : ℕ) :
    PolyLe
      (coeff i ((fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ))
        (RatFunc.X - RatFunc.C κ)).subst (Qr 𝔽))) i
      ((i.factorial : 𝔽)⁻¹ * algebraMap ℚ 𝔽 (coeff i ((nomeRatio ℚ - 1) ^ i)) *
        algebraMap ℚ 𝔽 (coeff i (Q0 ^ i))) := by
  have hF : ∀ j : ℕ, PolyLe
      (coeff j (fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ))
        (RatFunc.X - RatFunc.C κ))) j
      ((j.factorial : 𝔽)⁻¹ * algebraMap ℚ 𝔽 (coeff j ((nomeRatio ℚ - 1) ^ j))) := by
    intro j
    have h := PolyLe.sum_weaken (Finset.range (j + 1))
      (f := fun k => gbinom (RatFunc.X - RatFunc.C κ : RatFunc 𝔽) k *
        coeff j ((PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ) - 1) ^ k))
      (d := fun k => k + 0) (n := j)
      (a := fun k => (k.factorial : 𝔽)⁻¹ * algebraMap ℚ 𝔽 (coeff j ((nomeRatio ℚ - 1) ^ k)))
      (fun k _ => by
        rw [coeff_map_sub_one_pow]
        exact (polyLe_gbinom κ k).mul (polyLe_C _))
      (fun k hk => by have := Finset.mem_range.1 hk; omega)
    simp only [add_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, if_true] at h
    simpa only [Virasoro.Sphere.fpow, coeff_mk] using h
  have h := PolyLe.sum_weaken (Finset.range (i + 1))
    (f := fun j => coeff j (fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ))
        (RatFunc.X - RatFunc.C κ)) * coeff i (Qr 𝔽 ^ j))
    (d := fun j => j + 0) (n := i)
    (a := fun j => (j.factorial : 𝔽)⁻¹ * algebraMap ℚ 𝔽 (coeff j ((nomeRatio ℚ - 1) ^ j)) *
      algebraMap ℚ 𝔽 (coeff i (Q0 ^ j)))
    (fun j _ => by
      rw [coeff_Qr_pow]
      exact (hF j).mul (polyLe_C _))
    (fun j hj => by have := Finset.mem_range.1 hj; omega)
  simp only [add_zero, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_self, if_true] at h
  rw [coeff_subst_Qr _ le_rfl]
  exact h

/-- The coefficients of `f^a`, `f` rational and `a` constant in `Δ`, are constants. -/
theorem coeff_fpow_const (g : PowerSeries ℚ) (x : 𝔽) (n : ℕ) :
    ∃ y : 𝔽, coeff n (fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g) (RatFunc.C x)) =
      RatFunc.C y := by
  refine ⟨∑ k ∈ Finset.range (n + 1), gbinom x k * algebraMap ℚ 𝔽 (coeff n ((g - 1) ^ k)), ?_⟩
  simp only [Virasoro.Sphere.fpow, coeff_mk, coeff_map_sub_one_pow, gbinom_C, map_sum, map_mul]

/-- Constants in `Δ` are closed under products of series and under `q = q(z)`. -/
theorem coeff_const_mul {f g : PowerSeries (RatFunc 𝔽)}
    (hf : ∀ n, ∃ y : 𝔽, coeff n f = RatFunc.C y) (hg : ∀ n, ∃ y : 𝔽, coeff n g = RatFunc.C y)
    (n : ℕ) : ∃ y : 𝔽, coeff n (f * g) = RatFunc.C y := by
  choose a ha using hf
  choose b hb using hg
  refine ⟨∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)), a p.1 * b p.2, ?_⟩
  rw [coeff_mul, map_sum]
  exact Finset.sum_congr rfl fun p _ => by rw [ha, hb, map_mul]

theorem coeff_const_subst {f : PowerSeries (RatFunc 𝔽)}
    (hf : ∀ n, ∃ y : 𝔽, coeff n f = RatFunc.C y) (n : ℕ) :
    ∃ y : 𝔽, coeff n (f.subst (Qr 𝔽)) = RatFunc.C y := by
  choose a ha using hf
  refine ⟨∑ j ∈ Finset.range (n + 1), a j * algebraMap ℚ 𝔽 (coeff n (Q0 ^ j)), ?_⟩
  rw [coeff_subst_Qr _ le_rfl, map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [ha, coeff_Qr_pow, map_mul]

theorem PhiTilde_split (c : 𝔽) (Δe : Fin 4 → 𝔽) :
    PhiTilde c Δe =
      fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ))
          (RatFunc.X - RatFunc.C ((c - 1) / 24)) *
        (fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (1 - zq ℚ))
            (RatFunc.C ((c - 1) / 24 - Δe 1 - Δe 2)) *
          fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (th3 ℚ))
            (RatFunc.C ((c - 1) / 2 - 4 * (Δe 0 + Δe 1 + Δe 2 + Δe 3)))) := by
  rw [map_nomeRatio, map_sub, map_one, map_zq, map_th3, PhiTilde, mul_assoc]
  simp only [map_sub, map_div₀, map_one, map_mul, map_ofNat, map_add]

/-- `ψ_n = [z^n]Φ̃(q(z))` is a polynomial in `Δ` of degree at most `n` with nonzero coefficient
of `Δ^n` (l.393–395). -/
theorem polyLe_psiZ (c : 𝔽) (Δe : Fin 4 → 𝔽) (n : ℕ) :
    ∃ a : 𝔽, a ≠ 0 ∧ PolyLe (psiZ c Δe n) n a := by
  set F1 := fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ))
    (RatFunc.X - RatFunc.C ((c - 1) / 24)) with hF1
  set G := fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (1 - zq ℚ))
      (RatFunc.C ((c - 1) / 24 - Δe 1 - Δe 2)) *
    fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (th3 ℚ))
      (RatFunc.C ((c - 1) / 2 - 4 * (Δe 0 + Δe 1 + Δe 2 + Δe 3))) with hG
  have hGc : ∀ j, ∃ y : 𝔽, coeff j (G.subst (Qr 𝔽)) = RatFunc.C y :=
    coeff_const_subst (coeff_const_mul (coeff_fpow_const _ _) (coeff_fpow_const _ _))
  choose y hy using hGc
  have hG0 : coeff 0 (G.subst (Qr 𝔽)) = 1 := by
    rw [coeff_subst_Qr _ le_rfl, Finset.sum_range_one, pow_zero, coeff_zero_one, mul_one, hG,
      coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton, fpow_coeff_zero,
      fpow_coeff_zero, mul_one]
  have hy0 : y 0 = 1 := by
    have := (hy 0).symm.trans hG0
    exact RatFunc.C_injective (by rw [this, map_one])
  have h := PolyLe.sum_weaken (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ))
    (f := fun p => coeff p.1 (F1.subst (Qr 𝔽)) * coeff p.2 (G.subst (Qr 𝔽)))
    (d := fun p => p.1 + 0) (n := n)
    (a := fun p => (p.1.factorial : 𝔽)⁻¹ *
      algebraMap ℚ 𝔽 (coeff p.1 ((nomeRatio ℚ - 1) ^ p.1)) *
      algebraMap ℚ 𝔽 (coeff p.1 (Q0 ^ p.1)) * y p.2)
    (fun p _ => by
      rw [hy]
      exact (polyLe_first _ p.1).mul (polyLe_C _))
    (fun p hp => by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega)
  have hsum : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
      if p.1 + 0 = n then (p.1.factorial : 𝔽)⁻¹ *
        algebraMap ℚ 𝔽 (coeff p.1 ((nomeRatio ℚ - 1) ^ p.1)) *
        algebraMap ℚ 𝔽 (coeff p.1 (Q0 ^ p.1)) * y p.2 else 0) =
      (n.factorial : 𝔽)⁻¹ * algebraMap ℚ 𝔽 (coeff n ((nomeRatio ℚ - 1) ^ n)) *
        algebraMap ℚ 𝔽 (coeff n (Q0 ^ n)) := by
    rw [Finset.sum_eq_single (n, 0)]
    · rw [if_pos (add_zero n), hy0, mul_one]
    · rintro ⟨i, j⟩ hp hne
      have hij := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      refine if_neg fun h0 => hne ?_
      simp only [add_zero] at h0 hij
      rw [Prod.mk.injEq]
      omega
    · intro h0
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (add_zero n)) h0
  rw [hsum] at h
  refine ⟨(n.factorial : 𝔽)⁻¹ * algebraMap ℚ 𝔽 (coeff n ((nomeRatio ℚ - 1) ^ n)) *
    algebraMap ℚ 𝔽 (coeff n (Q0 ^ n)), ?_, ?_⟩
  rotate_left
  · rw [psiZ, PhiTilde_split, ← hF1, ← hG, subst_mul hasSubst_Qr, coeff_mul]
    exact h
  · have hu : constantCoeff (nomeRatio ℚ - 1) = 0 := by
      rw [map_sub, constantCoeff_nomeRatio, map_one, sub_self]
    have h8 : coeff 1 (nomeRatio ℚ - 1) = 8 := by
      rw [map_sub, coeff_one_nomeRatio, PowerSeries.coeff_one, if_neg one_ne_zero, sub_zero]
    rw [coeff_pow_self hu, coeff_pow_self constantCoeff_Q0, h8, coeff_one_Q0]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)))
      ?_) ?_
    · exact (map_ne_zero (algebraMap ℚ 𝔽)).2 (pow_ne_zero n (by norm_num))
    · exact (map_ne_zero (algebraMap ℚ 𝔽)).2 (pow_ne_zero n (by norm_num))

theorem wZ_zero (c : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) : wZ c Δe N 0 = psiZ c Δe N := by
  rw [wZ, Finset.sum_eq_single (N, 0)]
  · rw [pow_zero, pow_zero, coeff_zero_one, mul_one, mul_one]
  · rintro ⟨i, j⟩ hp hne
    have hij := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have hj : j ≠ 0 := by
      intro h0
      apply hne
      rw [Prod.mk.injEq]
      simp only at hij
      omega
    rw [pow_zero, pow_zero, PowerSeries.coeff_one, if_neg hj, mul_zero, mul_zero]
  · intro h0
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (add_zero N)) h0

/-- `[z^N](Φ̃(q(z)) (16q(z))^m)` is a polynomial in `Δ` of degree at most `N - m`. -/
theorem polyLe_wZ (c : 𝔽) (Δe : Fin 4 → 𝔽) {N m : ℕ} (hm : m ≤ N) :
    ∃ a : 𝔽, PolyLe (wZ c Δe N m) (N - m) a := by
  have hterm : ∀ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      PolyLe (psiZ c Δe p.1 * (16 ^ m * coeff p.2 (Qr 𝔽 ^ m))) (N - m) 0 ∨
        ∃ a, PolyLe (psiZ c Δe p.1 * (16 ^ m * coeff p.2 (Qr 𝔽 ^ m))) (N - m) a := by
    intro p hp
    have hij := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases hlt : p.2 < m
    · left
      rw [coeff_pow_of_lt constantCoeff_Qr hlt, mul_zero, mul_zero]
      exact polyLe_zero _
    · right
      obtain ⟨a, -, ha⟩ := polyLe_psiZ c Δe p.1
      have h16 : (16 : RatFunc 𝔽) ^ m * coeff p.2 (Qr 𝔽 ^ m) =
          RatFunc.C ((16 : 𝔽) ^ m * algebraMap ℚ 𝔽 (coeff p.2 (Q0 ^ m))) := by
        rw [coeff_Qr_pow, map_mul]
        congr 1
        rw [map_pow (RatFunc.C : 𝔽 →+* RatFunc 𝔽), map_ofNat]
      rw [h16]
      exact ⟨_, (ha.mul (polyLe_C _)).weaken (by omega)⟩
  have hall : ∀ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      ∃ a, PolyLe (psiZ c Δe p.1 * (16 ^ m * coeff p.2 (Qr 𝔽 ^ m))) (N - m) a := by
    intro p hp
    rcases hterm p hp with h | h
    · exact ⟨0, h⟩
    · exact h
  classical
  let a : ℕ × ℕ → 𝔽 := fun p =>
    if hp : p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ))
    then Classical.choose (hall p hp) else 0
  refine ⟨∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)), a p, ?_⟩
  rw [wZ]
  refine PolyLe.sum _ fun p hp => ?_
  have := Classical.choose_spec (hall p hp)
  simpa only [a, dif_pos hp] using this

end Psi

end Virasoro.Sphere
