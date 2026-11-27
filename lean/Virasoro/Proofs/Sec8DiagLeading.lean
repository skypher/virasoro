import Virasoro.Proofs.Sec8DiagLeadSums
import Virasoro.Proofs.Sec7FixedCharge

/-!
# Lemma 8.5 (`lem:node-leading`)

Part (ii): `FS(a → μ)` has `D` elements, the slopes `h_{aθ}` are distinct, and the sums
`F(θ) = ∑_{x₁ = θ} w_γ` solve the Vandermonde system given by part (i) with `(k, j) = (m+1, 0)`,
by Lagrange interpolation.
-/

namespace Virasoro

open scoped LaurentSeries

/-- Lagrange interpolation: if `∑_{i ∈ S} F_i x_i^m = 0` for `m < |S| - 1` and `= T` for
`m = |S| - 1`, with the `x_i` distinct, then `F_θ = T / ∏_{θ' ≠ θ} (x_θ - x_θ')`. -/
theorem moment_lagrange {ι K : Type*} [DecidableEq ι] [Field K] (S : Finset ι) (x F : ι → K)
    (T : K) (hinj : Set.InjOn x S)
    (hmom : ∀ m < S.card, ∑ i ∈ S, F i * x i ^ m = if m = S.card - 1 then T else 0) :
    ∀ θ ∈ S, F θ = T / ∏ θ' ∈ S.erase θ, (x θ - x θ') := by
  intro θ hθ
  obtain ⟨P, hP⟩ : ∃ P : Polynomial K,
      P = ∏ θ' ∈ S.erase θ, (Polynomial.X - Polynomial.C (x θ')) := ⟨_, rfl⟩
  have hmon : P.Monic := by
    rw [hP]; exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (x i)
  have hdeg : P.natDegree = S.card - 1 := by
    rw [hP, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (x i)]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem hθ]
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨θ, hθ⟩
  have heval : ∀ y, P.eval y = ∑ m ∈ Finset.range S.card, P.coeff m * y ^ m := fun y =>
    Polynomial.eval_eq_sum_range' (by omega) y
  have hsum : ∑ i ∈ S, F i * P.eval (x i) = T := by
    simp_rw [heval, Finset.mul_sum]
    rw [Finset.sum_comm]
    have h1 : ∀ m ∈ Finset.range S.card, ∑ i ∈ S, F i * (P.coeff m * x i ^ m) =
        P.coeff m * (if m = S.card - 1 then T else 0) := by
      intro m hm
      rw [← hmom m (Finset.mem_range.1 hm), Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_congr rfl h1]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' (Finset.range S.card) (S.card - 1),
      if_pos (Finset.mem_range.2 (by omega)), ← hdeg, hmon.coeff_natDegree, one_mul]
  have hzero : ∀ i ∈ S, i ≠ θ → P.eval (x i) = 0 := by
    intro i hi hne
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hne, hi⟩) (by simp)
  have hsum2 : ∑ i ∈ S, F i * P.eval (x i) = F θ * P.eval (x θ) :=
    Finset.sum_eq_single θ (fun i hi hne => by rw [hzero i hi hne, mul_zero])
      (fun h => absurd hθ h)
  have hev : P.eval (x θ) = ∏ θ' ∈ S.erase θ, (x θ - x θ') := by
    rw [hP, Polynomial.eval_prod]; simp
  have hne : ∏ θ' ∈ S.erase θ, (x θ - x θ') ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi e
    have hi' := Finset.mem_erase.1 hi
    exact hi'.1 (hinj hi'.2 hθ (sub_eq_zero.1 e).symm)
  rw [eq_div_iff hne, ← hev, ← hsum2, hsum]

variable {p p' r s : ℕ} {b : ℂ}

/-- `FS(a → μ)` has `D = L_μ - L_a` elements. -/
theorem firstSteps_card {a μ : Node} (h : a.2 < μ.2) : (firstSteps a μ).card = μ.2 - a.2 := by
  unfold firstSteps
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
    have hT : ((Finset.Ioo a.2 μ.2).filter fun k => (k - a.2) % 2 = 1) =
        (Finset.range ((μ.2 - a.2) / 2)).image (fun i => a.2 + 2 * i + 1) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨(k - a.2 - 1) / 2, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega
    rw [hT, Finset.card_image_of_injective _ (fun i i' (e : a.2 + 2 * i + 1 = a.2 + 2 * i' + 1) =>
      by omega), Finset.card_range]
    split_ifs with ho
    · rw [Finset.card_singleton]; omega
    · rw [Finset.card_empty]; omega
  · rw [Finset.disjoint_left]
    intro y hy hy2
    split_ifs at hy2 with ho
    · rw [Finset.mem_singleton.1 hy2] at hy
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter,
        Finset.mem_Ioo] at hy
      omega
    · simp at hy2

/-- The first node of a chain after `a` is a first step. -/
theorem chain_first {a μ : Node} {γ : List Node} (hγ : γ ∈ nodeChains a μ) :
    ∃ x l, γ = a :: x :: l ∧ x ∈ firstSteps a μ := by
  obtain ⟨x, l, rfl, hlt, hodd, hok⟩ := stepsOK_of_mem hγ
  refine ⟨x, l, rfl, ?_⟩
  rw [mem_firstSteps]
  rcases l with _ | ⟨y, l⟩
  · simp only [StepsOK] at hok
    subst hok
    exact Or.inr ⟨hodd, rfl⟩
  · obtain ⟨h1, -, h3⟩ := hok
    have := stepsOK_last h3
    exact Or.inl ⟨hlt, by omega, hodd⟩

section Slopes

variable (hset : MinimalSetting p p' r s b)
include hset

theorem nodeS_ne_zero (ν : Node) : nodeS p p' r s ν ≠ 0 := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hint, -⟩ := id hset
  have hcop' : IsCoprime (p : ℤ) p' := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop
  have h0 := nodeS_abs_ge hset ν
  have hn0 : (p' : ℤ) * r - p * s ≠ 0 := by
    intro h
    have hd : (p : ℤ) ∣ p' * r := ⟨s, by linarith⟩
    have := Int.le_of_dvd (by exact_mod_cast hr0) (hcop'.dvd_of_dvd_mul_left hd)
    have : (r : ℤ) < p := by exact_mod_cast hr
    omega
  have : 0 < |nodeS p p' r s (true, 0)| := by simpa [nodeS, nOrb] using hn0
  intro h
  rw [h, abs_zero] at h0
  linarith

/-- The slopes `h_{aθ}`, `θ ∈ FS(a → μ)`, are distinct. -/
theorem nodeH_injOn {a μ : Node} (haμ : a.2 < μ.2) :
    Set.InjOn (fun θ => nodeH p p' r s b a θ) (firstSteps a μ) := by
  intro θ hθ θ' hθ' h
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb0 := b_ne_zero_of hset
  have hv : varsig p' b ≠ 0 := by
    unfold varsig
    exact div_ne_zero hb0 (mul_ne_zero two_ne_zero (pow_ne_zero 2 (by exact_mod_cast hp'.ne')))
  simp only [nodeH] at h
  have h1 := RatFunc.C_injective h
  have h2 := mul_left_cancel₀ hv h1
  have h3 : (nodeS p p' r s a : ℂ) * (nodeS p p' r s θ : ℂ) =
      (nodeS p p' r s a : ℂ) * (nodeS p p' r s θ' : ℂ) := by linear_combination -h2
  have h4 := mul_left_cancel₀ (by exact_mod_cast nodeS_ne_zero hset a) h3
  have hS : nodeS p p' r s θ = nodeS p p' r s θ' := by exact_mod_cast h4
  have hL : nodeLabel p p' r s a θ = nodeLabel p p' r s a θ' := by
    simp only [nodeLabel, hS]
  exact nodeLabel_injOn hset (nodeLev_lt_of_lt hset haμ) hθ hθ' hL

end Slopes

/-- The moments `∑_θ F(θ) h_{aθ}^m` (`m < D`): `0` for `m ≤ D - 2`, `Top(a → μ)` for `m = D - 1`. -/
theorem first_moments (hreg : Stmt_lem_chain_regular) (hset : MinimalSetting p p' r s b)
    {a μ : Node} (haμ : a.2 < μ.2) (m : ℕ) (hm : m < μ.2 - a.2) :
    ∑ θ ∈ firstSteps a μ,
        (∑ γ ∈ (nodeChains a μ).filter (fun γ => γ.tail.head? = some θ), chainW p p' r s b γ) *
          nodeH p p' r s b a θ ^ m =
      if m = μ.2 - a.2 - 1 then nodeTop p p' r s b a μ else 0 := by
  have hmaps : ∀ γ ∈ nodeChains a μ, (fun γ : List Node => γ.tail.headD a) γ ∈ firstSteps a μ := by
    intro γ hγ
    obtain ⟨x, l, rfl, hx⟩ := chain_first hγ
    simpa using hx
  have hgroup : ∑ γ ∈ nodeChains a μ, chainW p p' r s b γ * chainH0 p p' r s b γ ^ m =
      ∑ θ ∈ firstSteps a μ,
        (∑ γ ∈ (nodeChains a μ).filter (fun γ => γ.tail.head? = some θ), chainW p p' r s b γ) *
          nodeH p p' r s b a θ ^ m := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [Finset.sum_mul]
    have hf : (nodeChains a μ).filter (fun γ => γ.tail.headD a = θ) =
        (nodeChains a μ).filter (fun γ => γ.tail.head? = some θ) :=
      Finset.filter_congr fun γ hγ => by
        obtain ⟨x, l, rfl, -⟩ := chain_first hγ
        simp
    rw [hf]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    obtain ⟨hγ1, hγ2⟩ := Finset.mem_filter.1 hγ
    obtain ⟨x, l, rfl, -⟩ := chain_first hγ1
    simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at hγ2
    subst hγ2
    rfl
  rw [← hgroup]
  obtain ⟨hs1, hs2⟩ := node_leading_sums hreg hset haμ
  split_ifs with hmD
  · have h2 := hs2 (m + 1) 0 (by omega) (by omega)
    simp only [Nat.add_sub_cancel, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
      div_one] at h2
    unfold nodeTop
    rw [show μ.2 - a.2 = m + 1 by omega, h2]
  · have h1 := hs1 (m + 1) 0 (by omega) (by omega)
    simpa using h1

/-- Lemma 8.5 (`lem:node-leading`), from the two cited results (through Lemma 7.13).

Paper label: lem:node-leading -/
theorem lem_node_leading_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_lem_node_leading := by
  intro p p' r s b hset a μ haμ
  have hreg := lem_chain_regular_of_cited hK hH
  obtain ⟨hs1, hs2⟩ := node_leading_sums hreg hset haμ
  have hcard := firstSteps_card haμ
  have hinj := nodeH_injOn hset haμ
  refine ⟨fun γ hγ k j hk => ?_, hs1, hs2, hcard, hinj, ?_⟩
  · have h := chainProd_lead hset hγ k j hk
    exact ⟨h.1, h.2⟩
  · refine moment_lagrange (firstSteps a μ) (fun θ => nodeH p p' r s b a θ)
      (fun θ => ∑ γ ∈ (nodeChains a μ).filter (fun γ => γ.tail.head? = some θ),
        chainW p p' r s b γ) (nodeTop p p' r s b a μ) hinj ?_
    rw [hcard]
    exact first_moments hreg hset haμ

end Virasoro
