import Virasoro.Sphere.Proofs.Sec3C2Rescale

/-!
# Lemma 3.7, Step 2: the stacked system at `λ^{-2} = 0` is injective (sphere paper)

sphere/paper.tex l.1076–1084: on `(ℋ_λ)_n` the primary conditions `(D_k + l_k^{(2)})P = 0`
(`1 ≤ k ≤ n`) together with `ev_0(P) = P|_{W=0}` form an injective system: filtering a kernel
element by `W`-level, its lowest nonzero positive `W`-level lies in `⋂_k ker D_k`, hence
vanishes by the lowest-degree injectivity of the proof of Lemma 3.3(i) (l.582–590).
-/

namespace Virasoro.Sphere

open MvPolynomial Finset TensorProduct

/-- The coefficients of `D_k g`. -/
theorem coeff_Dop (k : ℕ) (g : Fock) (γ : ℕ+ →₀ ℕ) :
    coeff γ (Dop k g) = ∑ j ∈ γ.support, ((j : ℕ) : ℂ) *
        coeff (γ - Finsupp.single j 1) (pderiv ((j : ℕ) + k).toPNat' g)
      + coeff γ (pderiv k.toPNat' g) := by
  induction g using MvPolynomial.induction_on' with
  | monomial α a =>
    have hm : monomial α a = a • monomial α (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, Dop_monomial, coeff_smul, DopMono]
    simp only [coeff_add, uVar, dVar, Derivation.coeFn_coe, smul_eq_mul]
    rw [coeff_shift_monomial (R := ℂ) k α γ]
    simp only [Derivation.map_smul, coeff_smul, smul_eq_mul]
    rw [mul_add, Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq]
    simp only [map_add, coeff_add, mul_add, Finset.sum_add_distrib]
    ring

theorem coeff_Dop_of_level (k : ℕ) (hk : 1 ≤ k) {M : ℕ} {g : Fock} (hg : g ∈ levelSub M)
    (γ : ℕ+ →₀ ℕ) (h : lvl γ + k ≠ M) : coeff γ (Dop k g) = 0 := by
  have hz : ∀ δ : ℕ+ →₀ ℕ, lvl δ ≠ M → coeff δ g = 0 := coeff_eq_zero_of_level hg
  have hjk : ∀ j : ℕ, 1 ≤ j → ((j.toPNat' : ℕ+) : ℕ) = j := fun j hj => PNat.toPNat'_coe hj
  rw [coeff_Dop]
  simp only [coeff_pderiv]
  have e1 : ∀ j ∈ γ.support,
      coeff (γ - Finsupp.single j 1 + Finsupp.single ((j : ℕ) + k).toPNat' 1) g = 0 :=
    fun j hj => hz _ (by
      have e := congrArg lvl (sub_add_single hj)
      rw [lvl_add, lvl_single] at e
      rw [lvl_add, lvl_single, hjk _ (by omega)]
      omega)
  have e3 : coeff (γ + Finsupp.single k.toPNat' 1) g = 0 :=
    hz _ (by rw [lvl_add, lvl_single, hjk _ hk]; omega)
  rw [Finset.sum_eq_zero (fun j hj => by rw [e1 j hj]; ring), e3]
  ring

/-- The lowest-degree injectivity (sphere/paper.tex l.582–590): a polynomial of level `j ≥ 1`
killed by all `D_k = ∂_{W_k} + ∑_m m W_m ∂_{W_{m+k}}` vanishes; `∂_{W_k}` lowers the total
degree by `1` while `∑_m m W_m ∂_{W_{m+k}}` preserves it. -/
theorem Dop_injective_level {j : ℕ} (hj : 1 ≤ j) {a : Fock} (ha : a ∈ levelSub j)
    (hD : ∀ k : ℕ, 1 ≤ k → Dop k a = 0) : a = 0 := by
  by_contra hne
  have hsn : a.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hne (support_eq_empty.mp h)
  obtain ⟨β, hβ, hmin⟩ := Finset.exists_min_image a.support (fun β => β.degree) hsn
  have hβ0 : coeff β a ≠ 0 := mem_support_iff.mp hβ
  have hlv : lvl β = j := ha hβ0
  have hβne : β ≠ 0 := by
    rintro rfl
    simp [lvl] at hlv
    omega
  obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr hβne
  have hmpos : 1 ≤ (m : ℕ) := m.pos
  have hmm : ((m : ℕ).toPNat' : ℕ+) = m := PNat.eq (PNat.toPNat'_coe m.pos)
  have h := congrArg (coeff (β - Finsupp.single m 1)) (hD (m : ℕ) hmpos)
  rw [coeff_Dop, coeff_zero, coeff_pderiv, hmm, sub_add_single hm] at h
  have hd1 := congrArg Finsupp.degree (sub_add_single hm)
  rw [map_add, Finsupp.degree_single] at hd1
  have hsum : (Finset.sum (β - Finsupp.single m 1).support fun j' : ℕ+ => ((j' : ℕ) : ℂ) *
      coeff (β - Finsupp.single m 1 - Finsupp.single j' 1)
        (pderiv ((j' : ℕ) + (m : ℕ)).toPNat' a)) = 0 := by
    refine Finset.sum_eq_zero fun j' hj' => ?_
    rw [coeff_pderiv]
    have hz : coeff (β - Finsupp.single m 1 - Finsupp.single j' 1 +
        Finsupp.single ((j' : ℕ) + (m : ℕ)).toPNat' 1) a = 0 := by
      by_contra hc
      have h1 := hmin _ (mem_support_iff.mpr hc)
      have hd2 := congrArg Finsupp.degree (sub_add_single hj')
      rw [map_add, Finsupp.degree_single] at hd2
      simp only [map_add, Finsupp.degree_single] at h1
      omega
    rw [hz]
    ring
  rw [hsum, zero_add] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact hβ0 h1
  · exact Nat.cast_add_one_ne_zero _ h1

theorem Tk_zero_tmul (k : ℕ) (a b : Fock) :
    Tk 0 k (a ⊗ₜ[ℂ] b) = Dop k a ⊗ₜ[ℂ] b + a ⊗ₜ[ℂ] ffOp 0 0 (k : ℤ) b := by
  simp only [Tk, zero_smul, add_zero, LinearMap.add_apply, TensorProduct.map_tmul,
    LinearMap.id_apply]

theorem evAt_tmul (c : ℕ+ → ℂ) (a b : Fock) : evAt c (a ⊗ₜ[ℂ] b) = aeval c a • b := by
  simp only [evAt, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, AlgHom.toLinearMap_apply]

/-- The coefficient of `u^γ` in `P|_{W=0}` is the coefficient of `W^0 ⊗ u^γ` in `P`. -/
theorem coeff_evAt_zero (γ : ℕ+ →₀ ℕ) (y : HH) :
    coeff γ (evAt 0 y) = hhBasis.repr y (0, γ) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [map_add, coeff_add, hy, hz, map_add, Finsupp.add_apply]
  | tmul a b =>
    rw [hhBasis_repr_tmul, evAt_tmul, coeff_smul, smul_eq_mul, aeval_zero, constantCoeff_eq]
    rfl

set_option maxHeartbeats 1600000 in
/-- The stacked system at `λ^{-2} = 0` is injective (sphere/paper.tex l.1081–1084). -/
theorem stacked_injective (n : ℕ) (x : HH) (hx : x ∈ hhLevel n)
    (hT : ∀ k : ℕ, 1 ≤ k → k ≤ n → Tk 0 k x = 0) (he : evAt 0 x = 0) : x = 0 := by
  classical
  have hx' := hx
  rw [hhLevel, Module.Basis.mem_span_image] at hx'
  have hxs0 := hhBasis.linearCombination_repr x
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hxs0
  generalize hξ : hhBasis.repr x = ξ at hx' hxs0
  have hsupp : ∀ p, ξ p ≠ 0 → lvl p.1 + lvl p.2 = n := fun p hp =>
    hx' (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hp))
  have hxs : x = ∑ p ∈ ξ.support,
      ξ p • (monomial p.1 (1 : ℂ) ⊗ₜ[ℂ] monomial p.2 (1 : ℂ)) := by
    rw [← hxs0]
    exact Finset.sum_congr rfl fun p _ => by rw [hhBasis_apply]
  have key : ∀ j : ℕ, ∀ β γ : ℕ+ →₀ ℕ, lvl β = j → ξ (β, γ) = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro β γ hβ
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · have hβ0 := lvl_eq_zero hβ
        subst hβ0
        rw [← hξ, ← coeff_evAt_zero, he, coeff_zero]
      by_contra hne
      have hlev : lvl β + lvl γ = n := hsupp (β, γ) hne
      have hacoeff : ∀ β' : ℕ+ →₀ ℕ,
          coeff β' (∑ p ∈ ξ.support.filter (fun p => p.2 = γ), ξ p • monomial p.1 (1 : ℂ)) =
            ξ (β', γ) := by
        intro β'
        rw [coeff_sum]
        simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_eq_single (β', γ)]
        · rw [if_pos rfl]
        · rintro ⟨b1, b2⟩ hb hbne
          rw [Finset.mem_filter] at hb
          rw [if_neg]
          rintro rfl
          exact hbne (by rw [← hb.2])
        · intro hnot
          rw [if_pos rfl]
          by_contra h
          exact hnot (Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr h, rfl⟩)
      have halev : (∑ p ∈ ξ.support.filter (fun p => p.2 = γ), ξ p • monomial p.1 (1 : ℂ)) ∈
          levelSub j := by
        intro β' hβ'
        rw [hacoeff] at hβ'
        have h1 : lvl β' + lvl γ = n := hsupp (β', γ) hβ'
        show lvl β' = j
        omega
      have hD : ∀ k : ℕ, 1 ≤ k →
          Dop k (∑ p ∈ ξ.support.filter (fun p => p.2 = γ), ξ p • monomial p.1 (1 : ℂ)) = 0 := by
        intro k hk
        ext δ
        rw [coeff_zero]
        by_cases hδ : lvl δ + k = j
        · have hkn : k ≤ n := by omega
          have h1 := congrArg (fun y => hhBasis.repr y (δ, γ)) (hT k hk hkn)
          simp only [map_zero, Finsupp.zero_apply] at h1
          rw [hxs] at h1
          simp only [map_sum, map_smul, Tk_zero_tmul, map_add, Finsupp.coe_finsetSum,
            Finsupp.coe_smul, Finsupp.coe_add, Finset.sum_apply, Pi.smul_apply, Pi.add_apply,
            hhBasis_repr_tmul, smul_eq_mul, mul_add, Finset.sum_add_distrib] at h1
          have h2 : ∑ p ∈ ξ.support, ξ p * (coeff δ (monomial p.1 (1 : ℂ)) *
              coeff γ (ffOp 0 0 (k : ℤ) (monomial p.2 (1 : ℂ)))) = 0 :=
            Finset.sum_eq_zero fun p _ => by
              rw [coeff_monomial]
              split_ifs with h
              · have h0 : ξ p = 0 := by
                  obtain ⟨p1, p2⟩ := p
                  simp only at h
                  subst h
                  exact ih (lvl p1) (by omega) p1 p2 rfl
                rw [h0]
                ring
              · ring
          have h3 : coeff δ (Dop k (∑ p ∈ ξ.support.filter (fun p => p.2 = γ),
                ξ p • monomial p.1 (1 : ℂ))) =
              ∑ p ∈ ξ.support, ξ p * (coeff δ (Dop k (monomial p.1 (1 : ℂ))) *
                coeff γ (monomial p.2 (1 : ℂ))) := by
            rw [map_sum, coeff_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [coeff_monomial]
            split_ifs with h
            · rw [map_smul, coeff_smul, smul_eq_mul, mul_one]
            · ring
          rw [h3]
          linear_combination h1 - h2
        · exact coeff_Dop_of_level k hk halev δ hδ
      have ha0 := Dop_injective_level hj halev hD
      exact hne (by rw [← hacoeff, ha0, coeff_zero])
  have hξ0 : ξ = 0 := Finsupp.ext fun p => key (lvl p.1) p.1 p.2 rfl
  rw [← hξ] at hξ0
  exact hhBasis.repr.map_eq_zero_iff.mp hξ0

end Virasoro.Sphere
