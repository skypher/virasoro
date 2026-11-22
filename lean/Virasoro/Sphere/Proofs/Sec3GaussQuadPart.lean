import Virasoro.Sphere.Proofs.Sec3GaussRestrict
import Virasoro.Sphere.Proofs.Sec3GaussCov
import Virasoro.Sphere.Proofs.Sec3SaddleI0a

/-!
# `S⁽⁰⁾` in the modes `≤ N` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.641–646.  Restricted to the modes `u_1,…,u_N` and `ū_1,…,ū_N`,
`λ² S⁽⁰⁾(u/λ) + λ² S̃⁽⁰⁾(ū/λ)` is the quadratic form `q = ∑ B_{m,n}(u_m u_n + ū_m ū_n)`, which is
absorbed into the Gaussian weight, plus the linear form `λ ∑ A_m (u_m - ū_m)`.
-/

namespace Virasoro.Sphere

open MvPowerSeries

section Low

variable {N : ℕ} {τ : Type*} {S : Type*} [CommRing S]

/-- A substitution that kills the variables `u_m`, `m > N`, sees only the monomials in
`u_1,…,u_N`. -/
theorem subst_eq_zero_of_low {b : ℕ+ → MvPowerSeries τ S} (hb : HasSubst b)
    (hbN : ∀ m : ℕ+, N < (m : ℕ) → b m = 0) (f : MvPowerSeries ℕ+ S)
    (hf : ∀ d : ℕ+ →₀ ℕ, (∀ m ∈ d.support, (m : ℕ) ≤ N) → coeff d f = 0) : subst b f = 0 := by
  ext e
  rw [coeff_subst hb, map_zero]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases h : ∀ m ∈ d.support, (m : ℕ) ≤ N
  · rw [hf d h, zero_smul]
  · push Not at h
    obtain ⟨m, hm, hN⟩ := h
    have : (d.prod fun s e => b s ^ e) = 0 :=
      Finset.prod_eq_zero hm (by
        show b m ^ d m = 0
        rw [hbN m hN, zero_pow (Finsupp.mem_support_iff.1 hm)])
    rw [this, map_zero, smul_zero]

theorem subst_congr_of_low {b : ℕ+ → MvPowerSeries τ S} (hb : HasSubst b)
    (hbN : ∀ m : ℕ+, N < (m : ℕ) → b m = 0) (f g : MvPowerSeries ℕ+ S)
    (hf : ∀ d : ℕ+ →₀ ℕ, (∀ m ∈ d.support, (m : ℕ) ≤ N) → coeff d f = coeff d g) :
    subst b f = subst b g := by
  have h := subst_eq_zero_of_low hb hbN (f - g) fun d hd => by rw [map_sub, hf d hd, sub_self]
  rwa [subst_sub hb, sub_eq_zero] at h

/-- `subst b (rescale r f) = subst (r b) f`. -/
theorem subst_rescale {b : ℕ+ → MvPowerSeries τ S} (hb : HasSubst b) (r : S)
    (f : MvPowerSeries ℕ+ S) :
    subst b (rescale (fun _ => r) f) = subst (fun m => C r * b m) f := by
  rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) hb]
  congr 1
  funext m
  show subst b (r • (X m : MvPowerSeries ℕ+ S)) = _
  rw [subst_smul hb, subst_X hb, smul_eq_C_mul]

variable (N) in
/-- The modes `1,…,N`. -/
def modeSet : Finset ℕ+ := Finset.univ.image (modeEmb N)

theorem sum_modeSet {M : Type*} [AddCommMonoid M] (g : ℕ+ → M) :
    ∑ m ∈ modeSet N, g m = ∑ i : Fin N, g (modeEmb N i) :=
  Finset.sum_image fun _ _ _ _ h => modeEmb_injective h

variable (N) in
/-- `∑_{m≤N} a_m σ_m + ∑_{m,n≤N} b_{m,n} σ_m σ_n`. -/
noncomputable def SqN (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) : MvPowerSeries ℕ+ ℂ :=
  ∑ μ ∈ modeSet N, a μ • (X μ : MvPowerSeries ℕ+ ℂ) +
    ∑ μ ∈ modeSet N, ∑ ν ∈ modeSet N, b μ ν • ((X μ : MvPowerSeries ℕ+ ℂ) * X ν)

theorem Sq_low (a : ℕ → ℂ) (b : ℕ → ℕ → ℂ) (d : ℕ+ →₀ ℕ)
    (hd : ∀ m ∈ d.support, (m : ℕ) ≤ N) : coeff d (Sq a b) = coeff d (SqN N a b) := by
  classical
  have hsupp : d.support ⊆ modeSet N := fun m hm => by
    obtain ⟨i, hi⟩ := (mem_range_modeEmb m).2 (hd m hm)
    exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩
  rw [SqN, map_add]
  simp only [map_sum, MvPowerSeries.coeff_smul, smul_eq_mul, MvPowerSeries.coeff_X,
    coeff_X_mul_X]
  rw [coeff_eq_apply, Sq]
  by_cases h1 : d.degree = 1
  · rw [if_pos h1]
    have h2 : ∀ μ ν : ℕ+, d ≠ Finsupp.single μ 1 + Finsupp.single ν 1 := by
      intro μ ν h
      rw [h, map_add, Finsupp.degree_single, Finsupp.degree_single] at h1
      omega
    simp only [if_neg (h2 _ _), mul_zero, Finset.sum_const_zero, add_zero]
    obtain ⟨s, rfl⟩ := exists_single_of_degree_one d h1
    rw [Finsupp.support_single _ one_ne_zero, Finset.sum_singleton, Finset.sum_eq_single s]
    · rw [if_pos rfl, mul_one]
    · intro μ _ hμ
      rw [if_neg (fun h => hμ (Finsupp.single_left_injective one_ne_zero h).symm), mul_zero]
    · intro h
      exact absurd (hsupp (by simp)) h
  · rw [if_neg h1]
    have h2 : ∀ μ : ℕ+, d ≠ Finsupp.single μ 1 := fun μ h =>
      h1 (by rw [h, Finsupp.degree_single])
    simp only [if_neg (h2 _), mul_zero, Finset.sum_const_zero, zero_add]
    by_cases h3 : d.degree = 2
    · rw [if_pos h3]
      have hmem : ∀ μ ν : ℕ+, d = Finsupp.single μ 1 + Finsupp.single ν 1 →
          μ ∈ d.support ∧ ν ∈ d.support := by
        intro μ ν h
        rw [h]
        simp [Finsupp.mem_support_iff]
      symm
      rw [← Finset.sum_subset hsupp (fun μ _ hμ => Finset.sum_eq_zero fun ν _ => by
        rw [if_neg (fun h => hμ (hmem μ ν h).1), mul_zero])]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [← Finset.sum_subset hsupp (fun ν _ hν => by
        rw [if_neg (fun h => hν (hmem μ ν h).2), mul_zero])]
      refine Finset.sum_congr rfl fun ν _ => ?_
      split_ifs <;> simp
    · rw [if_neg h3]
      symm
      refine Finset.sum_eq_zero fun μ _ => Finset.sum_eq_zero fun ν _ => ?_
      rw [if_neg, mul_zero]
      intro h
      apply h3
      rw [h, map_add, Finsupp.degree_single, Finsupp.degree_single]

/-- A quadratic series under a substitution that kills the modes `> N`. -/
theorem subst_map_Sq {b : ℕ+ → MvPowerSeries τ S} (hb : HasSubst b)
    (hbN : ∀ m : ℕ+, N < (m : ℕ) → b m = 0) (ψ : ℂ →+* S) (a : ℕ → ℂ) (c : ℕ → ℕ → ℂ) :
    subst b (map ψ (Sq a c)) =
      ∑ i : Fin N, ψ (a ((i : ℕ) + 1)) • b (modeEmb N i) +
        ∑ i : Fin N, ∑ j : Fin N,
          ψ (c ((i : ℕ) + 1) ((j : ℕ) + 1)) • (b (modeEmb N i) * b (modeEmb N j)) := by
  classical
  set p : MvPowerSeries ℕ+ S := ∑ μ ∈ modeSet N, ψ (a μ) • (X μ : MvPowerSeries ℕ+ S) +
    ∑ μ ∈ modeSet N, ∑ ν ∈ modeSet N, ψ (c μ ν) • ((X μ : MvPowerSeries ℕ+ S) * X ν) with hp
  have h1 : subst b (map ψ (Sq a c)) = subst b p := by
    refine subst_congr_of_low hb hbN _ _ fun d hd => ?_
    rw [coeff_map, Sq_low a c d hd, SqN, hp]
    simp only [map_add, map_sum, MvPowerSeries.coeff_smul, smul_eq_mul, map_mul,
      MvPowerSeries.coeff_X, X_def, monomial_mul_monomial, coeff_monomial, apply_ite ψ, map_one,
      map_zero, mul_one]
  rw [h1, hp, ← coe_substAlgHom hb]
  simp only [map_add, map_sum, map_smul, map_mul, substAlgHom_X, sum_modeSet]
  rfl

end Low

section Quad

variable {N : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `λ² S⁽⁰⁾(tu) + λ² S̃⁽⁰⁾(tū)` in the modes `≤ N` is `q + J·x` with
`J = λ (A_1,…,A_N,-A_1,…,-A_N)` (`λ t = 1`). -/
theorem subst_S0_eq (ψ : ℂ →+* R) (lam t : R) (hlt : lam * t = 1) :
    lam ^ 2 • subst (eS (S := R) Sum.inl) (rescale (fun _ => t) (map ψ S0)) +
      lam ^ 2 • subst (eS (S := R) Sum.inr) (rescale (fun _ => t) (map ψ (conjSeries S0))) =
    quadB N R + linForm (Sum.elim (fun i : Fin N => lam * ψ (Acoef ((i : ℕ) + 1)))
      (fun i : Fin N => -(lam * ψ (Acoef ((i : ℕ) + 1))))) := by
  have hb : ∀ s : Fin N → Modes N, HasSubst (fun m => C t * eS (S := R) s m) := fun s =>
    (hasSubst_eS s).mul_left (fun _ => C t)
  have hbN : ∀ (s : Fin N → Modes N) (m : ℕ+), N < (m : ℕ) → C t * eS (S := R) s m = 0 :=
    fun s m h => by rw [eS_of_lt s m h, mul_zero]
  have hq : ∀ q : ℚ, ψ ((q : ℂ)) = algebraMap ℚ R q := fun q =>
    RingHom.congr_fun (Subsingleton.elim (ψ.comp (algebraMap ℚ ℂ)) (algebraMap ℚ R)) q
  rw [subst_rescale (hasSubst_eS _), subst_rescale (hasSubst_eS _), conj_S0_eq_Sq, S0_eq_Sq,
    subst_map_Sq (hb _) (hbN _), subst_map_Sq (hb _) (hbN _), quadB, linForm,
    Fintype.sum_sum_type]
  simp only [eS_modeEmb, Sum.elim_inl, Sum.elim_inr, hq, smul_add, Finset.smul_sum,
    smul_eq_C_mul, map_neg, map_mul, map_pow, mul_add, Finset.sum_add_distrib]
  have e1 : (C lam : MvPowerSeries (Modes N) R) * C t = 1 := by rw [← map_mul, hlt, map_one]
  have e2 : ∀ x : MvPowerSeries (Modes N) R, C lam ^ 2 * (C t * x) = C lam * x := fun x => by
    linear_combination (C lam * x) * e1
  have e3 : ∀ x y z : MvPowerSeries (Modes N) R,
      C lam ^ 2 * (z * (C t * x * (C t * y))) = z * (x * y) := fun x y z => by
    linear_combination (z * x * y * (C lam * C t + 1)) * e1
  have e4 : ∀ x z : MvPowerSeries (Modes N) R, C lam ^ 2 * (z * (C t * x)) = C lam * z * x :=
    fun x z => by linear_combination (C lam * z * x) * e1
  simp only [e3, e4]
  ring

end Quad

end Virasoro.Sphere
