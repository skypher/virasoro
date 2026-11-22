import Virasoro.Sphere.Proofs.Sec3GaussShift

/-!
# The Fock pairing as an algebraic Gaussian expectation (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.637–650.  In the variables `u_1,…,u_n` and `ū_1,…,ū_n` (`Modes n`), over a
ring in which `z^{K+1} = 0`, the functional
`P(Φ) = ∑_β ∏_m β_m!/(2m)^{β_m} z^{|β|} [u^β ū^β] Φ` computes the Fock pairing (3.1) of
`f(z^• u)` with `g(ū)` when `Φ = f(u) g(ū)`.  It is the algebraic Gaussian expectation with
respect to `Q₀`: it satisfies the Wick rule with mean zero and covariance
`Cov(u_m, ū_m) = z^m/(2m)`.
-/

namespace Virasoro.Sphere

open Finset MvPowerSeries

/-- The index set of the variables `u_1,…,u_n` (left) and `ū_1,…,ū_n` (right); the index
`i : Fin n` stands for the mode `m = i + 1`. -/
abbrev Modes (n : ℕ) := Fin n ⊕ Fin n

/-- The oscillator level `∑_m m β_m` of an exponent. -/
def wtF {n : ℕ} (f : Fin n → ℕ) : ℕ := ∑ i : Fin n, ((i : ℕ) + 1) * f i

/-- `∏_m β_m!/(2m)^{β_m}`. -/
def nrmF {n : ℕ} (f : Fin n → ℕ) : ℚ :=
  ∏ i : Fin n, ((f i).factorial : ℚ) / (2 * (((i : ℕ) + 1 : ℕ) : ℚ)) ^ f i

theorem wtF_update {n : ℕ} (f : Fin n → ℕ) (m : Fin n) :
    wtF (Function.update f m (f m + 1)) = wtF f + ((m : ℕ) + 1) := by
  have h1 : (fun i : Fin n => ((i : ℕ) + 1) * Function.update f m (f m + 1) i) =
      Function.update (fun i : Fin n => ((i : ℕ) + 1) * f i) m (((m : ℕ) + 1) * (f m + 1)) := by
    funext i
    by_cases hi : i = m
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [wtF, h1, Finset.sum_update_of_mem (Finset.mem_univ m), wtF,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ m), Finset.sdiff_singleton_eq_erase]
  ring

theorem nrmF_update {n : ℕ} (f : Fin n → ℕ) (m : Fin n) :
    nrmF (Function.update f m (f m + 1)) =
      nrmF f * ((f m + 1 : ℕ) : ℚ) / (2 * (((m : ℕ) + 1 : ℕ) : ℚ)) := by
  have h1 : (fun i : Fin n => ((Function.update f m (f m + 1) i).factorial : ℚ) /
        (2 * (((i : ℕ) + 1 : ℕ) : ℚ)) ^ Function.update f m (f m + 1) i) =
      Function.update
        (fun i : Fin n => ((f i).factorial : ℚ) / (2 * (((i : ℕ) + 1 : ℕ) : ℚ)) ^ f i) m
        (((f m + 1).factorial : ℚ) / (2 * (((m : ℕ) + 1 : ℕ) : ℚ)) ^ (f m + 1)) := by
    funext i
    by_cases hi : i = m
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  rw [nrmF, h1, Finset.prod_update_of_mem (Finset.mem_univ m), nrmF,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Finset.sdiff_singleton_eq_erase,
    Nat.factorial_succ]
  have h2 : (2 * (((m : ℕ) + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

section Fock

variable (n K : ℕ) {R : Type*} [CommRing R] [Algebra ℚ R] (z : R)

/-- The moment `P(u^f ū^g)`: `∏_m f_m!/(2m)^{f_m} z^{|f|}` for `f = g`, zero otherwise. -/
noncomputable def momF (f g : Fin n → ℕ) : R :=
  if f = g then algebraMap ℚ R (nrmF f) * z ^ wtF f else 0

theorem momF_step (f g : Fin n → ℕ) (m : Fin n) :
    momF n z (Function.update f m (f m + 1)) g =
      algebraMap ℚ R (1 / (2 * (((m : ℕ) + 1 : ℕ) : ℚ))) * z ^ ((m : ℕ) + 1) *
        ((g m : R) * momF n z f (Function.update g m (g m - 1))) := by
  by_cases hg : g m = 0
  · have h1 : Function.update f m (f m + 1) ≠ g := by
      intro h
      have := congrFun h m
      simp at this
      omega
    rw [momF, if_neg h1, hg, Nat.cast_zero, zero_mul, mul_zero]
  · by_cases h : Function.update f m (f m + 1) = g
    · have h2 : f = Function.update g m (g m - 1) := by
        rw [← h]
        simp
      have h3 : g m = f m + 1 := by rw [← h]; simp
      rw [momF, if_pos h, momF, if_pos h2, nrmF_update, wtF_update, pow_add, h3]
      rw [show ((f m + 1 : ℕ) : R) = algebraMap ℚ R ((f m + 1 : ℕ) : ℚ) from
        (map_natCast (algebraMap ℚ R) _).symm]
      have h4 : algebraMap ℚ R (nrmF f * ((f m + 1 : ℕ) : ℚ) / (2 * (((m : ℕ) + 1 : ℕ) : ℚ))) =
          algebraMap ℚ R (1 / (2 * (((m : ℕ) + 1 : ℕ) : ℚ))) *
            (algebraMap ℚ R ((f m + 1 : ℕ) : ℚ) * algebraMap ℚ R (nrmF f)) := by
        rw [← map_mul, ← map_mul]
        congr 1
        ring
      rw [h4]
      ring
    · have h2 : f ≠ Function.update g m (g m - 1) := by
        intro h2
        apply h
        rw [h2]
        simp only [Function.update_self, Function.update_idem]
        rw [show g m - 1 + 1 = g m by omega, Function.update_eq_self]
      rw [momF, if_neg h, momF, if_neg h2, mul_zero, mul_zero]

theorem momF_symm (f g : Fin n → ℕ) : momF n z f g = momF n z g f := by
  unfold momF
  by_cases h : f = g
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem momF_eq_zero (hz : z ^ (K + 1) = 0) (f g : Fin n → ℕ) (m : Fin n) (hm : K < f m) :
    momF n z f g = 0 := by
  unfold momF
  split_ifs with h
  · have h1 : K + 1 ≤ wtF f := by
      have h2 : ((m : ℕ) + 1) * f m ≤ wtF f :=
        Finset.single_le_sum (f := fun i : Fin n => ((i : ℕ) + 1) * f i) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ m)
      nlinarith
    rw [pow_eq_zero_of_le h1 hz, mul_zero]
  · rfl

/-- The moments of the Fock pairing. -/
noncomputable def fockMom (γ : Modes n →₀ ℕ) : R :=
  momF n z (fun i => γ (Sum.inl i)) (fun i => γ (Sum.inr i))

/-- The Fock pairing `P` (sphere/paper.tex (3.1), l.637–640) on series in `u, ū`. -/
noncomputable def fockP : MvPowerSeries (Modes n) R →ₗ[R] R :=
  ∑ γ ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Modes n => K),
    fockMom n z γ • MvPowerSeries.coeff (R := R) γ

variable {n K z}

theorem fockP_monomial (hz : z ^ (K + 1) = 0) (γ : Modes n →₀ ℕ) :
    fockP n K z (monomial γ 1) = fockMom n z γ := by
  classical
  rw [fockP, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, coeff_monomial, smul_eq_mul]
  by_cases hγ : γ ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Modes n => K)
  · rw [Finset.sum_eq_single γ]
    · rw [if_pos rfl, mul_one]
    · intro γ' _ hne
      rw [if_neg hne, mul_zero]
    · intro h
      exact absurd hγ h
  · rw [Finset.sum_eq_zero]
    · rw [Finset.mem_Iic] at hγ
      obtain ⟨j, hj⟩ : ∃ j, K < γ j := by
        by_contra hcon
        push_neg at hcon
        exact hγ fun j => by simpa using hcon j
      rcases j with i | i
      · exact (momF_eq_zero n K z hz _ _ i hj).symm
      · rw [fockMom, momF_symm]
        exact (momF_eq_zero n K z hz _ _ i hj).symm
    · intro γ' hγ'
      have hne : γ' ≠ γ := fun h => hγ (h ▸ hγ')
      rw [if_neg hne, mul_zero]

theorem fockP_local : IsLocal (Fintype.card (Modes n) * K) (fockP n K z) := by
  intro Φ hΦ
  rw [fockP, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun γ hγ => ?_
  rw [Finset.mem_Iic] at hγ
  have h1 : γ.degree ≤ Fintype.card (Modes n) * K := by
    rw [Finsupp.degree_eq_sum]
    calc ∑ i, γ i ≤ ∑ _i : Modes n, K := Finset.sum_le_sum fun i _ => by simpa using hγ i
      _ = Fintype.card (Modes n) * K := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [LinearMap.smul_apply, hΦ γ h1, smul_zero]

variable (n z) in
/-- The covariance of `Q₀`: `Cov(u_m, ū_m) = z^m/(2m)`. -/
noncomputable def cov0 : Modes n → Modes n → R
  | Sum.inl i, Sum.inr j =>
    if i = j then algebraMap ℚ R (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) * z ^ ((i : ℕ) + 1) else 0
  | Sum.inr i, Sum.inl j =>
    if i = j then algebraMap ℚ R (1 / (2 * (((i : ℕ) + 1 : ℕ) : ℚ))) * z ^ ((i : ℕ) + 1) else 0
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

theorem fockMom_inl (α : Modes n →₀ ℕ) (m : Fin n) :
    fockMom n z (Finsupp.single (Sum.inl m) 1 + α) =
      algebraMap ℚ R (1 / (2 * (((m : ℕ) + 1 : ℕ) : ℚ))) * z ^ ((m : ℕ) + 1) *
        ((α (Sum.inr m) : R) * fockMom n z (α - Finsupp.single (Sum.inr m) 1)) := by
  have h1 : (fun i => (Finsupp.single (Sum.inl m) 1 + α : Modes n →₀ ℕ) (Sum.inl i)) =
      Function.update (fun i => α (Sum.inl i)) m (α (Sum.inl m) + 1) := by
    funext i
    by_cases hi : i = m
    · subst hi; simp [add_comm]
    · simp [Function.update_of_ne hi, Finsupp.single_eq_of_ne (Sum.inl_injective.ne hi)]
  have h2 : (fun i => (Finsupp.single (Sum.inl m) 1 + α : Modes n →₀ ℕ) (Sum.inr i)) =
      fun i => α (Sum.inr i) := by
    funext i
    simp
  have h3 : (fun i => (α - Finsupp.single (Sum.inr m) 1 : Modes n →₀ ℕ) (Sum.inr i)) =
      Function.update (fun i => α (Sum.inr i)) m (α (Sum.inr m) - 1) := by
    funext i
    by_cases hi : i = m
    · subst hi; simp
    · simp [Function.update_of_ne hi, Finsupp.single_eq_of_ne (Sum.inr_injective.ne hi)]
  have h4 : (fun i => (α - Finsupp.single (Sum.inr m) 1 : Modes n →₀ ℕ) (Sum.inl i)) =
      fun i => α (Sum.inl i) := by
    funext i
    simp
  rw [fockMom, fockMom, h1, h2, h3, h4]
  exact momF_step n z _ _ m

theorem fockMom_inr (α : Modes n →₀ ℕ) (m : Fin n) :
    fockMom n z (Finsupp.single (Sum.inr m) 1 + α) =
      algebraMap ℚ R (1 / (2 * (((m : ℕ) + 1 : ℕ) : ℚ))) * z ^ ((m : ℕ) + 1) *
        ((α (Sum.inl m) : R) * fockMom n z (α - Finsupp.single (Sum.inl m) 1)) := by
  have h1 : (fun i => (Finsupp.single (Sum.inr m) 1 + α : Modes n →₀ ℕ) (Sum.inr i)) =
      Function.update (fun i => α (Sum.inr i)) m (α (Sum.inr m) + 1) := by
    funext i
    by_cases hi : i = m
    · subst hi; simp [add_comm]
    · simp [Function.update_of_ne hi, Finsupp.single_eq_of_ne (Sum.inr_injective.ne hi)]
  have h2 : (fun i => (Finsupp.single (Sum.inr m) 1 + α : Modes n →₀ ℕ) (Sum.inl i)) =
      fun i => α (Sum.inl i) := by
    funext i
    simp
  have h3 : (fun i => (α - Finsupp.single (Sum.inl m) 1 : Modes n →₀ ℕ) (Sum.inl i)) =
      Function.update (fun i => α (Sum.inl i)) m (α (Sum.inl m) - 1) := by
    funext i
    by_cases hi : i = m
    · subst hi; simp
    · simp [Function.update_of_ne hi, Finsupp.single_eq_of_ne (Sum.inl_injective.ne hi)]
  have h4 : (fun i => (α - Finsupp.single (Sum.inl m) 1 : Modes n →₀ ℕ) (Sum.inr i)) =
      fun i => α (Sum.inr i) := by
    funext i
    simp
  rw [fockMom, fockMom, h1, h2, h3, h4, momF_symm,
    momF_symm n z (Function.update (fun i => α (Sum.inl i)) m (α (Sum.inl m) - 1))]
  exact momF_step n z _ _ m

/-- The Fock pairing satisfies the Wick rule of `Q₀` (sphere/paper.tex l.637–640). -/
theorem fockP_ibp (hz : z ^ (K + 1) = 0) : IBP (fockP n K z) 0 (cov0 n z) := by
  refine ibp_of_monomials fockP_local fun i α => ?_
  rw [Pi.zero_apply, zero_mul, zero_add, X_def, monomial_mul_monomial, one_mul,
    fockP_monomial hz, Fintype.sum_sum_type]
  rcases i with m | m
  · rw [fockMom_inl]
    simp only [cov0, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl, pderiv_monomial_one, apply_monomial, fockP_monomial hz]
    · intro j _ hj
      rw [if_neg (Ne.symm hj), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ m) h
  · rw [fockMom_inr]
    simp only [cov0, zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single m]
    · rw [if_pos rfl, pderiv_monomial_one, apply_monomial, fockP_monomial hz]
    · intro j _ hj
      rw [if_neg (Ne.symm hj), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ m) h

end Fock

end Virasoro.Sphere
