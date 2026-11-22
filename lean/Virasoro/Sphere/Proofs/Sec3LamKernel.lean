import Virasoro.Sphere.Proofs.Sec3LamRing
import Virasoro.Sphere.Proofs.Sec3L0Unique
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Uniqueness of the Ward solution over `ℂ(λ)` (sphere paper Lemma 3.3(i))

sphere/paper.tex l.569–588: the system `P ↦ (l_1 P, …, l_m P)` on the level-`m` part is
injective over `ℂ(λ)`, because its leading part at `λ = ∞` is `P ↦ (i∂_k P)_k`.  In the
variables `u_m` the operator is `l_k = l_k|_{λ=0} + iλ ∂_{u_k}`, and `l_k|_{λ=0}` has constant
coefficients, so in a kernel element with polynomial coefficients in `λ` the coefficients of
the highest power of `λ` are annihilated by every `∂_{u_k}`.
-/

namespace Virasoro.Sphere

open MvPolynomial

section Ring

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- At `λ = 0` and constant `μ` the operator `l_k` has constant coefficients: it preserves the
polynomials whose coefficients lie in a given `ℂ`-subspace of `R`. -/
theorem ffOpR_const_mem (W : Submodule ℂ R) (μ0 : ℂ) (k : ℤ) (f : MvPolynomial ℕ+ R)
    (hf : ∀ α, coeff α f ∈ W) (γ : ℕ+ →₀ ℕ) :
    coeff γ (ffOpR (algebraMap ℂ R μ0) 0 k f) ∈ W := by
  rw [f.as_sum, map_sum, coeff_sum]
  refine Submodule.sum_mem _ fun α _ => ?_
  have h := map_ffOpMonoR (Algebra.ofId ℂ R) μ0 0 k α
  rw [map_zero] at h
  have h' : ffOpMonoR (algebraMap ℂ R μ0) 0 k α =
      map (algebraMap ℂ R) (ffOpMonoR μ0 0 k α) := h.symm
  rw [ffOpR_monomial, h', coeff_smul, coeff_map, smul_eq_mul, mul_comm, ← Algebra.smul_def]
  exact W.smul_mem _ (hf α)

/-- `l_k = l_k|_{λ=0} + iλ ∂_{u_k}` for `k ≥ 1`. -/
theorem ffOpR_pos_split (μ lam : R) (k : ℕ) (hk : 1 ≤ k) (f : MvPolynomial ℕ+ R) :
    ffOpR μ lam k f =
      ffOpR μ 0 k f + C (algebraMap ℂ R Complex.I * lam) * pderiv k.toPNat' f := by
  induction f using MvPolynomial.induction_on' with
  | monomial α r =>
    have hm : monomial α r = r • monomial α (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [ffOpR_monomial, ffOpR_monomial, hm, Derivation.map_smul, mul_smul_comm, ← smul_add]
    congr 1
    unfold ffOpMonoR
    have h0 : (k : ℤ) ≠ 0 := by omega
    have h1 : (0 : ℤ) < k := by omega
    simp only [if_neg h0, if_pos h1, Int.toNat_natCast, mul_zero, add_zero]
    rw [map_add, add_mul]
    ring
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add, mul_add]
    abel

end Ring

open Polynomial in
/-- Injectivity of `P ↦ (l_k P)_{1 ≤ k ≤ m}` on the level-`m` part, `m ≥ 1`, for coefficients
in `ℂ[λ]`. -/
theorem ward_kernel_poly (μ0 : ℂ) (m : ℕ) (P : MvPolynomial ℕ+ ℂ[X])
    (hP : IsWeightedHomogeneous fockWeight P m) (hm : 1 ≤ m)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ m →
      ffOpR (Polynomial.C μ0) (Polynomial.X : ℂ[X]) (k : ℤ) P = 0) : P = 0 := by
  by_contra hne
  have hsup : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hne
  obtain ⟨α, hα, hJ⟩ :=
    Finset.exists_mem_eq_sup P.support hsup (fun α => (MvPolynomial.coeff α P).natDegree)
  set J := P.support.sup (fun α => (MvPolynomial.coeff α P).natDegree) with hJdef
  have hpα : MvPolynomial.coeff α P ≠ 0 := MvPolynomial.mem_support_iff.mp hα
  have hw : lvl α = m := hP hpα
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp [lvl] at hw
    omega
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hα0
  have hsplit := sub_add_single hj
  have hjm : (j : ℕ) ≤ m := by
    rw [← hw, ← hsplit, lvl_add, lvl_single]
    omega
  have hk := h (j : ℕ) j.pos hjm
  rw [ffOpR_pos_split _ _ _ j.pos, PNat.coe_toPNat'] at hk
  have hc := congrArg (MvPolynomial.coeff (α - Finsupp.single j 1)) hk
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, coeff_pderiv, hsplit,
    MvPolynomial.coeff_zero] at hc
  have hW : MvPolynomial.coeff (α - Finsupp.single j 1)
      (ffOpR (Polynomial.C μ0) (0 : ℂ[X]) ((j : ℕ) : ℤ) P) ∈ Polynomial.degreeLE ℂ J := by
    refine ffOpR_const_mem (Polynomial.degreeLE ℂ J) μ0 _ P (fun β => ?_) _
    rw [Polynomial.mem_degreeLE]
    by_cases hβ : β ∈ P.support
    · exact le_trans Polynomial.degree_le_natDegree
        (by exact_mod_cast Finset.le_sup (f := fun α => (MvPolynomial.coeff α P).natDegree) hβ)
    · rw [MvPolynomial.notMem_support_iff.mp hβ]
      simp
  set n : ℕ := (α - Finsupp.single j 1 : ℕ+ →₀ ℕ) j
  have hT : algebraMap ℂ ℂ[X] Complex.I * Polynomial.X *
      (MvPolynomial.coeff α P * ((n : ℂ[X]) + 1)) =
      Polynomial.C (Complex.I * ((n : ℂ) + 1)) * (Polynomial.X * MvPolynomial.coeff α P) := by
    rw [Polynomial.algebraMap_eq, Polynomial.C_mul, Polynomial.C_add, Polynomial.C_1,
      Polynomial.C_eq_natCast]
    ring
  rw [hT] at hc
  have hcne : Complex.I * ((n : ℂ) + 1) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
  have hdeg : (Polynomial.C (Complex.I * ((n : ℂ) + 1)) *
      (Polynomial.X * MvPolynomial.coeff α P)).natDegree = J + 1 := by
    rw [Polynomial.natDegree_C_mul hcne, Polynomial.natDegree_X_mul hpα, ← hJ]
  have hle : (Polynomial.C (Complex.I * ((n : ℂ) + 1)) *
      (Polynomial.X * MvPolynomial.coeff α P)).natDegree ≤ J := by
    rw [eq_neg_of_add_eq_zero_right hc, Polynomial.natDegree_neg]
    exact Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp hW)
  omega

open Polynomial in
/-- Injectivity of `P ↦ (l_k P)_{1 ≤ k ≤ m}` on the level-`m` part over `ℂ(λ)`. -/
theorem ward_kernel_ratFunc (μ0 : ℂ) (m : ℕ) (P : MvPolynomial ℕ+ (RatFunc ℂ))
    (hP : IsWeightedHomogeneous fockWeight P m) (hm : 1 ≤ m)
    (h : ∀ k : ℕ, 1 ≤ k → k ≤ m →
      ffOp (RatFunc.C μ0) (RatFunc.X : RatFunc ℂ) (k : ℤ) P = 0) : P = 0 := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℂ[X])
    (P.support.image fun α => MvPolynomial.coeff α P)
  choose! num hnum using hb
  let P0 : MvPolynomial ℕ+ ℂ[X] :=
    ∑ α ∈ P.support, MvPolynomial.monomial α (num (MvPolynomial.coeff α P))
  have hb0 : algebraMap ℂ[X] (RatFunc ℂ) (b : ℂ[X]) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (RatFunc.algebraMap_injective ℂ)]
    exact nonZeroDivisors.ne_zero b.2
  have hmap : MvPolynomial.map (algebraMap ℂ[X] (RatFunc ℂ)) P0 =
      MvPolynomial.C (algebraMap ℂ[X] (RatFunc ℂ) (b : ℂ[X])) * P := by
    ext γ
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_sum, map_sum, MvPolynomial.coeff_C_mul]
    simp only [MvPolynomial.coeff_monomial, apply_ite (algebraMap ℂ[X] (RatFunc ℂ)), map_zero,
      Finset.sum_ite_eq']
    split_ifs with hγ
    · rw [hnum _ (Finset.mem_image_of_mem _ hγ), Algebra.smul_def]
    · rw [MvPolynomial.notMem_support_iff.mp hγ, mul_zero]
  have hP0 : IsWeightedHomogeneous fockWeight P0 m :=
    IsWeightedHomogeneous.sum _ _ _ fun α hα =>
      isWeightedHomogeneous_monomial _ _ _ (hP (MvPolynomial.mem_support_iff.mp hα))
  have hz : P0 = 0 := by
    refine ward_kernel_poly μ0 m P0 hP0 hm fun k hk hkm => ?_
    apply MvPolynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    have e := map_ffOpR (IsScalarTower.toAlgHom ℂ ℂ[X] (RatFunc ℂ)) (Polynomial.C μ0)
      (Polynomial.X : ℂ[X]) (k : ℤ) P0
    simp only [IsScalarTower.coe_toAlgHom, IsScalarTower.coe_toAlgHom', RatFunc.algebraMap_C,
      RatFunc.algebraMap_X] at e
    rw [e, hmap, map_zero, MvPolynomial.C_mul', map_smul, ← ffOp_eq_ffOpR, h k hk hkm, smul_zero]
  rw [hz, map_zero] at hmap
  rcases mul_eq_zero.mp hmap.symm with h0 | h0
  · exact absurd (MvPolynomial.C_eq_zero.mp h0) hb0
  · exact h0

/-- Uniqueness of the solution of the Ward equations over `ℂ(λ)`. -/
theorem ward_unique_ratFunc (μ0 Δa Δb : ℂ) (F F' : ℕ → MvPolynomial ℕ+ (RatFunc ℂ))
    (h1 : IsWardSeries (RatFunc.C μ0) (RatFunc.X : RatFunc ℂ) (RatFunc.C Δa) (RatFunc.C Δb) F)
    (h2 : IsWardSeries (RatFunc.C μ0) (RatFunc.X : RatFunc ℂ) (RatFunc.C Δa) (RatFunc.C Δb) F') :
    ∀ m, F m = F' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m.eq_zero_or_pos with rfl | hm
    · rw [h1.1, h2.1]
    rw [← sub_eq_zero]
    refine ward_kernel_ratFunc μ0 m _ ((h1.2.1 m).sub (h2.2.1 m)) hm fun k hk hkm => ?_
    have e1 := h1.2.2 k hk (m - k)
    have e2 := h2.2.2 k hk (m - k)
    rw [Nat.sub_add_cancel hkm] at e1 e2
    rw [map_sub, e1, e2, ih (m - k) (by omega), sub_self]

end Virasoro.Sphere
