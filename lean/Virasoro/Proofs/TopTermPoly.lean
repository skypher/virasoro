import Virasoro.Proofs.TopLayerTrace
import Virasoro.Proofs.TorusAtZero
import Virasoro.Proofs.Sec6DDeriv
import Virasoro.Proofs.Sec4Thm

/-!
# The summands of equation (5.1) as polynomials in `d`

The summand `τ(d)/γ · H_{N-ℓ}(c, λ+ℓ, d)` of (5.1) is the image in `ℂ(d)` of a polynomial, and for
`N > ℓ` the factor `H_{N-ℓ}` vanishes at `d = 0` (paper Lemma 6.5 at the point `(c, λ+ℓ)`).  These
are the forms in which the proofs of Proposition 6.7 (paper.tex l.1146–1148) and Corollary 5.10
(l.910–913) use Theorem 5.9.
-/

namespace Virasoro

open Polynomial

/-- `H_M(c,μ,d)` over `ℂ(d)` at a complex point `μ` is the image of the polynomial `HpolyD`. -/
theorem Hval_Kd (c μ : ℂ) (M : ℕ) :
    Hval (RatFunc.C c : Kd) dvar (pt μ) M = algebraMap ℂ[X] Kd (HpolyD c μ M) := by
  unfold Hval HpolyD
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fval_Kd, map_mul, map_intCast]

/-- `H_M(c,μ,0) = 0` for `M ≥ 1` where the Shapovalov determinants do not vanish. -/
theorem HpolyD_coeff_zero_at {c μ : ℂ} {M : ℕ} (hM : 1 ≤ M)
    (h : ∀ M' ≤ M, (gram c μ M').det ≠ 0) : (HpolyD c μ M).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eval_HpolyD]
  exact Hval_zero_d hM h

/-- The summand of (5.1) for `ℓ ≤ N` as a polynomial in `d`. -/
theorem topTerm_eq_poly (c lam : ℂ) {N ℓ : ℕ} (k : ℕ) (x : Nat.Partition ℓ → ℂ) (hle : ℓ ≤ N)
    (hdet : ∀ M : ℕ, M ≤ N - ℓ → (gram c (lam + (ℓ : ℂ)) M).det ≠ 0) :
    topTerm c lam N ℓ k x = algebraMap ℂ[X] Kd
      (torusPolyForm c lam x * C (jform c lam ℓ k x x)⁻¹ * HpolyD c (lam + (ℓ : ℂ)) (N - ℓ)) := by
  classical
  unfold topTerm
  rw [if_pos hle]
  have hdetK : ∀ M ≤ N - ℓ, (gram (RatFunc.C c : Kd) (pt (lam + (ℓ : ℂ))) M).det ≠ 0 := by
    intro M hM
    have hg : gram (RatFunc.C c : Kd) (pt (lam + (ℓ : ℂ))) M =
        (gram c (lam + (ℓ : ℂ)) M).map (RatFunc.C : ℂ →+* Kd) :=
      gram_map (RatFunc.C : ℂ →+* Kd) c (lam + (ℓ : ℂ)) M
    have hd : ((gram c (lam + (ℓ : ℂ)) M).map (RatFunc.C : ℂ →+* Kd)).det =
        (RatFunc.C : ℂ →+* Kd) (gram c (lam + (ℓ : ℂ)) M).det :=
      (RingHom.map_det (RatFunc.C : ℂ →+* Kd) (gram c (lam + (ℓ : ℂ)) M)).symm
    rw [hg, hd]
    exact (map_ne_zero (RatFunc.C : ℂ →+* Kd)).2 (hdet M hM)
  have hev : RatFunc.eval (RingHom.id Kd) (pt (lam + (ℓ : ℂ))) (HN c (N - ℓ)) =
      Hval (RatFunc.C c : Kd) dvar (pt (lam + (ℓ : ℂ))) (N - ℓ) :=
    evalAt_Hrat hdetK
  rw [hev, Hval_Kd, map_mul, map_mul, RatFunc.algebraMap_C]

/-- The summand of (5.1) at `N = ℓ`, where `H_0 = 1`. -/
theorem topTerm_self (c lam : ℂ) {ℓ : ℕ} (k : ℕ) (x : Nat.Partition ℓ → ℂ) :
    topTerm c lam ℓ ℓ k x =
      algebraMap ℂ[X] Kd (torusPolyForm c lam x * C (jform c lam ℓ k x x)⁻¹) := by
  unfold topTerm
  rw [if_pos le_rfl, Nat.sub_self, HN_zero, map_mul, RatFunc.algebraMap_C]
  simp [RatFunc.eval]

theorem coeff_mul_low {P Q : ℂ[X]} {k : ℕ} (hP : ∀ n < k, P.coeff n = 0) (hQ : Q.coeff 0 = 0) :
    ∀ n ≤ k, (P * Q).coeff n = 0 := by
  obtain ⟨P', rfl⟩ := X_pow_dvd_iff.2 hP
  obtain ⟨Q', rfl⟩ := X_dvd_iff.2 hQ
  intro n hn
  rw [show X ^ k * P' * (X * Q') = X ^ (k + 1) * (P' * Q') by ring, coeff_X_pow_mul',
    if_neg (by omega)]

/-- From the coefficient of `(Δ-λ)^{-k}` of `H_{ℓ₁}` to the coefficients of `τ₁`: if the right side
of (5.1) at `N = ℓ₁` is a polynomial `A` with `[d^n]A = 0` for `n < k`, and the other summand
(present only when `ℓ₂ < ℓ₁`) has `τ₂ = O(d^k)`, then `[d^n]τ₁ = 0` for `n < k` and
`[d^k]τ₁ = γ₁ [d^k]A`. -/
theorem tau_coeffs_of_pp (c lam : ℂ) (k : ℕ) {ℓ₁ ℓ₂ : ℕ} (hne : ℓ₁ ≠ ℓ₂)
    (x₁ : Nat.Partition ℓ₁ → ℂ) (x₂ : Nat.Partition ℓ₂ → ℂ)
    (hγ : jform c lam ℓ₁ k x₁ x₁ ≠ 0)
    (hdet : ℓ₂ ≤ ℓ₁ → ∀ M : ℕ, M ≤ ℓ₁ - ℓ₂ → (gram c (lam + (ℓ₂ : ℂ)) M).det ≠ 0)
    (hτ₂ : ℓ₂ < ℓ₁ → ∀ n < k, (torusPolyForm c lam x₂).coeff n = 0)
    (A : ℂ[X])
    (hA : algebraMap ℂ[X] Kd A = topTerm c lam ℓ₁ ℓ₁ k x₁ + topTerm c lam ℓ₁ ℓ₂ k x₂)
    (hlow : ∀ n < k, A.coeff n = 0) :
    (∀ n < k, (torusPolyForm c lam x₁).coeff n = 0) ∧
      (torusPolyForm c lam x₁).coeff k = jform c lam ℓ₁ k x₁ x₁ * A.coeff k := by
  obtain ⟨B, hB, hB0⟩ : ∃ B : ℂ[X], topTerm c lam ℓ₁ ℓ₂ k x₂ = algebraMap ℂ[X] Kd B ∧
      ∀ n ≤ k, B.coeff n = 0 := by
    by_cases hle : ℓ₂ ≤ ℓ₁
    · have hlt : ℓ₂ < ℓ₁ := lt_of_le_of_ne hle (Ne.symm hne)
      refine ⟨_, topTerm_eq_poly c lam k x₂ hle (hdet hle), ?_⟩
      refine coeff_mul_low (fun n hn => ?_)
        (HpolyD_coeff_zero_at (by omega) (hdet hle))
      rw [Polynomial.coeff_mul_C, hτ₂ hlt n hn, zero_mul]
    · refine ⟨0, ?_, fun n _ => coeff_zero n⟩
      unfold topTerm
      rw [if_neg hle, map_zero]
  rw [topTerm_self, hB, ← map_add] at hA
  have hA' : A = torusPolyForm c lam x₁ * C (jform c lam ℓ₁ k x₁ x₁)⁻¹ + B :=
    IsFractionRing.injective ℂ[X] Kd hA
  have hc : ∀ n ≤ k, (torusPolyForm c lam x₁).coeff n = jform c lam ℓ₁ k x₁ x₁ * A.coeff n := by
    intro n hn
    rw [hA', coeff_add, Polynomial.coeff_mul_C, hB0 n hn, add_zero, mul_comm, mul_assoc,
      inv_mul_cancel₀ hγ, mul_one]
  refine ⟨fun n hn => ?_, hc k le_rfl⟩
  rw [hc n hn.le, hlow n hn, mul_zero]

end Virasoro
