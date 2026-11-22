import Virasoro.Statements.Sec9b
import Virasoro.Proofs.P2Sec10Ward
import Virasoro.Proofs.TorusAtZero
import Virasoro.Proofs.Specialize
import Virasoro.Proofs.PBWBasis
import Virasoro.Proofs.GramDet
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Theorem 9.2: the two-variable polynomial `f_d(x₁,x₂)` (paper.tex l.2630–2644, 2676–2681)

The two-weight form `ρ_{Δ₁,Δ₂;d}(𝒪 v_{Δ₁}, 𝒪 v_{Δ₂})` of a constant-coefficient PBW operator `𝒪`
is a polynomial in `(Δ₁,Δ₂)`; its restriction to the diagonal is the torus form, and the
derivative along the diagonal is the sum of the two partial derivatives (the product rule used
for (12.1)).
-/

namespace Virasoro.P2

open Virasoro Polynomial

section Ring

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem phi2_diag (h d : R) (w : List ℕ) : phi2 h h d w = phi d w := by
  induction w with
  | nil => rfl
  | cons m w ih => simp only [phi2, phi, ih, sub_self, zero_add]

/-- `ρ_{Δ,Δ;d}` has the matrix elements of the torus form. -/
theorem torusWord2_diag (c h d : R) : ∀ (Y w : List ℕ),
    torusWord2 c h h d Y w = torusWord c h d Y w
  | [], w => by simp [torusWord2, torusWord, phi2_diag]
  | y :: Y, w => by
    unfold torusWord2 torusWord
    rw [torusWord2_diag c h d Y w]
    congr 1
    · congr 1
      apply List.map_congr_left
      intro t _
      rw [torusWord2_diag c h d Y t.1]
    · congr 1
      ring

/-- `ρ_{Δ₁,Δ₂;d}(u,v)` for vectors with coordinates `u` (level `ℓ`) and `v` (level `ℓ'`). -/
def tw2Form (c h₁ h₂ d : R) {ℓ ℓ' : ℕ} (u : Nat.Partition ℓ → R) (v : Nat.Partition ℓ' → R) : R :=
  ∑ Y : Nat.Partition ℓ, ∑ Y' : Nat.Partition ℓ',
    u Y * v Y' * torusWord2 c h₁ h₂ d Y.word Y'.word

/-- `ρ_{Δ₁,Δ₂;d}(u,v_{Δ₂})` for a vector with coordinates `u`. -/
def tw1Form (c h₁ h₂ d : R) {ℓ : ℕ} (u : Nat.Partition ℓ → R) : R :=
  ∑ Y : Nat.Partition ℓ, u Y * torusWord2 c h₁ h₂ d Y.word []

variable {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S)

theorem map_tw2Form (c h₁ h₂ d : R) {ℓ ℓ' : ℕ} (u : Nat.Partition ℓ → R)
    (v : Nat.Partition ℓ' → R) :
    f (tw2Form c h₁ h₂ d u v) =
      tw2Form (f c) (f h₁) (f h₂) (f d) (fun Y => f (u Y)) (fun Y => f (v Y)) := by
  simp only [tw2Form, map_sum, map_mul, torusWord2_map]

theorem map_tw1Form (c h₁ h₂ d : R) {ℓ : ℕ} (u : Nat.Partition ℓ → R) :
    f (tw1Form c h₁ h₂ d u) = tw1Form (f c) (f h₁) (f h₂) (f d) (fun Y => f (u Y)) := by
  simp only [tw1Form, map_sum, map_mul, torusWord2_map]

theorem tw2Form_diag (c h d : R) {ℓ : ℕ} (u v : Nat.Partition ℓ → R) :
    tw2Form c h h d u v = torusForm c h d ℓ u v := by
  simp only [tw2Form, torusForm, dotProduct, Matrix.mulVec, torus, Matrix.of_apply,
    torusWord2_diag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => ?_
  ring

end Ring

section Complex

variable {c Δ₁ Δ₂ d : ℂ} {T : Verma ℂ c Δ₁ →ₗ[ℂ] Verma ℂ c Δ₂ →ₗ[ℂ] ℂ}

theorem twoWeight_pbwCoord (hT : Verma.IsTwoWeightPairing d T) {ℓ ℓ' : ℕ}
    (u : Nat.Partition ℓ → ℂ) (v : Nat.Partition ℓ' → ℂ) :
    T (Verma.pbwCoord ℓ u) (Verma.pbwCoord ℓ' v) = tw2Form c Δ₁ Δ₂ d u v := by
  rw [Verma.pbwCoord_apply, Verma.pbwCoord_apply, tw2Form]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => ?_
  rw [Verma.twoWeight_torusWord hT _ (word_pos Y) _ (word_pos Y')]
  ring

theorem twoWeight_pbwCoord_hw (hT : Verma.IsTwoWeightPairing d T) {ℓ : ℕ}
    (u : Nat.Partition ℓ → ℂ) :
    T (Verma.pbwCoord ℓ u) Verma.hw = tw1Form c Δ₁ Δ₂ d u := by
  rw [Verma.pbwCoord_apply, map_sum, LinearMap.sum_apply, tw1Form]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, LinearMap.smul_apply, ← Verma.neg_nil,
    Verma.twoWeight_torusWord hT _ (word_pos Y) _ (fun y hy => absurd hy List.not_mem_nil)]
  rfl

end Complex

/-- The polynomial `f_d(Δ₁,Δ₂) = ρ_{Δ₁,Δ₂;d}(𝒪 v_{Δ₁}, 𝒪 v_{Δ₂})` of l.2636–2642, in the two
weights. -/
noncomputable def twoPoly (c d : ℂ) {ℓ : ℕ} (x : Nat.Partition ℓ → ℂ) : MvPolynomial (Fin 2) ℂ :=
  tw2Form (MvPolynomial.C c) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.C d)
    (fun Y => MvPolynomial.C (x Y)) (fun Y => MvPolynomial.C (x Y))

theorem eval_twoPoly (c d Δ₁ Δ₂ : ℂ) {ℓ : ℕ} (x : Nat.Partition ℓ → ℂ) :
    MvPolynomial.eval ![Δ₁, Δ₂] (twoPoly c d x) = tw2Form c Δ₁ Δ₂ d x x := by
  unfold twoPoly
  rw [map_tw2Form]
  simp

/-- `f_d(Δ₁,Δ₂) = f_d(Δ₂,Δ₁)` (l.2643, from (10.2)). -/
theorem twoPoly_symm (hE : Cited_TwoWeightPairingExists) (c d Δ₁ Δ₂ : ℂ) {ℓ : ℕ}
    (x : Nat.Partition ℓ → ℂ) :
    MvPolynomial.eval ![Δ₁, Δ₂] (twoPoly c d x) = MvPolynomial.eval ![Δ₂, Δ₁] (twoPoly c d x) := by
  obtain ⟨T, hT⟩ := hE c Δ₁ Δ₂ d
  obtain ⟨T', hT'⟩ := hE c Δ₂ Δ₁ d
  rw [eval_twoPoly, eval_twoPoly, ← twoWeight_pbwCoord hT, ← twoWeight_pbwCoord hT']
  exact (lem_two_weight_ward_of_cited hE).2.2.1 c Δ₁ Δ₂ d T T' hT hT' _ _

theorem aeval_eval (v : Fin 2 → ℂ[X]) (F : MvPolynomial (Fin 2) ℂ) (a : ℂ) :
    (MvPolynomial.aeval v F).eval a = MvPolynomial.eval (fun i => (v i).eval a) F := by
  induction F using MvPolynomial.induction_on with
  | C z => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The diagonal restriction of `f_d` is the torus form `ρ_{Δ,d}(χ,χ)` as a polynomial in `Δ`. -/
theorem twoPoly_diag (c d : ℂ) {ℓ : ℕ} (x : Nat.Partition ℓ → ℂ) :
    MvPolynomial.aeval (fun _ : Fin 2 => (X : ℂ[X])) (twoPoly c d x) =
      torusForm (C c) (X : ℂ[X]) (C d) ℓ (fun Y => C (x Y)) (fun Y => C (x Y)) := by
  unfold twoPoly
  have h := map_tw2Form
    ((MvPolynomial.aeval (fun _ : Fin 2 => (X : ℂ[X])) : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] ℂ[X]) :
      MvPolynomial (Fin 2) ℂ →+* ℂ[X])
    (MvPolynomial.C c) (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.C d)
    (fun Y : Nat.Partition ℓ => MvPolynomial.C (x Y)) (fun Y : Nat.Partition ℓ => MvPolynomial.C (x Y))
  simp only [AlgHom.coe_toRingHom, RingHom.coe_coe, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    Polynomial.algebraMap_eq] at h
  rw [h, tw2Form_diag]

/-- The derivative along the diagonal is the sum of the two partial derivatives. -/
theorem deriv_diag (F : MvPolynomial (Fin 2) ℂ) (a : ℂ) :
    (derivative (MvPolynomial.aeval (fun _ : Fin 2 => (X : ℂ[X])) F)).eval a =
      (derivative (MvPolynomial.aeval (![X, C a] : Fin 2 → ℂ[X]) F)).eval a +
        (derivative (MvPolynomial.aeval (![C a, X] : Fin 2 → ℂ[X]) F)).eval a := by
  induction F using MvPolynomial.induction_on with
  | C z => simp
  | add p q hp hq =>
    simp only [map_add, eval_add, derivative_add, hp, hq]
    ring
  | mul_X p i hp =>
    have e1 := aeval_eval (fun _ => X) p a
    have e2 := aeval_eval ![X, C a] p a
    have e3 := aeval_eval ![C a, X] p a
    have k1 : (fun i : Fin 2 => ((fun _ : Fin 2 => (X : ℂ[X])) i).eval a) = fun _ => a := by
      funext i; simp
    have k2 : (fun i : Fin 2 => ((![X, C a] : Fin 2 → ℂ[X]) i).eval a) = fun _ => a := by
      funext i; fin_cases i <;> simp
    have k3 : (fun i : Fin 2 => ((![C a, X] : Fin 2 → ℂ[X]) i).eval a) = fun _ => a := by
      funext i; fin_cases i <;> simp
    rw [k1] at e1
    rw [k2] at e2
    rw [k3] at e3
    fin_cases i
    · simp only [map_mul, MvPolynomial.aeval_X, derivative_mul, eval_add, eval_mul, derivative_X,
        Fin.zero_eta, Matrix.cons_val_zero, eval_X, eval_C, derivative_C, mul_one, mul_zero,
        add_zero, hp, e1, e2, e3]
      ring
    · simp only [map_mul, MvPolynomial.aeval_X, derivative_mul, eval_add, eval_mul, derivative_X,
        Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, eval_X, eval_C, derivative_C,
        mul_one, mul_zero, add_zero, hp, e1, e2, e3]
      ring

/-- (12.1), first equality: `d/dx f_d(x,x) = 2 ∂_{x₁} f_d` on the diagonal. -/
theorem deriv_twoPoly_diag (hE : Cited_TwoWeightPairingExists) (c d h₀ : ℂ) {ℓ : ℕ}
    (x : Nat.Partition ℓ → ℂ) :
    torusCrossScalar c h₀ d x =
      2 * (derivative (MvPolynomial.aeval (![X, C h₀] : Fin 2 → ℂ[X]) (twoPoly c d x))).eval h₀ := by
  have hsym : MvPolynomial.aeval (![C h₀, X] : Fin 2 → ℂ[X]) (twoPoly c d x) =
      MvPolynomial.aeval (![X, C h₀] : Fin 2 → ℂ[X]) (twoPoly c d x) := by
    refine Polynomial.funext fun z => ?_
    rw [aeval_eval, aeval_eval]
    have k2 : (fun i : Fin 2 => ((![X, C h₀] : Fin 2 → ℂ[X]) i).eval z) = ![z, h₀] := by
      funext i; fin_cases i <;> simp
    have k3 : (fun i : Fin 2 => ((![C h₀, X] : Fin 2 → ℂ[X]) i).eval z) = ![h₀, z] := by
      funext i; fin_cases i <;> simp
    rw [k2, k3]
    exact twoPoly_symm hE c d h₀ z x
  unfold torusCrossScalar
  rw [← twoPoly_diag, deriv_diag, hsym]
  ring

/-- `f_0(x,x) = B_{c,Δ}(χ,χ)` ((10.4), l.2682): the same identity for the crossing scalar. -/
theorem deriv_twoPoly_diag_zero (hE : Cited_TwoWeightPairingExists) (c h₀ : ℂ) {ℓ : ℕ}
    (x : Nat.Partition ℓ → ℂ) :
    crossScalar c h₀ x =
      2 * (derivative (MvPolynomial.aeval (![X, C h₀] : Fin 2 → ℂ[X]) (twoPoly c 0 x))).eval h₀ := by
  rw [← deriv_twoPoly_diag hE]
  unfold torusCrossScalar crossScalar torusForm gramForm
  rw [map_zero, torus_zero]

end Virasoro.P2
