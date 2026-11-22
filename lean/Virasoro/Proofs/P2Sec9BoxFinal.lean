import Virasoro.Proofs.P2Sec9BoxWard
import Virasoro.Proofs.P2Sec9BoxEval

/-!
# Theorem 9.2 (generic first-layer Jantzen vertex ratio): the box formula (9.4)
(paper.tex l.2630–2715)
-/

namespace Virasoro.P2

open Virasoro Polynomial

/-- (12.1) in the momentum variable: with `Δ₁ = (Q²-L₁²)/4`, `∂_{Δ₁} = (-2/L₁)∂_{L₁}`
(l.2686–2689), for `d = h_{2k+1,2m+1}(b)`:
`∂_{x₁}f_d(0,0) · (-L_in/2) = κ² · ∂_{L₁}P_{R,S}|_{L_in} · P_{R,S}|_{L_out}`. -/
theorem partial_box (hE : Cited_TwoWeightPairingExists) {b : ℂ} (hb : b ≠ 0) {R S : ℕ}
    (x : Nat.Partition (R * S) → ℂ) {κ : ℂ}
    (h1 : ∀ Δ₁ d : ℂ, MvPolynomial.eval ![Δ₁, kacH R S b] (twoPoly (kacC b) d x) =
      κ * fusP R S b Δ₁ d * tw1Form (kacC b) Δ₁ (kacH R S b + ((R * S : ℕ) : ℂ)) d x)
    (h2 : ∀ d : ℂ, tw1Form (kacC b) (kacH R S b) (kacH R S b + ((R * S : ℕ) : ℂ)) d x =
      κ * fusP R S b (kacH R S b + ((R * S : ℕ) : ℂ)) d)
    {k m : ℕ} (hk : k < R) (hm : m < S) :
    (derivative (MvPolynomial.aeval (![X, C (kacH R S b)] : Fin 2 → ℂ[X])
        (twoPoly (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) x))).eval (kacH R S b) *
      (-((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) = κ ^ 2 * kap R S b * boxNum R S k m (b ^ 2) := by
  set d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b with hd
  set Md : ℂ := (2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹ with hMd
  set Lin : ℂ := (R : ℂ) * b + (S : ℂ) * b⁻¹ with hLin
  set Lout : ℂ := (R : ℂ) * b - (S : ℂ) * b⁻¹ with hLout
  set h₀ : ℂ := kacH R S b with hh₀
  have hMd2 : Md ^ 2 = (b + b⁻¹) ^ 2 - 4 * d := by
    simp only [hd, hMd, kacH]
    push_cast
    ring
  have hin : h₀ = ((b + b⁻¹) ^ 2 - Lin ^ 2) / 4 := by
    simp only [hh₀, hLin, kacH, Int.cast_natCast]
  have hout : h₀ + ((R * S : ℕ) : ℂ) = ((b + b⁻¹) ^ 2 - Lout ^ 2) / 4 := by
    simp only [hh₀, hLout, kacH, Int.cast_natCast]
    push_cast
    field_simp
    ring
  set g : ℂ[X] := MvPolynomial.aeval (![X, C h₀] : Fin 2 → ℂ[X]) (twoPoly (kacC b) d x) with hg
  set q : ℂ[X] := tw1Form (C (kacC b)) (X : ℂ[X]) (C (h₀ + ((R * S : ℕ) : ℂ))) (C d)
    (fun Y => C (x Y)) with hq
  set sub : ℂ[X] := C ((b + b⁻¹) ^ 2 / 4) - C (1 / 4) * X ^ 2 with hsub
  have hqev : ∀ z : ℂ, q.eval z = tw1Form (kacC b) z (h₀ + ((R * S : ℕ) : ℂ)) d x := by
    intro z
    have := map_tw1Form (Polynomial.evalRingHom z) (C (kacC b)) (X : ℂ[X])
      (C (h₀ + ((R * S : ℕ) : ℂ))) (C d) (fun Y : Nat.Partition (R * S) => C (x Y))
    simpa only [coe_evalRingHom, eval_C, eval_X] using this
  have hgev : ∀ z : ℂ, g.eval z = κ * fusP R S b z d * q.eval z := by
    intro z
    have kk : (fun i : Fin 2 => ((![X, C h₀] : Fin 2 → ℂ[X]) i).eval z) = ![z, h₀] := by
      funext i; fin_cases i <;> simp
    rw [hg, aeval_eval, kk, h1, hqev]
  have hsubev : ∀ z : ℂ, sub.eval z = ((b + b⁻¹) ^ 2 - z ^ 2) / 4 := by
    intro z
    simp only [hsub, eval_sub, eval_C, eval_mul, eval_pow, eval_X]
    ring
  have hpoly : g.comp sub = C κ * fusL R S b Md * q.comp sub := by
    refine Polynomial.funext fun z => ?_
    rw [eval_comp, eval_mul, eval_mul, eval_C, eval_comp, hgev, hsubev,
      fusP_eq_fusL R S b z Md d hMd2]
  obtain ⟨hzero, hbox⟩ := fusL_box hb hk hm
  have hder := congrArg (fun P : ℂ[X] => (derivative P).eval Lin) hpoly
  simp only [derivative_comp, derivative_mul, derivative_C, eval_mul, eval_add, eval_comp,
    eval_C, zero_mul, zero_add] at hder
  rw [hsubev Lin, ← hin, hzero, hqev h₀, h2 d, hout, fusP_eq_fusL R S b Lout Md d hMd2] at hder
  have hsubd : (derivative sub).eval Lin = -Lin / 2 := by
    simp only [hsub, derivative_sub, derivative_C, derivative_mul, derivative_X_pow, eval_sub,
      eval_mul, eval_C, eval_add, eval_pow, eval_X, zero_sub, zero_mul, zero_add, eval_zero,
      eval_neg]
    push_cast
    ring
  rw [hsubd] at hder
  linear_combination hder + κ ^ 2 * hbox

/-- The box formula (9.4).  Cited inputs: existence of the two-weight pairing (Lemma 10.1),
the normalized singular vector and its uniqueness, and the fusion polynomial
(Proposition 10.2(ii)). -/
theorem sub_first_layer_box_of_cited (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) :
    Stmt_sub_first_layer_box := by
  intro b hb hirr R S k m hR hS hk hm x hx
  obtain ⟨κ, hκ, h1, h2⟩ := box_ward hE hH hU hF hb hR hS x hx
  have hLin : -((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2 ≠ 0 := by
    have h := lin_ne_generic hirr (R : ℤ) (S : ℤ) (Or.inl (by omega))
    intro h0
    apply h
    have e : ((R : ℤ) : ℂ) * b ^ 2 + ((S : ℤ) : ℂ) =
        -2 * b * (-((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) := by
      push_cast
      field_simp
    rw [e, h0, mul_zero]
  have hd0 : kacH (2 * ((0 : ℕ) : ℤ) + 1) (2 * ((0 : ℕ) : ℤ) + 1) b = 0 := by
    simp [kacH]
  have hden : boxNum R S 0 0 (b ^ 2) = boxDen R S (b ^ 2) := by
    simp [boxNum, boxDen]
  have hT := partial_box hE hb x h1 h2 hk hm
  have hB := partial_box hE hb x h1 h2 (k := 0) (m := 0) (by omega) (by omega)
  rw [hd0, hden] at hB
  rw [← mul_div_assoc] at hT hB
  have eT := deriv_twoPoly_diag hE (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
    (kacH R S b) x
  have eB := deriv_twoPoly_diag_zero hE (kacC b) (kacH R S b) x
  have hden0 : boxDen R S (b ^ 2) ≠ 0 := (box_gamma_generic hb hirr hk hm).1
  have hcross : crossScalar (kacC b) (kacH R S b) x * (-((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) =
      2 * (κ ^ 2 * kap R S b * boxDen R S (b ^ 2)) := by
    rw [eB]
    linear_combination 2 * hB
  have htorus : torusCrossScalar (kacC b) (kacH R S b)
      (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) x *
        (-((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) =
      2 * (κ ^ 2 * kap R S b * boxNum R S k m (b ^ 2)) := by
    rw [eT]
    linear_combination 2 * hT
  refine ⟨fun h0 => ?_, ?_⟩
  · rw [h0, zero_mul] at hcross
    exact mul_ne_zero two_ne_zero
      (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hκ) (kap_ne_zero R S hb)) hden0) hcross.symm
  · refine mul_right_cancel₀ hLin ?_
    linear_combination boxDen R S (b ^ 2) * htorus - boxNum R S k m (b ^ 2) * hcross

example (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) : Stmt_sub_first_layer_box :=
  sub_first_layer_box_of_cited hE hH hU hF

/-- Theorem 9.2.

Paper label: thm:first-layer-ratio -/
theorem thm_first_layer_ratio_of_cited (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) :
    Stmt_thm_first_layer_ratio :=
  thm_first_layer_ratio_of_box (sub_first_layer_box_of_cited hE hH hU hF)

example (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) : Stmt_thm_first_layer_ratio :=
  thm_first_layer_ratio_of_cited hE hH hU hF

end Virasoro.P2
