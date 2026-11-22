import Virasoro.Proofs.P2Sec9BoxFus

/-!
# Theorem 9.2: evaluation of the two factors of (12.2) (paper.tex l.2686–2715)

At `L₁ = L_in = Rb + Sb⁻¹` the product `P_{R,S}` has the vanishing factor of `(p₀,q₀) =
(2k+1-R, 2m+1-S)`; the remaining factors of `∂_{L₁}P_{R,S}|_{L_in} · P_{R,S}|_{L_out}` are, up to
a constant independent of `(k,m)`, the linear forms `(a+k)t + (b'+m)` of the four quadrants.
-/

namespace Virasoro.P2

open Virasoro Polynomial

/-- The `(k,m)`-independent constant: `1/2` from the derivative of the vanishing factor, and one
factor `±b⁻¹` for each of the `4RS-1` remaining factors. -/
noncomputable def kap (R S : ℕ) (b : ℂ) : ℂ :=
  1 / 2 * b⁻¹ ^ (R * S) * (-b⁻¹) ^ (R * S - 1) * b⁻¹ ^ (R * S) * (-b⁻¹) ^ (R * S)

theorem kap_ne_zero (R S : ℕ) {b : ℂ} (hb : b ≠ 0) : kap R S b ≠ 0 := by
  unfold kap
  have h1 : b⁻¹ ≠ 0 := inv_ne_zero hb
  have h2 : -b⁻¹ ≠ 0 := neg_ne_zero.2 h1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ h1))
    (pow_ne_zero _ h2)) (pow_ne_zero _ h1)) (pow_ne_zero _ h2)

section

variable {b : ℂ} (hb : b ≠ 0) (R S k m : ℕ)

include hb

theorem facA_in (y : ℕ × ℕ) :
    ((R : ℂ) * b + (S : ℂ) * b⁻¹ + ((2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹) +
        bet b R S y) / 2 = b⁻¹ * linV (b ^ 2) ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 + m) := by
  simp only [bet, linV]
  push_cast
  field_simp
  ring

theorem facB_in (y : ℕ × ℕ) :
    ((R : ℂ) * b + (S : ℂ) * b⁻¹ - ((2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹) +
        bet b R S y) / 2 = -b⁻¹ * linV (b ^ 2) ((k : ℤ) - y.1, (m : ℤ) - y.2) := by
  simp only [bet, linV]
  push_cast
  field_simp
  ring

theorem facA_out (y : ℕ × ℕ) :
    ((R : ℂ) * b - (S : ℂ) * b⁻¹ + ((2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹) +
        bet b R S y) / 2 = b⁻¹ * linV (b ^ 2) ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 - S + m) := by
  simp only [bet, linV]
  push_cast
  field_simp
  ring

theorem facB_out (y : ℕ × ℕ) :
    ((R : ℂ) * b - (S : ℂ) * b⁻¹ - ((2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹) +
        bet b R S y) / 2 = -b⁻¹ * linV (b ^ 2) ((k : ℤ) - y.1, (S : ℤ) - y.2 + m) := by
  simp only [bet, linV]
  push_cast
  field_simp
  ring

end

theorem card_idxBox (R S : ℕ) : (idxBox R S).card = R * S := by
  simp [idxBox]

/-- The vanishing of `P_{R,S}` at `L_in` and the evaluation of
`∂_{L₁}P_{R,S}|_{L_in} · P_{R,S}|_{L_out}` (l.2686–2713). -/
theorem fusL_box {b : ℂ} (hb : b ≠ 0) {R S k m : ℕ} (hk : k < R) (hm : m < S) :
    (fusL R S b ((2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹)).eval
        ((R : ℂ) * b + (S : ℂ) * b⁻¹) = 0 ∧
      (derivative (fusL R S b ((2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹))).eval
          ((R : ℂ) * b + (S : ℂ) * b⁻¹) *
        (fusL R S b ((2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹)).eval
          ((R : ℂ) * b - (S : ℂ) * b⁻¹) = kap R S b * boxNum R S k m (b ^ 2) := by
  set Md : ℂ := (2 * (k : ℂ) + 1) * b + (2 * (m : ℂ) + 1) * b⁻¹ with hMd
  set Lin : ℂ := (R : ℂ) * b + (S : ℂ) * b⁻¹ with hLin
  set Lout : ℂ := (R : ℂ) * b - (S : ℂ) * b⁻¹ with hLout
  set g : ℕ × ℕ → ℂ[X] := fun y =>
    (C (1 / 2) * (X + C (Md + bet b R S y))) * (C (1 / 2) * (X - C (Md - bet b R S y))) with hg
  have hy0 : (k, m) ∈ idxBox R S := by
    simp only [idxBox, Finset.mem_product, Finset.mem_range]
    exact ⟨hk, hm⟩
  have hsplit : fusL R S b Md = g (k, m) * ∏ y ∈ (idxBox R S).erase (k, m), g y :=
    (Finset.mul_prod_erase _ g hy0).symm
  have hB0 : (Lin - Md + bet b R S (k, m)) / 2 = 0 := by
    rw [hLin, hMd, facB_in hb R S k m (k, m)]
    simp [linV]
  have hgev : ∀ y L, (g y).eval L =
      ((L + Md + bet b R S y) / 2) * ((L - Md + bet b R S y) / 2) := by
    intro y L
    simp only [hg, eval_mul, eval_C, eval_add, eval_sub, eval_X]
    ring
  have hzero : (fusL R S b Md).eval Lin = 0 := by
    rw [hsplit, eval_mul, hgev, hB0, mul_zero, zero_mul]
  refine ⟨hzero, ?_⟩
  have hder : (derivative (fusL R S b Md)).eval Lin =
      1 / 2 * ((Lin + Md + bet b R S (k, m)) / 2) *
        ∏ y ∈ (idxBox R S).erase (k, m),
          ((Lin + Md + bet b R S y) / 2) * ((Lin - Md + bet b R S y) / 2) := by
    rw [hsplit, derivative_mul, eval_add, eval_mul, eval_mul, hgev, hB0, mul_zero, zero_mul,
      add_zero, eval_prod]
    simp only [hgev]
    congr 1
    simp only [hg, derivative_mul, derivative_C, derivative_add, derivative_sub, derivative_X,
      eval_mul, eval_add, eval_C, eval_sub, eval_X, zero_mul, zero_add, sub_zero, add_zero,
      eval_one, eval_zero, mul_one]
    linear_combination (1 / 2 : ℂ) * hB0
  have hP1 : ∏ y ∈ idxBox R S, (Lin + Md + bet b R S y) / 2 =
      b⁻¹ ^ (R * S) * ∏ y ∈ idxBox R S, linV (b ^ 2) ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 + m) := by
    rw [Finset.prod_congr rfl (fun y _ => facA_in hb R S k m y), Finset.prod_mul_distrib,
      Finset.prod_const, card_idxBox]
  have hP2 : ∏ y ∈ (idxBox R S).erase (k, m), (Lin - Md + bet b R S y) / 2 =
      (-b⁻¹) ^ (R * S - 1) *
        ∏ y ∈ (idxBox R S).erase (k, m), linV (b ^ 2) ((k : ℤ) - y.1, (m : ℤ) - y.2) := by
    rw [Finset.prod_congr rfl (fun y _ => facB_in hb R S k m y), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_erase_of_mem hy0, card_idxBox]
  have hP3 : ∏ y ∈ idxBox R S, (Lout + Md + bet b R S y) / 2 =
      b⁻¹ ^ (R * S) *
        ∏ y ∈ idxBox R S, linV (b ^ 2) ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 - S + m) := by
    rw [Finset.prod_congr rfl (fun y _ => facA_out hb R S k m y), Finset.prod_mul_distrib,
      Finset.prod_const, card_idxBox]
  have hP4 : ∏ y ∈ idxBox R S, (Lout - Md + bet b R S y) / 2 =
      (-b⁻¹) ^ (R * S) *
        ∏ y ∈ idxBox R S, linV (b ^ 2) ((k : ℤ) - y.1, (S : ℤ) - y.2 + m) := by
    rw [Finset.prod_congr rfl (fun y _ => facB_out hb R S k m y), Finset.prod_mul_distrib,
      Finset.prod_const, card_idxBox]
  have hA : (Lin + Md + bet b R S (k, m)) / 2 *
      ∏ y ∈ (idxBox R S).erase (k, m), (Lin + Md + bet b R S y) / 2 =
      ∏ y ∈ idxBox R S, (Lin + Md + bet b R S y) / 2 :=
    Finset.mul_prod_erase _ (fun y => (Lin + Md + bet b R S y) / 2) hy0
  rw [hder, fusL_eval, Finset.prod_mul_distrib, Finset.prod_mul_distrib, hP2, hP3, hP4,
    boxNum_shift, box_quadrants hk hm (linV (b ^ 2))]
  rw [hP1] at hA
  unfold kap
  linear_combination (1 / 2 * ((-b⁻¹) ^ (R * S - 1) *
      ∏ y ∈ (idxBox R S).erase (k, m), linV (b ^ 2) ((k : ℤ) - y.1, (m : ℤ) - y.2)) *
    (b⁻¹ ^ (R * S) * ∏ y ∈ idxBox R S, linV (b ^ 2) ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 - S + m)) *
    ((-b⁻¹) ^ (R * S) * ∏ y ∈ idxBox R S, linV (b ^ 2) ((k : ℤ) - y.1, (S : ℤ) - y.2 + m))) * hA

end Virasoro.P2
