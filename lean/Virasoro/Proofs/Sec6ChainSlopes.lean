import Virasoro.Proofs.Sec6ChainSteps
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp

/-!
# Proposition 6.7: slopes, residue limits and boxes of the first steps (paper.tex l.1153–1168)

For the first step `g_i`: `ρ_{g_i} = ε_i ρ`, `4p'² ḣ_{g_i} = p'² − p² − n₀(n₁ + iN₀)`
(l.1153–1155); the box of `(r + jp, s + jp')` meets `ℤ(p,p')` at the `j'` with `|j'| ≤ j`
(l.1165–1166), so the top coefficient of `ρ_g y ∏_{j'}(1 − y/(j'κ₀))` is
`ρ_g (−1)^j/(j!² κ₀^{2j})`.
-/

namespace Virasoro.ChainEval

open Polynomial Finset

variable {p p' r s : ℕ}

/-- `ρ = −n₀/(2(p'−p))`. -/
noncomputable def rho (p p' r s : ℕ) : ℂ := -(n0 p p' r s : ℂ) / (2 * ((p' : ℂ) - p))

theorem Setup.p'_ne (h : Setup p p' r s) : (p' : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (by have := h.hp'; omega)

theorem Setup.p_ne (h : Setup p p' r s) : (p : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (by have := h.hp; omega)

theorem Setup.p_ne_p' (h : Setup p p' r s) : p ≠ p' := by
  intro he
  have h1 := h.cop
  rw [he, Nat.coprime_self] at h1
  have := h.hp'
  omega

theorem Setup.sub_ne (h : Setup p p' r s) : (p' : ℂ) - p ≠ 0 :=
  sub_ne_zero.2 fun he => h.p_ne_p' (Nat.cast_injective he).symm

/-- `4p'² ḣ_g = p'² − p² − (p'u − pv)(p'u + pv)`. -/
theorem Setup.hdot_formula (h : Setup p p' r s) (g : Label) :
    4 * (p' : ℂ) ^ 2 * hdotNu p p' g =
      (p' : ℂ) ^ 2 - (p : ℂ) ^ 2 - ((p' : ℂ) * g.1 - p * g.2) * ((p' : ℂ) * g.1 + p * g.2) := by
  have hp' := h.p'_ne
  unfold hdotNu
  field_simp
  ring

theorem Setup.rhoG_gL (h : Setup p p' r s) (i : ℤ) :
    rhoG p p' (gL p p' r s i) = (sgnI i : ℂ) * rho p p' r s := by
  have h1 := congrArg (Int.cast : ℤ → ℂ) (h.gL_diff i)
  push_cast at h1
  unfold rhoG rho
  rw [h1]
  ring

/-- `4p'² ḣ_{g_i} = p'² − p² − n₀(n₁ + iN₀)` (paper.tex l.1154–1155). -/
theorem Setup.hdot_gL (h : Setup p p' r s) (i : ℤ) :
    4 * (p' : ℂ) ^ 2 * hdotNu p p' (gL p p' r s i) =
      (p' : ℂ) ^ 2 - (p : ℂ) ^ 2 - (n0 p p' r s : ℂ) * ((n1 p p' r s : ℂ) + i * N0 p p') := by
  have h1 := congrArg (Int.cast : ℤ → ℂ) (h.gL_diff i)
  have h2 := congrArg (Int.cast : ℤ → ℂ) (h.gL_sum i)
  have h3 := congrArg (Int.cast : ℤ → ℂ) (sgnI_sq i)
  push_cast at h1 h2 h3
  rw [h.hdot_formula, h1, h2]
  linear_combination (-(n0 p p' r s : ℂ) * ((n1 p p' r s : ℂ) + i * N0 p p')) * h3

/-- `ḣ_κ − ḣ_i = n₀N₀(i − κ)/(4p'²)` (paper.tex l.1155, l.1163). -/
theorem Setup.hdot_sub (h : Setup p p' r s) (κ i : ℤ) :
    hdotNu p p' (gL p p' r s κ) - hdotNu p p' (gL p p' r s i) =
      (n0 p p' r s : ℂ) * N0 p p' / (4 * (p' : ℂ) ^ 2) * ((i : ℂ) - κ) := by
  have hp' := h.p'_ne
  have h1 := h.hdot_gL κ
  have h2 := h.hdot_gL i
  field_simp
  linear_combination h1 - h2

/-- The box of `(r + jp, s + jp')` meets `ℤ(p,p')` at the `j' ≠ 0` with `|j'| ≤ j`. -/
theorem Setup.boxMults_plus (h : Setup p p' r s) (j : ℕ) :
    boxMults p p' (r + j * p, s + j * p') = (Icc (-(j : ℤ)) j).erase 0 := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have hp' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  have hr : (0 : ℤ) < r := by exact_mod_cast h.hr
  have hs : (0 : ℤ) < s := by exact_mod_cast h.hs
  have hrp : (r : ℤ) < p := by exact_mod_cast h.hrp
  have hsp : (s : ℤ) < p' := by exact_mod_cast h.hsp
  have hj : (0 : ℤ) ≤ j := Int.natCast_nonneg j
  ext j'
  simp only [boxMults, mem_filter, mem_Icc, mem_erase, Nat.cast_add, Nat.cast_mul]
  constructor
  · rintro ⟨_, h0, h1, h2, _, _⟩
    refine ⟨h0, ?_, ?_⟩
    · by_contra hc
      have hc := not_le.1 hc
      nlinarith
    · by_contra hc
      have hc := not_le.1 hc
      nlinarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨⟨?_, ?_⟩, h0, ?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- A product over `0 < |j'| ≤ j` by pairs `±(t+1)`. -/
theorem prod_box (f : ℤ → ℂ) (j : ℕ) :
    ∏ j' ∈ (Icc (-(j : ℤ)) j).erase 0, f j' =
      ∏ t ∈ range j, (f ((t : ℤ) + 1) * f (-((t : ℤ) + 1))) := by
  induction j with
  | zero =>
    have e : (Icc (-((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).erase 0 = ∅ := by
      ext x
      simp only [mem_erase, mem_Icc, notMem_empty, iff_false, Nat.cast_zero]
      omega
    rw [e, prod_empty, prod_range_zero]
  | succ j ih =>
    have e : (Icc (-((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ)).erase 0 =
        insert ((j : ℤ) + 1) (insert (-((j : ℤ) + 1)) ((Icc (-(j : ℤ)) j).erase 0)) := by
      ext x
      simp only [mem_erase, mem_Icc, mem_insert, Nat.cast_add, Nat.cast_one]
      omega
    have h1 : ((j : ℤ) + 1) ∉ insert (-((j : ℤ) + 1)) ((Icc (-(j : ℤ)) j).erase 0) := by
      simp only [mem_erase, mem_Icc, mem_insert]
      omega
    have h2 : (-((j : ℤ) + 1)) ∉ (Icc (-(j : ℤ)) j).erase 0 := by
      simp only [mem_erase, mem_Icc]
      omega
    rw [e, prod_insert h1, prod_insert h2, ih, prod_range_succ]
    ring

/-- The top coefficient of `ρ y ∏_b (1 − c_b y)`. -/
theorem coeff_resLimit_top {ι : Type*} (B : Finset ι) (c : ι → ℂ) (ρ : ℂ) :
    (C ρ * X * ∏ b ∈ B, (1 - C (c b) * X)).coeff (B.card + 1) = ρ * ∏ b ∈ B, (-c b) := by
  have h1 : ∀ b ∈ B, (1 - C (c b) * X : ℂ[X]).natDegree ≤ 1 := fun b _ =>
    (natDegree_sub_le _ _).trans (max_le (by simp) (((natDegree_C_mul_le _ _).trans natDegree_X_le)))
  have h2 := coeff_prod_of_natDegree_le B (fun b => (1 - C (c b) * X : ℂ[X])) 1 h1
  rw [mul_one] at h2
  rw [mul_assoc, coeff_C_mul, coeff_X_mul, h2]
  congr 1
  refine prod_congr rfl fun b _ => ?_
  simp [coeff_one]

/-- A product with fewer than the top number of factors has no top coefficient. -/
theorem coeff_resLimit_above {ι : Type*} (B : Finset ι) (c : ι → ℂ) (ρ : ℂ) {n : ℕ}
    (hn : B.card + 1 < n) : (C ρ * X * ∏ b ∈ B, (1 - C (c b) * X)).coeff n = 0 := by
  have h1 : ∀ b ∈ B, (1 - C (c b) * X : ℂ[X]).natDegree ≤ 1 := fun b _ =>
    (natDegree_sub_le _ _).trans (max_le (by simp) (((natDegree_C_mul_le _ _).trans natDegree_X_le)))
  have h2 : (∏ b ∈ B, (1 - C (c b) * X : ℂ[X])).natDegree ≤ B.card := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (sum_le_card_nsmul _ _ 1 h1).trans ?_
    simp
  refine coeff_eq_zero_of_natDegree_lt ?_
  refine lt_of_le_of_lt (natDegree_mul_le.trans ?_) hn
  have h3 : (C ρ * X : ℂ[X]).natDegree ≤ 1 := ((natDegree_C_mul_le _ _).trans natDegree_X_le)
  omega

theorem prod_range_sub (n : ℕ) : ∏ t ∈ range n, ((t : ℂ) - n) = (-1) ^ n * (n.factorial : ℂ) := by
  have h1 : ∀ t ∈ range n, ((t : ℂ) - n) = -1 * (((n - 1 - t : ℕ) : ℂ) + 1) := by
    intro t ht
    have ht' := mem_range.1 ht
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_const, card_range]
  congr 1
  have h2 := prod_range_reflect (fun t : ℕ => ((t : ℂ) + 1)) n
  rw [h2]
  have h3 := prod_range_add_one_eq_factorial n
  have h4 := congrArg (Nat.cast : ℕ → ℂ) h3
  push_cast at h4
  exact h4

end Virasoro.ChainEval
