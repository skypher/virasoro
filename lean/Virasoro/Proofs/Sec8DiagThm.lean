import Virasoro.Proofs.Sec8DiagKappa

/-!
# Theorem 8.8 (`thm:diagonal`)

From the coefficient identities of (8.2) (`Ecoef_zero`), by induction on `D` for all bases:
`D` odd, `j` odd: the coefficient of the class of `μ` gives `f_j = 0`;
`D` even, `j` odd: the coefficient of the class of `a` gives `f_j = f_{j-1}`, and the constant term
`f_j (π_μ - π_a) = -f_{j-1}(L_a+k, j) ∑_θ κ̂(a,θ,μ) π_θ`;
`D` odd, `j` even: the coefficient of the class of `μ` gives `f_j = -f_{j-1}(L_a+k, j) ∑_θ κ̂(a,θ,μ)`;
`D` even, `j` even: `f_j = f_{j+1}`.  The sums of `κ̂` are evaluated in closed form.
-/

namespace Virasoro

open scoped LaurentSeries

theorem TA_eq (L U : ℕ) :
    TA L U = (Finset.range ((U - L) / 2)).image (fun ρ => L + 1 + 2 * ρ) := by
  ext m
  simp only [TA, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(m - L - 1) / 2, by omega, by omega⟩
  · rintro ⟨ρ, hρ, rfl⟩
    omega

theorem TB_eq (L U : ℕ) :
    TB L U = (Finset.range ((U - L - 1) / 2)).image (fun ρ => L + 2 + 2 * ρ) := by
  ext m
  simp only [TB, Finset.mem_filter, Finset.mem_Ioo, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(m - L - 2) / 2, by omega, by omega⟩
  · rintro ⟨ρ, hρ, rfl⟩
    omega

theorem prod_range_shift (c i : ℕ) :
    ∏ ρ ∈ Finset.range i, ((c : ℚ) + 1 + ρ) = ((c + i).factorial : ℚ) / c.factorial := by
  have hc : (c.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos c).ne'
  induction i with
  | zero =>
    simp only [Finset.prod_range_zero, Nat.add_zero]
    rw [div_self hc]
  | succ i ih =>
    rw [Finset.prod_range_succ, ih, show c + (i + 1) = (c + i) + 1 by ring, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem prod_negmul (i : ℕ) (f g : ℕ → ℚ) :
    ∏ ρ ∈ Finset.range i, (-(f ρ * g ρ)) =
      (-1) ^ i * (∏ ρ ∈ Finset.range i, f ρ) * ∏ ρ ∈ Finset.range i, g ρ := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_range_succ, Finset.prod_range_succ, pow_succ]
    ring

/-- The numerator product in closed form. -/
theorem numP_closed (l n' c U : ℕ) (hc : (U - (l + (2 * n' + 1))) / 2 = c) :
    ∏ m ∈ TA (l + (2 * n' + 1)) U, ((l : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4) =
      (-1) ^ c * (((n' + c).factorial : ℚ) / n'.factorial) *
        (((l + n' + c).factorial : ℚ) / (l + n').factorial) := by
  rw [TA_eq, Finset.prod_image (fun x _ y _ h => by (try simp only at h); omega), hc]
  have e : ∀ ρ ∈ Finset.range c, ((l : ℚ) ^ 2 / 4 -
      ((l + (2 * n' + 1) + 1 + 2 * ρ : ℕ) : ℚ) ^ 2 / 4) =
      -(((n' : ℚ) + 1 + ρ) * (((l + n' : ℕ) : ℚ) + 1 + ρ)) := by
    intro ρ _; push_cast; ring
  rw [Finset.prod_congr rfl e, prod_negmul, prod_range_shift, prod_range_shift]

/-- The denominator product in closed form. -/
theorem Q_closed (L c U : ℕ) (hc : (U - L - 1) / 2 = c) :
    ∏ m ∈ TB L U, ((L : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4) =
      (-1) ^ c * (c.factorial : ℚ) * (((L + c).factorial : ℚ) / L.factorial) := by
  rw [TB_eq, Finset.prod_image (fun x _ y _ h => by (try simp only at h); omega), hc]
  have e : ∀ ρ ∈ Finset.range c, ((L : ℚ) ^ 2 / 4 - ((L + 2 + 2 * ρ : ℕ) : ℚ) ^ 2 / 4) =
      -(((((0 : ℕ) : ℚ) + 1 + ρ)) * ((L : ℚ) + 1 + ρ)) := by
    intro ρ _; push_cast; ring
  rw [Finset.prod_congr rfl e, prod_negmul, prod_range_shift, prod_range_shift]
  simp only [Nat.zero_add, Nat.factorial_zero, Nat.cast_one, div_one]

theorem fDiag_eval (l D j : ℕ) (h : ¬ (j % 2 = 1 ∧ D % 2 = 1)) :
    fDiag l D j = (-1) ^ (j / 2) * (((D - 1) / 2).choose (j / 2) : ℚ) *
      ((l + (D - 1) / 2).choose (j / 2) : ℚ) / ((l + D - 1).choose (j / 2) : ℚ) := by
  unfold fDiag; rw [if_neg h]

theorem choose_add (a b : ℕ) :
    (((a + b).choose b : ℕ) : ℚ) = ((a + b).factorial : ℚ) / ((b.factorial : ℚ) * a.factorial) := by
  rw [Nat.cast_choose ℚ (Nat.le_add_left b a), Nat.add_sub_cancel]

/-- The closed form for `D = 2n+2`, `j = 2i+1` (`n = n' + i`). -/
theorem F2_identity (l n' i : ℕ) :
    fDiag l (2 * n' + 2 * i + 2) (2 * i + 1) =
      fDiag (l + (2 * n' + 1)) (2 * i + 1) (2 * i) *
        ((-1) ^ i * (((n' + i).factorial : ℚ) / n'.factorial) *
          (((l + n' + i).factorial : ℚ) / (l + n').factorial)) /
        ((-1) ^ i * (i.factorial : ℚ) *
          (((l + (2 * n' + 1) + i).factorial : ℚ) / (l + (2 * n' + 1)).factorial)) := by
  rw [fDiag_eval _ _ _ (by omega), fDiag_eval _ _ _ (by omega)]
  rw [show (2 * n' + 2 * i + 2 - 1) / 2 = n' + i by omega, show (2 * i + 1) / 2 = i by omega,
    show (2 * i + 1 - 1) / 2 = i by omega, show 2 * i / 2 = i by omega,
    show l + (n' + i) = l + n' + i by ring,
    show l + (2 * n' + 2 * i + 2) - 1 = l + (2 * n' + 1) + i + i by omega,
    show l + (2 * n' + 1) + (2 * i + 1) - 1 = l + (2 * n' + 1) + i + i by omega,
    Nat.choose_self, choose_add n' i, choose_add (l + n') i, choose_add (l + (2 * n' + 1) + i) i,
    choose_add (l + (2 * n' + 1)) i]
  have h1 : ((n' + i).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (n'.factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((l + n' + i).factorial : ℚ) ≠ 0 := by positivity
  have h4 : ((l + n').factorial : ℚ) ≠ 0 := by positivity
  have h5 : (i.factorial : ℚ) ≠ 0 := by positivity
  have h6 : ((l + (2 * n' + 1) + i).factorial : ℚ) ≠ 0 := by positivity
  have h7 : ((l + (2 * n' + 1)).factorial : ℚ) ≠ 0 := by positivity
  have h8 : ((l + (2 * n' + 1) + i + i).factorial : ℚ) ≠ 0 := by positivity
  have h9 : ((-1 : ℚ) ^ i) ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  first | (field_simp; done) | (field_simp; ring)

/-- The closed form for `D = 2n+1`, `j = 2i` (`i = i' + 1`, `n = n' + i`). -/
theorem F1_identity (l n' i' : ℕ) :
    fDiag l (2 * n' + 2 * i' + 3) (2 * i' + 2) =
      fDiag (l + (2 * n' + 1)) (2 * i' + 2) (2 * i' + 1) *
        ((-1) ^ (i' + 1) * (((n' + (i' + 1)).factorial : ℚ) / n'.factorial) *
          (((l + n' + (i' + 1)).factorial : ℚ) / (l + n').factorial)) /
        (((-1) ^ i' * (i'.factorial : ℚ) *
          (((l + (2 * n' + 1) + i').factorial : ℚ) / (l + (2 * n' + 1)).factorial)) *
          (((i' : ℚ) + 1) * (((l + (2 * n' + 1) + i' : ℕ) : ℚ) + 1))) := by
  rw [fDiag_eval _ _ _ (by omega), fDiag_eval _ _ _ (by omega)]
  rw [show (2 * n' + 2 * i' + 3 - 1) / 2 = n' + (i' + 1) by omega,
    show (2 * i' + 2) / 2 = i' + 1 by omega, show (2 * i' + 2 - 1) / 2 = i' by omega,
    show (2 * i' + 1) / 2 = i' by omega,
    show l + (n' + (i' + 1)) = l + n' + (i' + 1) by ring,
    show l + (2 * n' + 2 * i' + 3) - 1 = l + (2 * n' + 1) + i' + (i' + 1) by omega,
    show l + (2 * n' + 1) + (2 * i' + 2) - 1 = l + (2 * n' + 1) + i' + 1 + i' by omega,
    Nat.choose_self, choose_add n' (i' + 1), choose_add (l + n') (i' + 1),
    choose_add (l + (2 * n' + 1) + i') (i' + 1), choose_add (l + (2 * n' + 1)) i',
    choose_add (l + (2 * n' + 1) + i' + 1) i',
    show l + (2 * n' + 1) + i' + 1 + i' = l + (2 * n' + 1) + i' + (i' + 1) by ring,
    Nat.factorial_succ i', Nat.factorial_succ (l + (2 * n' + 1) + i')]
  have h1 : ((n' + (i' + 1)).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (n'.factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((l + n' + (i' + 1)).factorial : ℚ) ≠ 0 := by positivity
  have h4 : ((l + n').factorial : ℚ) ≠ 0 := by positivity
  have h5 : (i'.factorial : ℚ) ≠ 0 := by positivity
  have h6 : ((l + (2 * n' + 1) + i').factorial : ℚ) ≠ 0 := by positivity
  have h7 : ((l + (2 * n' + 1)).factorial : ℚ) ≠ 0 := by positivity
  have h8 : ((l + (2 * n' + 1) + i' + (i' + 1)).factorial : ℚ) ≠ 0 := by positivity
  have h9 : ((-1 : ℚ) ^ i') ≠ 0 := pow_ne_zero _ (by norm_num)
  have h10 : ((i' : ℚ) + 1) ≠ 0 := by positivity
  have h11 : ((l : ℚ) + (2 * n' + 1) + i' + 1) ≠ 0 := by positivity
  push_cast
  first | (field_simp; done) | (field_simp; ring)

theorem cls_zero (x : Node) : cls x 0 0 = 0 := by unfold cls; split_ifs <;> rfl

theorem cls_ind (x y : Node) :
    cls y (if x.2 % 2 = 0 then 1 else 0) (if x.2 % 2 = 0 then 0 else 1) =
      if y.2 % 2 = x.2 % 2 then 1 else 0 := by
  unfold cls; split_ifs <;> first | rfl | (exfalso; omega)

section Cases

variable (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
include hK hH

/-- The constant term and the class coefficients of (8.2). -/
theorem coef_ids {a μ : Node} (haμ : a.2 < μ.2) (m : ℕ) (hj : m + 1 < μ.2 - a.2) :
    (fVal a μ (m + 1) * nodePos μ - fVal a μ m * nodePos a +
      ∑ ε : Bool, kap a (ε, a.2 + (μ.2 - a.2 - (m + 1))) μ *
        fVal (ε, a.2 + (μ.2 - a.2 - (m + 1))) μ m * nodePos (ε, a.2 + (μ.2 - a.2 - (m + 1))) = 0) ∧
    ∀ x : Node, fVal a μ (m + 1) * (if μ.2 % 2 = x.2 % 2 then 1 else 0) -
      fVal a μ m * (if a.2 % 2 = x.2 % 2 then 1 else 0) +
      ∑ ε : Bool, kap a (ε, a.2 + (μ.2 - a.2 - (m + 1))) μ *
        fVal (ε, a.2 + (μ.2 - a.2 - (m + 1))) μ m *
          (if (ε, a.2 + (μ.2 - a.2 - (m + 1))).2 % 2 = x.2 % 2 then 1 else 0) = 0 := by
  have E0 := Ecoef_zero hK hH haμ m hj 0 0
  unfold Ecoef at E0
  simp only [cls_zero, zero_add] at E0
  refine ⟨E0, fun x => ?_⟩
  have Ex := Ecoef_zero hK hH haμ m hj (if x.2 % 2 = 0 then 1 else 0) (if x.2 % 2 = 0 then 0 else 1)
  unfold Ecoef at Ex
  simp only [cls_ind] at Ex
  rw [Fintype.sum_bool] at Ex E0 ⊢
  linear_combination Ex - E0

/-- `D` odd, `j` odd: `f_j = 0`. -/
theorem caseA {a μ : Node} (haμ : a.2 < μ.2) (m : ℕ) (hj : m + 1 < μ.2 - a.2)
    (hD : (μ.2 - a.2) % 2 = 1) (hjo : (m + 1) % 2 = 1) : fVal a μ (m + 1) = 0 := by
  obtain ⟨-, Hc⟩ := coef_ids hK hH haμ m hj
  have H := Hc μ
  rw [Fintype.sum_bool] at H
  try dsimp only at H
  have c1 : ¬ (a.2 % 2 = μ.2 % 2) := by omega
  have c2 : ¬ ((a.2 + (μ.2 - a.2 - (m + 1))) % 2 = μ.2 % 2) := by omega
  simp only [c1, c2, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one, mul_zero,
    sub_zero, add_zero] at H
  exact H

/-- `D` even, `j` even: `f_j = f_{j+1}`. -/
theorem caseD_link {a μ : Node} (haμ : a.2 < μ.2) (m : ℕ) (hj : m + 2 < μ.2 - a.2)
    (hD : (μ.2 - a.2) % 2 = 0) (hje : (m + 1) % 2 = 0) : fVal a μ (m + 1) = fVal a μ (m + 2) := by
  obtain ⟨-, Hc⟩ := coef_ids hK hH haμ (m + 1) (by omega)
  have H := Hc a
  rw [Fintype.sum_bool] at H
  try dsimp only at H
  have c1 : μ.2 % 2 = a.2 % 2 := by omega
  have c2 : ¬ ((a.2 + (μ.2 - a.2 - (m + 1 + 1))) % 2 = a.2 % 2) := by omega
  simp only [c1, c2, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one, mul_zero,
    add_zero] at H
  linarith

/-- `D = 2n+2`, `j = 2i+1`. -/
theorem caseB {a μ : Node} (n' i : ℕ) (hD : μ.2 - a.2 = 2 * n' + 2 * i + 2)
    (hIH : ∀ ε : Bool, fVal (ε, a.2 + (2 * n' + 1)) μ (2 * i) =
      fDiag (a.2 + (2 * n' + 1)) (2 * i + 1) (2 * i)) :
    fVal a μ (2 * i + 1) = fDiag a.2 (2 * n' + 2 * i + 2) (2 * i + 1) := by
  have haμ : a.2 < μ.2 := by omega
  have hj : 2 * i + 1 < μ.2 - a.2 := by omega
  have hk : μ.2 - a.2 - (2 * i + 1) = 2 * n' + 1 := by omega
  obtain ⟨H0, Hc⟩ := coef_ids hK hH haμ (2 * i) hj
  have Ha := Hc a
  rw [hk] at H0 Ha
  simp only [Fintype.sum_bool, kap] at H0 Ha
  try dsimp only at H0 Ha
  have hodd : (a.2 + (2 * n' + 1) - a.2) % 2 = 1 := by omega
  have c1 : μ.2 % 2 = a.2 % 2 := by omega
  have c2 : ¬ ((a.2 + (2 * n' + 1)) % 2 = a.2 % 2) := by omega
  simp only [hodd, c1, c2, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one, mul_zero,
    add_zero] at H0 Ha
  rw [hIH true, hIH false] at H0
  have hks := kappa_sum_even (a := a) (μ := μ) (L := a.2 + (2 * n' + 1)) (by omega) (by omega)
    (by omega) (by omega)
  rw [Fintype.sum_bool] at hks
  have hP : nodePos μ - nodePos a ≠ 0 := sub_ne_zero.2 (nodePos_ne haμ)
  have key : fVal a μ (2 * i + 1) = fDiag (a.2 + (2 * n' + 1)) (2 * i + 1) (2 * i) *
      (∏ m ∈ TA (a.2 + (2 * n' + 1)) μ.2, (nodePos a ^ 2 - (m : ℚ) ^ 2 / 4)) /
      (∏ m ∈ TB (a.2 + (2 * n' + 1)) μ.2,
        (((a.2 + (2 * n' + 1) : ℕ) : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4)) := by
    have e : (fVal a μ (2 * i + 1) - fDiag (a.2 + (2 * n' + 1)) (2 * i + 1) (2 * i) *
        (∏ m ∈ TA (a.2 + (2 * n' + 1)) μ.2, (nodePos a ^ 2 - (m : ℚ) ^ 2 / 4)) /
        (∏ m ∈ TB (a.2 + (2 * n' + 1)) μ.2,
          (((a.2 + (2 * n' + 1) : ℕ) : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4))) *
        (nodePos μ - nodePos a) = 0 := by
      linear_combination H0 - fDiag (a.2 + (2 * n' + 1)) (2 * i + 1) (2 * i) * hks -
        nodePos a * Ha
    have := (mul_eq_zero.1 e).resolve_right hP
    linarith
  rw [key, pos_sq, numP_closed a.2 n' i μ.2 (by omega), Q_closed _ i μ.2 (by omega)]
  exact (F2_identity a.2 n' i).symm

/-- `D = 2n+1`, `j = 2i` (`i = i' + 1`). -/
theorem caseC {a μ : Node} (n' i' : ℕ) (hD : μ.2 - a.2 = 2 * n' + 2 * i' + 3)
    (hIH : ∀ ε : Bool, fVal (ε, a.2 + (2 * n' + 1)) μ (2 * i' + 1) =
      fDiag (a.2 + (2 * n' + 1)) (2 * i' + 1 + 1) (2 * i' + 1)) :
    fVal a μ (2 * i' + 1 + 1) = fDiag a.2 (2 * n' + 2 * i' + 3) (2 * i' + 1 + 1) := by
  have haμ : a.2 < μ.2 := by omega
  have hj : 2 * i' + 1 + 1 < μ.2 - a.2 := by omega
  have hk : μ.2 - a.2 - (2 * i' + 1 + 1) = 2 * n' + 1 := by omega
  obtain ⟨-, Hc⟩ := coef_ids hK hH haμ (2 * i' + 1) hj
  have Hμ := Hc μ
  rw [hk] at Hμ
  simp only [Fintype.sum_bool, kap] at Hμ
  try dsimp only at Hμ
  have hodd : (a.2 + (2 * n' + 1) - a.2) % 2 = 1 := by omega
  have c1 : ¬ (a.2 % 2 = μ.2 % 2) := by omega
  have c2 : (a.2 + (2 * n' + 1)) % 2 = μ.2 % 2 := by omega
  simp only [hodd, c1, c2, eq_self_iff_true, if_true, if_false, ↓reduceIte, mul_one, mul_zero,
    sub_zero] at Hμ
  rw [hIH true, hIH false] at Hμ
  have hks := kappa_sum_odd (a := a) (μ := μ) (L := a.2 + (2 * n' + 1)) (by omega) (by omega)
    (by omega) (by omega)
  rw [Fintype.sum_bool] at hks
  have key : fVal a μ (2 * i' + 1 + 1) = fDiag (a.2 + (2 * n' + 1)) (2 * i' + 1 + 1) (2 * i' + 1) *
      (∏ m ∈ TA (a.2 + (2 * n' + 1)) μ.2, (nodePos a ^ 2 - (m : ℚ) ^ 2 / 4)) /
      ((∏ m ∈ TB (a.2 + (2 * n' + 1)) μ.2,
        (((a.2 + (2 * n' + 1) : ℕ) : ℚ) ^ 2 / 4 - (m : ℚ) ^ 2 / 4)) *
        (nodePos μ ^ 2 - ((a.2 + (2 * n' + 1) : ℕ) : ℚ) ^ 2 / 4)) := by
    linear_combination Hμ - fDiag (a.2 + (2 * n' + 1)) (2 * i' + 1 + 1) (2 * i' + 1) * hks
  have hPi : nodePos μ ^ 2 - ((a.2 + (2 * n' + 1) : ℕ) : ℚ) ^ 2 / 4 =
      ((i' : ℚ) + 1) * (((a.2 + (2 * n' + 1) + i' : ℕ) : ℚ) + 1) := by
    rw [pos_sq, show μ.2 = a.2 + (2 * n' + 1) + (2 * i' + 2) by omega]
    push_cast
    ring
  rw [key, hPi, pos_sq, numP_closed a.2 n' (i' + 1) μ.2 (by omega), Q_closed _ i' μ.2 (by omega)]
  exact (F1_identity a.2 n' i').symm

/-- `f_j(a,μ)` is the closed form `fDiag (L_a) D j`. -/
theorem fVal_eq : ∀ D : ℕ, ∀ a μ : Node, μ.2 - a.2 = D → a.2 < μ.2 → ∀ j < D,
    fVal a μ j = fDiag a.2 D j := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro a μ hD haμ j hj
  have IHν : ∀ (m : ℕ) (ε : Bool), m + 1 < D →
      fVal (ε, a.2 + (D - (m + 1))) μ m = fDiag (a.2 + (D - (m + 1))) (m + 1) m := by
    intro m ε hm
    exact ih (m + 1) hm (ε, a.2 + (D - (m + 1))) μ
      (by show μ.2 - (a.2 + (D - (m + 1))) = m + 1; omega)
      (by show a.2 + (D - (m + 1)) < μ.2; omega) m (by omega)
  have hB : ∀ m : ℕ, D % 2 = 0 → m % 2 = 0 → m + 1 < D →
      fVal a μ (m + 1) = fDiag a.2 D (m + 1) := by
    intro m hDe hme hm
    obtain ⟨i, rfl⟩ : ∃ i, m = 2 * i := ⟨m / 2, by omega⟩
    obtain ⟨n', hn'⟩ : ∃ n', D = 2 * n' + 2 * i + 2 := ⟨(D - 2 * i - 2) / 2, by omega⟩
    rw [hn']
    refine caseB hK hH n' i (by omega) (fun ε => ?_)
    have := IHν (2 * i) ε (by omega)
    rwa [show D - (2 * i + 1) = 2 * n' + 1 by omega] at this
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp [fVal, fDiag]
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  rcases Nat.even_or_odd D with ⟨n, hn⟩ | ⟨n, hn⟩
  · rcases Nat.even_or_odd m with ⟨q, hq⟩ | ⟨q, hq⟩
    · exact hB m (by omega) (by omega) (by omega)
    · have hlink := caseD_link hK hH haμ m (by omega) (by omega) (by omega)
      rw [hlink, hB (m + 1) (by omega) (by omega) (by omega)]
      unfold fDiag
      rw [if_neg (by omega), if_neg (by omega), show (m + 1 + 1) / 2 = (m + 1) / 2 by omega]
  · rcases Nat.even_or_odd m with ⟨q, hq⟩ | ⟨q, hq⟩
    · rw [caseA hK hH haμ m (by omega) (by omega) (by omega)]
      unfold fDiag
      rw [if_pos (by omega)]
    · obtain ⟨i', rfl⟩ : ∃ i', m = 2 * i' + 1 := ⟨q, by omega⟩
      obtain ⟨n', hn'⟩ : ∃ n', D = 2 * n' + 2 * i' + 3 := ⟨(D - 2 * i' - 3) / 2, by omega⟩
      rw [hn']
      refine caseC hK hH n' i' (by omega) (fun ε => ?_)
      have := IHν (2 * i' + 1) ε (by omega)
      rwa [show D - (2 * i' + 1 + 1) = 2 * n' + 1 by omega] at this

end Cases

/-- `(-c)_i = (-1)^i c!/(c-i)!`. -/
theorem prod_neg_shift (c i : ℕ) (h : i ≤ c) :
    ∏ m ∈ Finset.range i, (-(c : ℚ) + m) = (-1) ^ i * (c.factorial : ℚ) / (c - i).factorial := by
  induction i with
  | zero => simp [div_self (show (c.factorial : ℚ) ≠ 0 by positivity)]
  | succ i ih =>
    rw [Finset.prod_range_succ, ih (by omega), show c - i = (c - (i + 1)) + 1 by omega,
      Nat.factorial_succ]
    have h1 : ((c - (i + 1)).factorial : ℚ) ≠ 0 := by positivity
    have h2 : (c : ℚ) - i ≠ 0 := by
      have : (i : ℚ) < c := by exact_mod_cast (show i < c by omega)
      linarith
    have hu : ((c : ℚ) - i) * ((c : ℚ) - i)⁻¹ = 1 := mul_inv_cancel₀ h2
    push_cast [Nat.cast_sub (show i + 1 ≤ c from h)]
    field_simp
    linear_combination (-(-1 : ℚ) ^ i) * hu

/-- `∑_i f_{2i}(l,D) xⁱ = ₂F₁(-n, -n-l; 1-D-l; x)`, `n = ⌊(D-1)/2⌋`. -/
theorem diag_hyp (l D : ℕ) (hD : 1 ≤ D) :
    ∑ i ∈ Finset.range ((D - 1) / 2 + 1), Polynomial.C (fDiag l D (2 * i)) * Polynomial.X ^ i =
      hyp2F1Poly (-(((D - 1) / 2 : ℕ) : ℚ)) (-(((D - 1) / 2 : ℕ) : ℚ) - l) (1 - (D : ℚ) - l)
        ((D - 1) / 2) := by
  unfold hyp2F1Poly
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ (D - 1) / 2 := by have := Finset.mem_range.1 hi; omega
  congr 2
  rw [fDiag_eval l D (2 * i) (by omega), show 2 * i / 2 = i by omega,
    show (-(((D - 1) / 2 : ℕ) : ℚ) - l) = -((((D - 1) / 2 + l) : ℕ) : ℚ) by push_cast; ring,
    show (1 - (D : ℚ) - l) = -(((D + l - 1) : ℕ) : ℚ) by push_cast [Nat.cast_sub (show 1 ≤ D + l by omega)]; ring,
    prod_neg_shift _ i hi', prod_neg_shift _ i (by omega), prod_neg_shift _ i (by omega),
    show l + (D - 1) / 2 = (D - 1) / 2 + l by ring, show l + D - 1 = D + l - 1 by omega,
    Nat.cast_choose ℚ hi', Nat.cast_choose ℚ (show i ≤ (D - 1) / 2 + l by omega),
    Nat.cast_choose ℚ (show i ≤ D + l - 1 by omega)]
  have h1 : ((((D - 1) / 2) - i).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (((D - 1) / 2 + l - i).factorial : ℚ) ≠ 0 := by positivity
  have h3 : ((D + l - 1 - i).factorial : ℚ) ≠ 0 := by positivity
  have h4 : (((D + l - 1)).factorial : ℚ) ≠ 0 := by positivity
  have h5 : ((i).factorial : ℚ) ≠ 0 := by positivity
  have h6 : ((((D - 1) / 2)).factorial : ℚ) ≠ 0 := by positivity
  have h7 : ((((D - 1) / 2 + l)).factorial : ℚ) ≠ 0 := by positivity
  have h8 : ((-1 : ℚ) ^ i) ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

/-- Theorem 8.8 (`thm:diagonal`), from the two cited results (through Lemma 8.7 and
Proposition 8.6).

Paper label: thm:diagonal -/
theorem thm_diagonal_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_thm_diagonal := by
  refine ⟨fun p p' r s b hset a μ haμ j hj => ?_, fun l D hD => diag_hyp l D hD⟩
  rw [chain_val hK hH hset haμ j hj, cv, fVal_eq hK hH (μ.2 - a.2) a μ rfl haμ j hj]

end Virasoro
