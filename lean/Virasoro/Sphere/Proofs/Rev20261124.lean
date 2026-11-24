import Virasoro.Sphere.Statements.Rev20261124
import Virasoro.Sphere.Proofs.Sec3Headline
import Virasoro.Sphere.Proofs.Sec5PiFactorization

/-!
# Proofs of the statements of `sphere/paper.tex` added or restated after 70bac53

- Lemma 3.3 and Proposition 3.4 in their current form are clauses of the 70bac53 form of
  Lemma 3.3 (`Stmt_lem_lambda_expansion`).
- Lemma 5.2(iii): every factor of `P_{R,S}(b⋆,Δ_a,Δ_b)` is, in the momentum coordinates, a
  product of linear forms in `x_a + x_b` and `x_a - x_b` (`fus_factor`, `fus_pref`), so a factor
  that vanishes at a point vanishes on the whole line through it (`fusP_zero_line`).  The rest of
  the argument is the paper's: `R^±_k p' + S^±_k p = m^±_k`, and for even `k` the factor
  `P_{r,s}` has its zeros on lines with `|e| ≤ n₁ - p' - p ≤ m^±_k - p' - p`.
-/

namespace Virasoro.Sphere

open Verma

/-- Lemma 3.3 in its current form, from the 70bac53 form. -/
theorem lem_lambda_expansion_paper_of (h : Stmt_lem_lambda_expansion) :
    Stmt_lem_lambda_expansion_paper := by
  obtain ⟨h1, S1t, S2c, S21, S22, hE, hi, hL, _⟩ := h
  exact ⟨h1, S1t, S2c, S21, S22, hE, hi, hL⟩

/-- Proposition 3.4, from the 70bac53 form of Lemma 3.3. -/
theorem prop_gaussian_limit_of (h : Stmt_lem_lambda_expansion) : Stmt_prop_gaussian_limit := by
  obtain ⟨_, S1t, S2c, S21, S22, hE, _, _, hrest⟩ := h
  exact ⟨S1t, S2c, S21, S22, hE, hrest⟩

/-- Lemma 3.3 (sphere), from the cited inputs of `lem_lambda_expansion_of_cited`.

Paper label: lem:lambda-expansion -/
theorem lem_lambda_expansion_paper_of_cited (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) :
    Stmt_lem_lambda_expansion_paper :=
  lem_lambda_expansion_paper_of (lem_lambda_expansion_of_cited hF hK hJ1 hJ2)

/-- Proposition 3.4 (sphere), from the same cited inputs.

Paper label: prop:gaussian-limit -/
theorem prop_gaussian_limit_of_cited (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2) :
    Stmt_prop_gaussian_limit :=
  prop_gaussian_limit_of (lem_lambda_expansion_of_cited hF hK hJ1 hJ2)

section

variable {p p' : ℕ} {b : ℂ}

theorem wtX_eq_wtOf (x : ℂ) : wtX p p' x = wtOf p p' x := rfl

/-- A zero of `P_{R,S}(b⋆)` lies on a line `x_a ± x_b = e`, `|e| ≤ (R-1)p' + (S-1)p`, on which
`P_{R,S}(b⋆)` vanishes identically. -/
theorem fusP_zero_line (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) {R S : ℕ}
    (hR : 0 < R) (hS : 0 < S) (aa ab : ℂ)
    (h0 : fusP R S b (wtOf p p' aa) (wtOf p p' ab) = 0) :
    ∃ e : ℤ, |e| ≤ (R : ℤ) * p' + S * p - p' - p ∧
      ZeroOnLine (fun ya yb => fusP R S b (wtOf p p' ya) (wtOf p p' yb)) e aa ab := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpp : ((p : ℂ) * p') ≠ 0 := mul_ne_zero hp0 hp'0
  have hbnd : (0 : ℤ) ≤ (R : ℤ) * p' + S * p - p' - p := by
    have h1 : (p' : ℤ) ≤ (R : ℤ) * p' := by nlinarith
    have h2 : (p : ℤ) ≤ (S : ℤ) * p := by nlinarith
    linarith
  simp only [fusP] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · split_ifs at h with hc
    · rw [fus_pref hp hp' hb, div_div, div_eq_zero_iff] at h
      rcases h with h | h
      · rcases mul_eq_zero.1 h with h | h
        · refine ⟨0, by simpa using hbnd, Or.inr ⟨by push_cast; linear_combination -h,
            fun ya yb hy => ?_⟩⟩
          simp only [fusP]
          rw [if_pos hc, fus_pref hp hp' hb]
          have e0 : yb - ya = 0 := by push_cast at hy; linear_combination -hy
          rw [e0]
          simp
        · refine ⟨0, by simpa using hbnd, Or.inl ⟨by push_cast; linear_combination h,
            fun ya yb hy => ?_⟩⟩
          simp only [fusP]
          rw [if_pos hc, fus_pref hp hp' hb]
          have e0 : yb + ya = 0 := by push_cast at hy; linear_combination hy
          rw [e0]
          simp
      · exact absurd h (mul_ne_zero hpp (by norm_num))
    · exact absurd h one_ne_zero
  · obtain ⟨x, hx, hx0⟩ := Finset.prod_eq_zero_iff.1 h
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.1 (Finset.mem_filter.1 hx).1
    obtain ⟨a1, a2⟩ := mem_stepRange_bound hx1
    obtain ⟨a3, a4⟩ := mem_stepRange_bound hx2
    have hn : |x.1 * (p' : ℤ) - x.2 * p| ≤ (R : ℤ) * p' + S * p - p' - p := by
      rw [abs_le]
      constructor <;> nlinarith
    have hn' : |-(x.1 * (p' : ℤ) - x.2 * p)| ≤ (R : ℤ) * p' + S * p - p' - p := by
      rwa [abs_neg]
    -- the factor of `x` vanishes at every point where one of its four linear forms vanishes
    have key : ∀ ya yb : ℂ,
        (yb - ya - ((x.1 : ℂ) * p' - x.2 * p) = 0 ∨ yb + ya + ((x.1 : ℂ) * p' - x.2 * p) = 0 ∨
          yb - ya + ((x.1 : ℂ) * p' - x.2 * p) = 0 ∨ yb + ya - ((x.1 : ℂ) * p' - x.2 * p) = 0) →
        fusP R S b (wtOf p p' ya) (wtOf p p' yb) = 0 := by
      intro ya yb hor
      simp only [fusP]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero hx
      rw [div_eq_zero_iff]
      left
      rw [fus_factor hp hp' hb]
      rcases hor with h' | h' | h' | h' <;> simp [h']
    rw [div_eq_zero_iff] at hx0
    rcases hx0 with hx0 | hx0
    swap
    · norm_num at hx0
    rw [fus_factor hp hp' hb, div_eq_zero_iff] at hx0
    rcases hx0 with hx0 | hx0
    swap
    · exact absurd hx0 (pow_ne_zero 2 hpp)
    rcases mul_eq_zero.1 hx0 with hx0 | h4
    · rcases mul_eq_zero.1 hx0 with hx0 | h3
      · rcases mul_eq_zero.1 hx0 with h1 | h2
        · refine ⟨_, hn', Or.inr ⟨by push_cast; linear_combination -h1, fun ya yb hy => ?_⟩⟩
          exact key ya yb (Or.inl (by push_cast at hy; linear_combination -hy))
        · refine ⟨_, hn', Or.inl ⟨by push_cast; linear_combination h2, fun ya yb hy => ?_⟩⟩
          exact key ya yb (Or.inr (Or.inl (by push_cast at hy; linear_combination hy)))
      · refine ⟨_, hn, Or.inr ⟨by push_cast; linear_combination -h3, fun ya yb hy => ?_⟩⟩
        exact key ya yb (Or.inr (Or.inr (Or.inl (by push_cast at hy; linear_combination -hy))))
    · refine ⟨_, hn, Or.inl ⟨by push_cast; linear_combination h4, fun ya yb hy => ?_⟩⟩
      exact key ya yb (Or.inr (Or.inr (Or.inr (by push_cast at hy; linear_combination hy))))

/-- If `π = Q · P_{R,S}(b⋆)` pointwise, the line property passes from `Q` and `P_{R,S}` to `π`. -/
theorem line_of_factor (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) {R S : ℕ}
    (hR : 0 < R) (hS : 0 < S) (M : ℤ) (hM : (R : ℤ) * p' + S * p - p' - p ≤ M)
    (πf Qf : ℂ → ℂ → ℂ)
    (hπ : ∀ ya yb, πf ya yb = Qf ya yb * fusP R S b (wtOf p p' ya) (wtOf p p' yb))
    (hQ : ∀ ya yb, Qf ya yb = 0 → ∃ e : ℤ, |e| ≤ M ∧ ZeroOnLine Qf e ya yb)
    (xa xb : ℂ) (h0 : πf xa xb = 0) : ∃ e : ℤ, |e| ≤ M ∧ ZeroOnLine πf e xa xb := by
  rw [hπ] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · obtain ⟨e, he, hl⟩ := hQ xa xb h
    refine ⟨e, he, ?_⟩
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun ya yb hy => by rw [hπ, h2 ya yb hy, zero_mul]⟩
    · exact Or.inr ⟨h1, fun ya yb hy => by rw [hπ, h2 ya yb hy, zero_mul]⟩
  · obtain ⟨e, he, hl⟩ := fusP_zero_line hp hp' hb hR hS xa xb h
    refine ⟨e, le_trans he hM, ?_⟩
    rcases hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, fun ya yb hy => by
        rw [hπ, show fusP R S b (wtOf p p' ya) (wtOf p p' yb) = 0 from h2 ya yb hy, mul_zero]⟩
    · exact Or.inr ⟨h1, fun ya yb hy => by
        rw [hπ, show fusP R S b (wtOf p p' ya) (wtOf p p' yb) = 0 from h2 ya yb hy, mul_zero]⟩

end

/-- Lemma 5.2 (sphere) in its current form, from the cited inputs of
`lem_pi_factorization_of_cited`.

Paper label: lem:pi-factorization -/
theorem lem_pi_factorization_paper_of_cited (hH : Cited_HJSNormalizations)
    (hF : Cited_SphereFusionPolynomial) (hU : Cited_SingularUnique) :
    Stmt_lem_pi_factorization_paper := by
  intro p p' r s b hset k ε hk x hx1 hx
  obtain ⟨hodd, heven, hiii⟩ := lem_pi_factorization_of_cited hH hF hU p p' r s b hset k ε hk x
    hx1 hx
  refine ⟨hodd, heven, fun xa xb => ?_⟩
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hp0 : 0 < p := by omega
  have hp'0 : 0 < p' := by omega
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
  have hp'z : (0 : ℤ) < p' := by exact_mod_cast hp'0
  -- the zero-line clause, by the paper's case split on the parity of `k` and the sign
  have hA : ∀ xa xb : ℂ,
      piScalar (kacH r s b) x (wtX p p' xa) (wtX p p' xb) = 0 →
      ∃ e : ℤ, |e| ≤ nOrb p p' r s ε k - p' - p ∧
        ZeroOnLine (fun ya yb => piScalar (kacH r s b) x (wtX p p' ya) (wtX p p' yb)) e xa xb := by
    intro xa xb h0
    have hpj : p ≤ (k / 2 + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
    have hpj' : p' ≤ (k / 2 + 1) * p' := Nat.le_mul_of_pos_left _ (by omega)
    rcases Nat.mod_two_eq_zero_or_one k with he | ho
    · have hkj : (k : ℤ) = 2 * ((k / 2 : ℕ) : ℤ) := by omega
      have hj : 1 ≤ k / 2 := by omega
      have h1 : r < k / 2 * p := by
        have : p ≤ k / 2 * p := Nat.le_mul_of_pos_left _ (by omega)
        omega
      have h2 : s < k / 2 * p' := by
        have : p' ≤ k / 2 * p' := Nat.le_mul_of_pos_left _ (by omega)
        omega
      have h1z : (r : ℤ) < ((k / 2 : ℕ) : ℤ) * p := by exact_mod_cast h1
      have h2z : (s : ℤ) < ((k / 2 : ℕ) : ℤ) * p' := by exact_mod_cast h2
      have hQ : ∀ (M : ℤ), (r : ℤ) * p' + s * p - p' - p ≤ M → ∀ ya yb : ℂ,
          fusP r s b (wtOf p p' ya) (wtOf p p' yb) = 0 →
          ∃ e : ℤ, |e| ≤ M ∧
            ZeroOnLine (fun ya yb => fusP r s b (wtOf p p' ya) (wtOf p p' yb)) e ya yb := by
        intro M hM ya yb hz
        obtain ⟨e, hle, hl⟩ := fusP_zero_line hp0 hp'0 hb hr hs ya yb hz
        exact ⟨e, le_trans hle hM, hl⟩
      cases ε with
      | true =>
        have e : nOrb p p' r s true k = (k : ℤ) * p * p' + ((p' : ℤ) * r - p * s) := by
          simp [nOrb, he]
        have q1 : (0 : ℤ) ≤ (((k / 2 : ℕ) : ℤ) * p' - s) * p :=
          mul_nonneg (by linarith) hpz.le
        refine line_of_factor hp0 hp'0 hb (R := r + k / 2 * p) (S := k / 2 * p' - s) (by omega)
          (by omega) _ ?_ _ (fun ya yb => fusP r s b (wtOf p p' ya) (wtOf p p' yb)) ?_
          (hQ _ ?_) xa xb h0
        · apply le_of_eq
          rw [e, hkj]
          push_cast [Nat.cast_sub h2.le]
          ring
        · intro ya yb
          show piScalar (kacH r s b) x (wtOf p p' ya) (wtOf p p' yb) = _
          rw [heven he, if_pos rfl]
        · rw [e, hkj]
          nlinarith [q1]
      | false =>
        have e : nOrb p p' r s false k = (k : ℤ) * p * p' - ((p' : ℤ) * r - p * s) := by
          simp [nOrb, he]
        have q1 : (0 : ℤ) ≤ (((k / 2 : ℕ) : ℤ) * p - r) * p' :=
          mul_nonneg (by linarith) hp'z.le
        refine line_of_factor hp0 hp'0 hb (R := k / 2 * p - r) (S := k / 2 * p' + s) (by omega)
          (by omega) _ ?_ _ (fun ya yb => fusP r s b (wtOf p p' ya) (wtOf p p' yb)) ?_
          (hQ _ ?_) xa xb h0
        · apply le_of_eq
          rw [e, hkj]
          push_cast [Nat.cast_sub h1.le]
          ring
        · intro ya yb
          show piScalar (kacH r s b) x (wtOf p p' ya) (wtOf p p' yb) = _
          rw [heven he, if_neg (by simp)]
        · rw [e, hkj]
          nlinarith [q1]
    · have hkj : (k : ℤ) = 2 * ((k / 2 : ℕ) : ℤ) + 1 := by omega
      cases ε with
      | true =>
        have e : nOrb p p' r s true k = ((k : ℤ) - 1) * p * p' + ((p' : ℤ) * r + p * s) := by
          simp [nOrb, ho]
        refine line_of_factor hp0 hp'0 hb (R := r + k / 2 * p) (S := s + k / 2 * p') (by omega)
          (by omega) _ ?_ _ (fun _ _ => 1) ?_ (fun _ _ h1 => absurd h1 one_ne_zero) xa xb h0
        · apply le_of_eq
          rw [e, hkj]
          push_cast
          ring
        · intro ya yb
          show piScalar (kacH r s b) x (wtOf p p' ya) (wtOf p p' yb) = _
          rw [hodd ho, if_pos rfl]
          simp
      | false =>
        have e : nOrb p p' r s false k = ((k : ℤ) + 1) * p * p' - ((p' : ℤ) * r + p * s) := by
          simp [nOrb, ho]
        refine line_of_factor hp0 hp'0 hb (R := (k / 2 + 1) * p - r)
          (S := (k / 2 + 1) * p' - s) (by omega) (by omega) _ ?_ _ (fun _ _ => 1) ?_
          (fun _ _ h1 => absurd h1 one_ne_zero) xa xb h0
        · apply le_of_eq
          rw [e, hkj]
          push_cast [Nat.cast_sub (show r ≤ (k / 2 + 1) * p by omega),
            Nat.cast_sub (show s ≤ (k / 2 + 1) * p' by omega)]
          ring
        · intro ya yb
          show piScalar (kacH r s b) x (wtOf p p' ya) (wtOf p p' yb) = _
          rw [hodd ho, if_neg (by simp)]
          simp
  have hB := hiii xa xb
  simp only at hB
  intro φ mm
  refine ⟨hA xa xb, hB.2, fun h1 h2 h0 => ?_, ?_⟩
  · obtain ⟨e, he, hl⟩ := hA xa xb h0
    have hen : ‖((e : ℤ) : ℂ)‖ ≤ (mm : ℝ) := by
      rw [Complex.norm_intCast]
      exact_mod_cast he
    rcases hl with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at h1
      linarith
    · rw [h] at h2
      linarith
  · show piScalar (kacH r s b) x (wtX p p' (-xa)) (wtX p p' (-xb)) =
      piScalar (kacH r s b) x (wtX p p' xa) (wtX p p' xb)
    simp only [wtX, neg_sq]

end Virasoro.Sphere
