import Virasoro.Sphere.Proofs.Sec3BergmanSupport
import Virasoro.Sphere.Proofs.Sec3BergmanBound

/-!
# Sphere paper Lemma 3.5: polynomial bounds on the blocks (`sphere/paper.tex` l.845–847, l.878–880)

At each order `z^j` the entries of `K₁₂`, `K₂₁` and of the blocks `A₊₊`, `A₋₋`, `A₋₊`, `A₊₋` are
bounded by `C_j ((m+1)(n+1))^{d_j}`: this holds for `B` by `|B_{m,n}| ≤ 2n(n+1)` and is preserved
by the products and Neumann series, whose sums at order `z^j` have at most `m + n + j + 1` terms.
The paper uses the Cauchy bound `|B_{m,n}| ≤ C_ρ ρ^{-m-n}` in the same role.

Consumer: `summable_WnoTerm` (normal convergence of `[z^j] W_no`).
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- The weight `(m+1)(n+1)`. -/
def wt (m n : ℕ) : ℚ := ((m : ℚ) + 1) * ((n : ℚ) + 1)

theorem one_le_wt (m n : ℕ) : 1 ≤ wt m n := by
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  exact one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)

theorem wt_nonneg (m n : ℕ) : 0 ≤ wt m n := le_trans zero_le_one (one_le_wt m n)

theorem wt_pow_le {m n d e : ℕ} (h : d ≤ e) : wt m n ^ d ≤ wt m n ^ e :=
  pow_le_pow_right₀ (one_le_wt m n) h

/-- Entries with polynomially bounded coefficients at each order in `z`. -/
def PolyBdd (A : IMat) : Prop :=
  ∀ j : ℕ, ∃ (C : ℚ) (d : ℕ), 0 ≤ C ∧ ∀ m n, |coeff j (A m n)| ≤ C * wt m n ^ d

theorem bdd_add {C1 C2 w a b : ℚ} {d1 d2 : ℕ} (hw : 1 ≤ w) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (ha : |a| ≤ C1 * w ^ d1) (hb : |b| ≤ C2 * w ^ d2) :
    |a + b| ≤ (C1 + C2) * w ^ (d1 + d2) := by
  have h1 : w ^ d1 ≤ w ^ (d1 + d2) := pow_le_pow_right₀ hw (by omega)
  have h2 : w ^ d2 ≤ w ^ (d1 + d2) := pow_le_pow_right₀ hw (by omega)
  calc |a + b| ≤ |a| + |b| := abs_add_le a b
    _ ≤ C1 * w ^ d1 + C2 * w ^ d2 := add_le_add ha hb
    _ ≤ C1 * w ^ (d1 + d2) + C2 * w ^ (d1 + d2) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC1) (mul_le_mul_of_nonneg_left h2 hC2)
    _ = (C1 + C2) * w ^ (d1 + d2) := by ring

theorem PolyBdd.uniform {A : IMat} (h : PolyBdd A) (j : ℕ) :
    ∃ (C : ℚ) (d : ℕ), 0 ≤ C ∧ ∀ a ≤ j, ∀ m n, |coeff a (A m n)| ≤ C * wt m n ^ d := by
  induction j with
  | zero =>
    obtain ⟨C, d, hC, hb⟩ := h 0
    exact ⟨C, d, hC, fun a ha m n => by
      obtain rfl : a = 0 := by omega
      exact hb m n⟩
  | succ j ih =>
    obtain ⟨C1, d1, hC1, hb1⟩ := ih
    obtain ⟨C2, d2, hC2, hb2⟩ := h (j + 1)
    refine ⟨C1 + C2, d1 + d2, by positivity, fun a ha m n => ?_⟩
    rcases Nat.lt_or_ge a (j + 1) with h1 | h1
    · have := bdd_add (one_le_wt m n) hC1 hC2 (hb1 a (by omega) m n)
        (show |(0 : ℚ)| ≤ C2 * wt m n ^ d2 by
          rw [abs_zero]; exact mul_nonneg hC2 (pow_nonneg (wt_nonneg m n) _))
      rwa [add_zero] at this
    · obtain rfl : a = j + 1 := by omega
      have := bdd_add (one_le_wt m n) hC1 hC2
        (show |(0 : ℚ)| ≤ C1 * wt m n ^ d1 by
          rw [abs_zero]; exact mul_nonneg hC1 (pow_nonneg (wt_nonneg m n) _)) (hb2 m n)
      rwa [zero_add] at this

theorem PolyBdd.neg {A : IMat} (h : PolyBdd A) : PolyBdd fun m n => -A m n := by
  intro j
  obtain ⟨C, d, hC, hb⟩ := h j
  exact ⟨C, d, hC, fun m n => by rw [map_neg, abs_neg]; exact hb m n⟩

theorem PolyBdd.imul {A B : IMat} (hA : PolyBdd A) (hB : PolyBdd B) : PolyBdd (imul A B) := by
  intro j
  obtain ⟨CA, dA, hCA, hbA⟩ := hA.uniform j
  obtain ⟨CB, dB, hCB, hbB⟩ := hB.uniform j
  set d := dA + dB with hd
  refine ⟨CA * CB * ((j : ℚ) + 1) ^ (2 * d + 2), 3 * d + 1, by positivity, fun m n => ?_⟩
  have hw := one_le_wt m n
  have hwd : 0 ≤ wt m n ^ d := pow_nonneg (wt_nonneg m n) _
  set N : ℚ := ((m + n + j + 1 : ℕ) : ℚ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hterm : ∀ k ∈ range (m + n + j + 1), |coeff j (A m k * B k n)| ≤
      ((j : ℚ) + 1) * (CA * CB * wt m n ^ d * N ^ (2 * d)) := by
    intro k hk
    rw [coeff_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ (CA * CB * wt m n ^ d * N ^ (2 * d))
      fun p hp => ?_).trans ?_
    · have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      rw [abs_mul]
      have e1 : |coeff p.1 (A m k)| ≤ CA * wt m k ^ d :=
        (hbA p.1 (by omega) m k).trans (mul_le_mul_of_nonneg_left (wt_pow_le (by omega)) hCA)
      have e2 : |coeff p.2 (B k n)| ≤ CB * wt k n ^ d :=
        (hbB p.2 (by omega) k n).trans (mul_le_mul_of_nonneg_left (wt_pow_le (by omega)) hCB)
      have e3 : wt m k ^ d * wt k n ^ d = wt m n ^ d * ((k : ℚ) + 1) ^ (2 * d) := by
        rw [← mul_pow, pow_mul, ← mul_pow]
        congr 1
        unfold wt
        ring
      have hk1 : (k : ℚ) + 1 ≤ N := by
        have := Finset.mem_range.1 hk
        rw [hN]
        exact_mod_cast this
      have e4 : ((k : ℚ) + 1) ^ (2 * d) ≤ N ^ (2 * d) :=
        pow_le_pow_left₀ (by positivity) hk1 _
      calc |coeff p.1 (A m k)| * |coeff p.2 (B k n)|
          ≤ (CA * wt m k ^ d) * (CB * wt k n ^ d) :=
            mul_le_mul e1 e2 (abs_nonneg _) (mul_nonneg hCA (pow_nonneg (wt_nonneg m k) _))
        _ = (CA * CB * wt m n ^ d) * ((k : ℚ) + 1) ^ (2 * d) := by
            rw [mul_mul_mul_comm, e3]; ring
        _ ≤ (CA * CB * wt m n ^ d) * N ^ (2 * d) :=
            mul_le_mul_of_nonneg_left e4 (mul_nonneg (mul_nonneg hCA hCB) hwd)
    · rw [Finset.Nat.card_antidiagonal, nsmul_eq_mul]
      push_cast
      exact le_rfl
  rw [Virasoro.Sphere.imul, coeff_mk]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_)
  rw [Finset.card_range, nsmul_eq_mul, ← hN]
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hj : (0 : ℚ) ≤ j := Nat.cast_nonneg j
  have hNle : N ≤ ((j : ℚ) + 1) * wt m n := by
    rw [hN]
    unfold wt
    push_cast
    nlinarith [mul_nonneg hj (mul_nonneg hm hn), mul_nonneg hj hm, mul_nonneg hj hn,
      mul_nonneg hm hn]
  have hpow : N ^ (2 * d + 1) ≤ (((j : ℚ) + 1) * wt m n) ^ (2 * d + 1) :=
    pow_le_pow_left₀ hN0 hNle _
  calc N * (((j : ℚ) + 1) * (CA * CB * wt m n ^ d * N ^ (2 * d)))
      = (CA * CB * ((j : ℚ) + 1) * wt m n ^ d) * N ^ (2 * d + 1) := by ring
    _ ≤ (CA * CB * ((j : ℚ) + 1) * wt m n ^ d) * (((j : ℚ) + 1) * wt m n) ^ (2 * d + 1) :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (mul_nonneg (mul_nonneg hCA hCB) (by linarith)) hwd)
    _ = CA * CB * ((j : ℚ) + 1) ^ (2 * d + 2) * wt m n ^ (3 * d + 1) := by
        rw [mul_pow]; ring

theorem PolyBdd.rangeSum {F : ℕ → IMat} (hF : ∀ r, PolyBdd (F r)) :
    PolyBdd (fun m n => PowerSeries.mk fun j => ∑ r ∈ range (j + 1), coeff j (F r m n)) := by
  intro j
  have key : ∀ s : ℕ, ∃ (C : ℚ) (d : ℕ), 0 ≤ C ∧
      ∀ m n, |∑ r ∈ range s, coeff j (F r m n)| ≤ C * wt m n ^ d := by
    intro s
    induction s with
    | zero => exact ⟨0, 0, le_rfl, fun m n => by simp⟩
    | succ s ih =>
      obtain ⟨C1, d1, hC1, hb1⟩ := ih
      obtain ⟨C2, d2, hC2, hb2⟩ := hF s j
      refine ⟨C1 + C2, d1 + d2, by positivity, fun m n => ?_⟩
      rw [Finset.sum_range_succ]
      exact bdd_add (one_le_wt m n) hC1 hC2 (hb1 m n) (hb2 m n)
  obtain ⟨C, d, hC, hb⟩ := key (j + 1)
  exact ⟨C, d, hC, fun m n => by rw [coeff_mk]; exact hb m n⟩

theorem PolyBdd.ione : PolyBdd ione := by
  intro j
  refine ⟨1, 0, zero_le_one, fun m n => ?_⟩
  rw [Virasoro.Sphere.ione, pow_zero, mul_one]
  split_ifs
  · rw [PowerSeries.coeff_one]
    split_ifs <;> simp
  · simp

theorem PolyBdd.ipow {A : IMat} (hA : PolyBdd A) (r : ℕ) : PolyBdd (ipow A r) := by
  induction r with
  | zero => exact PolyBdd.ione
  | succ r ih => exact ih.imul hA

theorem PolyBdd.ineumann {A : IMat} (hA : PolyBdd A) : PolyBdd (ineumann A) :=
  PolyBdd.rangeSum fun r => hA.ipow r

theorem Bcoef_le_wt (m n : ℕ) : |Bcoef m n| ≤ 2 * wt m n ^ 2 := by
  have h := Bcoef_abs_le m n
  have hm : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have h1 : (n : ℚ) * ((n : ℚ) + 1) ≤ wt m n ^ 2 := by
    unfold wt
    nlinarith [mul_nonneg hm hn, mul_nonneg hm hm, mul_nonneg hn hn,
      mul_nonneg (mul_nonneg hm hn) hn, mul_nonneg (mul_nonneg hm hm) hn,
      mul_nonneg (mul_nonneg hm hm) (mul_nonneg hn hn)]
  linarith

theorem Bcoef_div_le_wt (m n : ℕ) : |Bcoef m n / (m : ℚ)| ≤ 2 * wt m n ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.cast_zero, div_zero, abs_zero]
    positivity
  · rw [abs_div]
    refine (div_le_self (abs_nonneg _) ?_).trans (Bcoef_le_wt m n)
    rw [Nat.abs_cast]
    exact_mod_cast hm

theorem PolyBdd.of_monomial (c : ℕ → ℕ → ℚ) (e : ℕ → ℕ → ℕ)
    (h : ∀ m n, |c m n| ≤ 2 * wt m n ^ 2) :
    PolyBdd fun m n => C (c m n) * X ^ (e m n) := by
  intro j
  refine ⟨2, 2, by norm_num, fun m n => ?_⟩
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs
  · rw [mul_one]
    exact h m n
  · rw [mul_zero, abs_zero]
    exact mul_nonneg (by norm_num) (pow_nonneg (wt_nonneg m n) _)

theorem PolyBdd.Bzinf : PolyBdd Bzinf := PolyBdd.of_monomial _ _ Bcoef_le_wt

theorem PolyBdd.M1inf : PolyBdd M1inf := PolyBdd.of_monomial _ _ Bcoef_div_le_wt

theorem PolyBdd.Binf : PolyBdd Binf := by
  have e : Virasoro.Sphere.Binf = fun m n => C (Bcoef m n) * X ^ 0 := by
    funext m n
    rw [Virasoro.Sphere.Binf, pow_zero, mul_one]
  rw [e]
  exact PolyBdd.of_monomial _ (fun _ _ => 0) Bcoef_le_wt

theorem PolyBdd.M2inf : PolyBdd M2inf := by
  have e : Virasoro.Sphere.M2inf = fun m n => C (Bcoef m n / (m : ℚ)) * X ^ 0 := by
    funext m n
    rw [Virasoro.Sphere.M2inf, pow_zero, mul_one]
  rw [e]
  exact PolyBdd.of_monomial _ (fun _ _ => 0) Bcoef_div_le_wt

theorem PolyBdd.K12 : PolyBdd K12 := (PolyBdd.M1inf.imul PolyBdd.M2inf).ineumann

theorem PolyBdd.K21 : PolyBdd K21 := (PolyBdd.M2inf.imul PolyBdd.M1inf).ineumann

theorem PolyBdd.App : PolyBdd App := (PolyBdd.Bzinf.imul PolyBdd.K21).neg

theorem PolyBdd.Amm : PolyBdd Amm := (PolyBdd.Binf.imul PolyBdd.K12).neg

theorem PolyBdd.Amp : PolyBdd Amp := (PolyBdd.Binf.imul PolyBdd.K12).imul PolyBdd.M1inf

theorem PolyBdd.Apm : PolyBdd Apm := (PolyBdd.Bzinf.imul PolyBdd.K21).imul PolyBdd.M2inf

end Virasoro.Sphere
