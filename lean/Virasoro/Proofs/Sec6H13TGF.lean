import Virasoro.Proofs.Sec6H13TRho

/-!
# Proposition 6.8(ii): families that are good from a level on (paper.tex l.1374–1378)

`GF G W D V`: the family is good (`Good`) from the level `W` on.  The root-set argument of the
paper: a scalar polynomial vanishing on `[W₀, W)` times a family good from `W` is good from `W₀`;
a family good from `W₁` that vanishes on `[W₁, W₂)` times a family good from `W₂` is good from `W₁`.
-/

namespace Virasoro.H13T

open Virasoro.H13D Finset

/-- Good from the level `W` on. -/
def GF (G : ℕ → LL) (W : ℕ) (D V : ℤ) : Prop := Good (fun M => G (M + W)) D V

theorem GF.good {G : ℕ → LL} {D V : ℤ} (h : GF G 0 D V) : Good G D V := by
  simpa [GF] using h

theorem GF.mono {G : ℕ → LL} {W : ℕ} {D V D' V' : ℤ} (h : GF G W D V) (hD : D' ≤ D) (hV : V' ≤ V) :
    GF G W D' V' := Good.mono h hD hV

theorem GF.add {G G' : ℕ → LL} {W : ℕ} {D V : ℤ} (h : GF G W D V) (h' : GF G' W D V) :
    GF (fun M => G M + G' M) W D V := Good.add h h'

theorem GF.sum {ι : Type*} (S : Finset ι) {G : ι → ℕ → LL} {W : ℕ} {D V : ℤ}
    (h : ∀ a ∈ S, GF (G a) W D V) : GF (fun M => ∑ a ∈ S, G a M) W D V :=
  Good.sum S h

theorem GF.congr {G G' : ℕ → LL} {W : ℕ} {D V : ℤ} (h : GF G W D V)
    (hG : ∀ M, W ≤ M → G' M = G M) : GF G' W D V := by
  refine ⟨fun i j => (h.poly i j).congr fun M => ?_, fun M i j hij => ?_, ?_⟩
  · beta_reduce
    rw [hG (M + W) (by omega)]
  · beta_reduce
    rw [hG (M + W) (by omega)]
    exact h.val M i j hij
  · obtain ⟨b, hb⟩ := h.ord
    exact ⟨b, fun M n hn => by beta_reduce; rw [hG (M + W) (by omega)]; exact hb M n hn⟩

/-- Root sets: a scalar polynomial vanishing on `[W₀, W)` times a family good from `W` on. -/
theorem GF.pi_mul (π : Polynomial ℚ) {e : ℕ} (hπ : π.natDegree ≤ e) {W₀ W : ℕ} (hW : W₀ ≤ W)
    (hz : ∀ M : ℕ, W₀ ≤ M → M < W → π.eval (M : ℚ) = 0) {R : ℕ → LL} {D V : ℤ}
    (hR : GF R W D V) : GF (fun M => cL (π.eval (M : ℚ)) * R M) W₀ (D - e) V := by
  have h := good_pi_mul (π.comp (Polynomial.X + Polynomial.C (W₀ : ℚ))) (e := e)
    (Polynomial.natDegree_comp_le.trans (by
      rw [Polynomial.natDegree_X_add_C, mul_one]; exact hπ)) (W := W - W₀)
    (R := fun M => R (M + W₀))
    (fun M hM => by
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
      have := hz (M + W₀) (by omega) (by omega)
      push_cast at this
      exact this)
    (by
      have e1 : (fun M => R (M + (W - W₀) + W₀)) = fun M => R (M + W) := by
        funext M; congr 1; omega
      rw [e1]
      exact hR)
  refine ⟨fun i j => (h.poly i j).congr fun M => ?_, fun M i j hij => ?_, ?_⟩
  · beta_reduce
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    push_cast
    rfl
  · have := h.val M i j hij
    beta_reduce at this ⊢
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at this
    push_cast at this ⊢
    exact this
  · obtain ⟨b, hb⟩ := h.ord
    refine ⟨b, fun M n hn => ?_⟩
    have := hb M n hn
    beta_reduce at this ⊢
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at this
    push_cast at this ⊢
    exact this

/-- A family good from `W₁` that vanishes on `[W₁, W₂)` times a family good from `W₂`. -/
theorem GF.mul_vanish {G G' : ℕ → LL} {W₁ W₂ : ℕ} {D V D' V' : ℤ} (h : GF G W₁ D V)
    (h' : GF G' W₂ D' V') (hW : W₁ ≤ W₂) (hz : ∀ M : ℕ, W₁ ≤ M → M < W₂ → G M = 0) :
    GF (fun M => G M * G' M) W₁ (D + D') (V + V') := by
  obtain ⟨b, hb⟩ := h.ord
  obtain ⟨b', hb'⟩ := h'.ord
  set d := W₂ - W₁ with hd
  -- the coefficient formula with ranges independent of `M`, from the level `W₂` on
  have key : ∀ (M : ℕ) (i j : ℤ), d ≤ M → cfL (G (M + W₁) * G' (M + W₁)) i j =
      ∑ n ∈ Icc b (i - b'), ∑ m ∈ Icc ((V - 2 * n) / 2) (j - (V' - 2 * (i - n)) / 2),
        cfL (G (M + W₁)) n m * cfL (G' (M - d + W₂)) (i - n) (j - m) := by
    intro M i j hM
    have e1 : M + W₁ = M - d + W₂ := by omega
    rw [cfL, hahn_coeff_mul (hb M) (by rw [e1]; exact hb' (M - d)), AddMonoidAlgebra.coeff_sum,
      Finsupp.finsetSum_apply]
    refine sum_congr rfl fun n _ => ?_
    rw [lq_coeff_mul (h.lq_low M n) (by rw [e1]; exact h'.lq_low (M - d) (i - n))]
    rw [e1]
    rfl
  have hzero : ∀ (M : ℕ), M < d → G (M + W₁) = 0 := fun M hM => hz (M + W₁) (by omega) (by omega)
  refine ⟨fun i j => ?_, fun M i j hij => ?_, ⟨b + b', fun M n hn => ?_⟩⟩
  · -- the polynomial
    have hpoly : ∀ n m, ∃ f : Polynomial ℚ, (∀ k : ℕ, 2 * n + 2 * m - D < k → f.coeff k = 0) ∧
        ∀ M, cfL (G (M + W₁)) n m = f.eval (M : ℚ) := fun n m => h.poly n m
    have hpoly' : ∀ n m, ∃ f : Polynomial ℚ, (∀ k : ℕ, 2 * n + 2 * m - D' < k → f.coeff k = 0) ∧
        ∀ M, cfL (G' (M - d + W₂)) n m = f.eval (((M - d : ℕ) : ℚ)) := fun n m => by
      obtain ⟨f, h1, h2⟩ := h'.poly n m
      exact ⟨f, h1, fun M => h2 (M - d)⟩
    choose f1 hf1 hf1' using hpoly
    choose f2 hf2 hf2' using hpoly'
    refine ⟨∑ n ∈ Icc b (i - b'), ∑ m ∈ Icc ((V - 2 * n) / 2) (j - (V' - 2 * (i - n)) / 2),
      f1 n m * (f2 (i - n) (j - m)).comp (Polynomial.X - Polynomial.C (d : ℚ)), ?_, fun M => ?_⟩
    · intro k hk
      rw [Polynomial.finsetSum_coeff]
      refine sum_eq_zero fun n _ => ?_
      rw [Polynomial.finsetSum_coeff]
      refine sum_eq_zero fun m _ => ?_
      by_cases h1z : f1 n m = 0
      · rw [h1z, zero_mul, Polynomial.coeff_zero]
      by_cases h2z : f2 (i - n) (j - m) = 0
      · rw [h2z, Polynomial.zero_comp, mul_zero, Polynomial.coeff_zero]
      have hd1 : (f1 n m).natDegree ≤ 2 * n + 2 * m - D := by
        by_contra hc
        exact (Polynomial.leadingCoeff_ne_zero.2 h1z) (hf1 n m _ (by omega))
      have hd2 : ((f2 (i - n) (j - m)).natDegree : ℤ) ≤ 2 * (i - n) + 2 * (j - m) - D' := by
        by_contra hc
        exact (Polynomial.leadingCoeff_ne_zero.2 h2z) (hf2 (i - n) (j - m) _ (by omega))
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hc : ((f2 (i - n) (j - m)).comp (Polynomial.X - Polynomial.C (d : ℚ))).natDegree ≤
          (f2 (i - n) (j - m)).natDegree :=
        Polynomial.natDegree_comp_le.trans
          ((Nat.mul_le_mul_left _ (Polynomial.natDegree_X_sub_C_le _)).trans (by rw [mul_one]))
      have := Polynomial.natDegree_mul_le (p := f1 n m)
        (q := (f2 (i - n) (j - m)).comp (Polynomial.X - Polynomial.C (d : ℚ)))
      omega
    · beta_reduce
      rw [Polynomial.eval_finsetSum]
      by_cases hM : d ≤ M
      · rw [key M i j hM]
        refine sum_congr rfl fun n _ => ?_
        rw [Polynomial.eval_finsetSum]
        refine sum_congr rfl fun m _ => ?_
        rw [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C, ← hf1' n m M, hf2' (i - n) (j - m) M, Nat.cast_sub hM]
      · rw [hzero M (by omega), zero_mul, cfL_zero]
        refine (sum_eq_zero fun n _ => ?_).symm
        rw [Polynomial.eval_finsetSum]
        refine sum_eq_zero fun m _ => ?_
        rw [Polynomial.eval_mul, ← hf1' n m M, hzero M (by omega), cfL_zero, zero_mul]
  · by_cases hM : d ≤ M
    · rw [key M i j hM]
      refine sum_eq_zero fun n _ => sum_eq_zero fun m _ => ?_
      by_cases h1 : 2 * n + 2 * m < V
      · rw [h.val M n m h1, zero_mul]
      · have := h'.val (M - d) (i - n) (j - m) (by omega)
        rw [this, mul_zero]
    · beta_reduce
      rw [hzero M (by omega), zero_mul, cfL_zero]
  · by_cases hM : d ≤ M
    · beta_reduce
      have e1 : M + W₁ = M - d + W₂ := by omega
      rw [hahn_coeff_mul (hb M) (by rw [e1]; exact hb' (M - d))]
      refine sum_eq_zero fun k hk => ?_
      have := mem_Icc.1 hk
      omega
    · beta_reduce
      rw [hzero M (by omega), zero_mul, HahnSeries.coeff_zero]

end Virasoro.H13T
