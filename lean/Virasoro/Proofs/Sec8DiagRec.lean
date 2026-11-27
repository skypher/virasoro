import Virasoro.Proofs.Sec8DiagMoments

/-!
# Theorem 8.8, first part: the recursion (8.2) and the comparison of three models

Lemma 8.7(i) divided by `Top(a→μ)`, with Lemma 8.7(ii) and Proposition 8.6:
`f_j(a,μ) S_μ = f_{j-1}(a,μ) S_a - ∑_ν κ̂(a,ν,μ) f_{j-1}(ν,μ) S_ν` (8.2), over the two nodes `ν` of
layer `L_a + k`.  The numbers `f` (`fVal`) and `κ̂` (`kap`) are the same in every minimal model;
with `S_x = 2pp' (c_x + π_x)`, `c_x` the class centre of `x`, (8.2) divided by `2pp'` is an affine
identity in the class centres, and the three models `(2,3)`, `(2,5)`, `(3,4)` at `h_{1,1}` give its
three coefficients.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' r s : ℕ} {b : ℂ}

/-- `κ̂(a,ν,μ)`: Proposition 8.6's `kappaHat` at odd distance, `kappaEven` at even distance. -/
def kap (a ν μ : Node) : ℚ := if (ν.2 - a.2) % 2 = 1 then kappaHat a ν μ else kappaEven a ν μ

/-- `κ(a,ν,μ) = (S_ν/S_a)^{D(ν,μ)} κ̂(a,ν,μ)`. -/
def kfac (p p' r s : ℕ) (a ν μ : Node) : ℚ :=
  ((nodeS p p' r s ν : ℚ) / nodeS p p' r s a) ^ (μ.2 - ν.2) * kap a ν μ

/-- `c^{(D-j)}_{a→μ,j}(b⋆)/Top(a→μ) = f_j(a,μ)/j! (S_μ/S_a)^j`. -/
def cv (p p' r s : ℕ) (a μ : Node) (j : ℕ) : ℚ :=
  fVal a μ j / j.factorial * ((nodeS p p' r s μ : ℚ) / nodeS p p' r s a) ^ j

/-- The class centre of a node: `α` for even layers, `β` for odd layers. -/
def cls (x : Node) (α β : ℚ) : ℚ := if x.2 % 2 = 0 then α else β

/-- (8.2) divided by `2pp'`, with class centres `α`, `β`, as a function of `(α, β)`. -/
def Ecoef (a μ : Node) (m : ℕ) (α β : ℚ) : ℚ :=
  fVal a μ (m + 1) * (cls μ α β + nodePos μ) - fVal a μ m * (cls a α β + nodePos a) +
    ∑ ε : Bool, kap a (ε, a.2 + (μ.2 - a.2 - (m + 1))) μ *
      fVal (ε, a.2 + (μ.2 - a.2 - (m + 1))) μ m *
        (cls (ε, a.2 + (μ.2 - a.2 - (m + 1))) α β + nodePos (ε, a.2 + (μ.2 - a.2 - (m + 1))))

theorem Ecoef_affine (a μ : Node) (m : ℕ) (α β : ℚ) :
    Ecoef a μ m α β = α * (Ecoef a μ m 1 0 - Ecoef a μ m 0 0) +
      β * (Ecoef a μ m 0 1 - Ecoef a μ m 0 0) + Ecoef a μ m 0 0 := by
  unfold Ecoef cls
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool]
  split_ifs <;> ring

section Model

variable (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
  (hset : MinimalSetting p p' r s b)
include hK hH hset

theorem top_kap {a ν μ : Node} (h1 : a.2 < ν.2) (h2 : ν.2 < μ.2) :
    nodeTop p p' r s b a ν * nodeTop p p' r s b ν μ =
      ((kfac p p' r s a ν μ : ℚ) : Kd) * nodeTop p p' r s b a μ := by
  unfold kfac kap
  split_ifs with ho
  · exact top_identity hK hH hset (mem_firstSteps.2 (Or.inl ⟨h1, h2, ho⟩))
      (by intro e; rw [e] at h2; exact lt_irrefl _ h2)
  · exact top_even hK hH hset h1 h2 (by omega)

theorem chain_val {a μ : Node} (haμ : a.2 < μ.2) (j : ℕ) (hj : j < μ.2 - a.2) :
    (nodeChain p p' r s b a μ (μ.2 - a.2 - j) j).coeff 0 =
      ((cv p p' r s a μ j : ℚ) : Kd) * nodeTop p p' r s b a μ := by
  have hX := diag_values_ii hK hH hset haμ j hj
  have hSa : (nodeS p p' r s a : ℚ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset a
  have hSμ : (nodeS p p' r s μ : ℚ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset μ
  have hf : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hcq : (j.factorial : ℚ) * ((nodeS p p' r s a : ℚ) / nodeS p p' r s μ) ^ j ≠ 0 :=
    mul_ne_zero hf (pow_ne_zero _ (div_ne_zero hSa hSμ))
  have hrat : ((j.factorial : ℚ) * ((nodeS p p' r s a : ℚ) / nodeS p p' r s μ) ^ j) *
      cv p p' r s a μ j = fVal a μ j := by
    unfold cv
    rw [div_pow, div_pow]
    field_simp
  have hc : (((j.factorial : ℚ) * ((nodeS p p' r s a : ℚ) / nodeS p p' r s μ) ^ j : ℚ) : Kd) ≠ 0 := by
    exact_mod_cast hcq
  apply mul_left_cancel₀ hc
  rw [← mul_assoc, ← Rat.cast_mul, hrat]
  rw [← hX]
  push_cast
  ring

/-- (8.2) in the model `(p, p', r, s)`. -/
theorem rec82 {a μ : Node} (haμ : a.2 < μ.2) (m : ℕ) (hj : m + 1 < μ.2 - a.2) :
    fVal a μ (m + 1) * (nodeS p p' r s μ : ℚ) - fVal a μ m * nodeS p p' r s a +
      ∑ ε : Bool, kap a (ε, a.2 + (μ.2 - a.2 - (m + 1))) μ *
        fVal (ε, a.2 + (μ.2 - a.2 - (m + 1))) μ m *
          (nodeS p p' r s (ε, a.2 + (μ.2 - a.2 - (m + 1))) : ℚ) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, μ.2 - a.2 - (m + 1) = k := ⟨_, rfl⟩
  rw [hk]
  have hi := diag_values_i hK hH hset haμ k (m + 1) (by omega) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hi
  have hX := chain_val hK hH hset haμ (m + 1) (by omega)
  rw [hk] at hX
  have hY := chain_val hK hH hset haμ m (by omega)
  rw [show μ.2 - a.2 - m = k + 1 by omega] at hY
  have hZ : ∀ ε : Bool, (nodeChain p p' r s b (ε, a.2 + k) μ 1 m).coeff 0 =
      ((cv p p' r s (ε, a.2 + k) μ m : ℚ) : Kd) * nodeTop p p' r s b (ε, a.2 + k) μ := by
    intro ε
    have h := chain_val hK hH hset (a := (ε, a.2 + k)) (μ := μ)
      (show a.2 + k < μ.2 by omega) m (show m < μ.2 - (a.2 + k) by omega)
    rwa [show μ.2 - (ε, a.2 + k).2 - m = 1 by show μ.2 - (a.2 + k) - m = 1; omega] at h
  have hκ : ∀ ε : Bool, nodeTop p p' r s b a (ε, a.2 + k) * nodeTop p p' r s b (ε, a.2 + k) μ =
      ((kfac p p' r s a (ε, a.2 + k) μ : ℚ) : Kd) * nodeTop p p' r s b a μ := fun ε =>
    top_kap hK hH hset (show a.2 < a.2 + k by omega) (show a.2 + k < μ.2 by omega)
  have hT := top_ne hK hH hset haμ
  rw [hX, hY, Fintype.sum_bool, hZ true, hZ false] at hi
  have h0 : (((m : Kd) + 1) * ((cv p p' r s a μ (m + 1) : ℚ) : Kd) - ((cv p p' r s a μ m : ℚ) : Kd) +
      ((cv p p' r s (true, a.2 + k) μ m : ℚ) : Kd) * ((kfac p p' r s a (true, a.2 + k) μ : ℚ) : Kd) +
      ((cv p p' r s (false, a.2 + k) μ m : ℚ) : Kd) *
        ((kfac p p' r s a (false, a.2 + k) μ : ℚ) : Kd)) * nodeTop p p' r s b a μ = 0 := by
    push_cast at hi
    linear_combination hi - ((cv p p' r s (true, a.2 + k) μ m : ℚ) : Kd) * hκ true -
      ((cv p p' r s (false, a.2 + k) μ m : ℚ) : Kd) * hκ false
  have h1 : ((((m : ℚ) + 1) * cv p p' r s a μ (m + 1) - cv p p' r s a μ m +
      cv p p' r s (true, a.2 + k) μ m * kfac p p' r s a (true, a.2 + k) μ +
      cv p p' r s (false, a.2 + k) μ m * kfac p p' r s a (false, a.2 + k) μ : ℚ) : Kd) = 0 := by
    have := (mul_eq_zero.1 h0).resolve_right hT
    push_cast
    exact this
  have h2 := Rat.cast_eq_zero.1 h1
  have hSa : (nodeS p p' r s a : ℚ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset a
  have hSμ : (nodeS p p' r s μ : ℚ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset μ
  have hSt : (nodeS p p' r s (true, a.2 + k) : ℚ) ≠ 0 := by
    exact_mod_cast nodeS_ne_zero hset (true, a.2 + k)
  have hSf : (nodeS p p' r s (false, a.2 + k) : ℚ) ≠ 0 := by
    exact_mod_cast nodeS_ne_zero hset (false, a.2 + k)
  have hfm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hD : μ.2 - (a.2 + k) = m + 1 := by omega
  unfold cv kfac at h2
  simp only at h2
  rw [hD, Nat.factorial_succ] at h2
  rw [Fintype.sum_bool]
  have e : fVal a μ (m + 1) * (nodeS p p' r s μ : ℚ) - fVal a μ m * nodeS p p' r s a +
      (kap a (true, a.2 + k) μ * fVal (true, a.2 + k) μ m * (nodeS p p' r s (true, a.2 + k) : ℚ) +
        kap a (false, a.2 + k) μ * fVal (false, a.2 + k) μ m *
          (nodeS p p' r s (false, a.2 + k) : ℚ)) =
      (((m : ℚ) + 1) * (fVal a μ (m + 1) / ((m + 1 : ℕ) * m.factorial : ℕ) *
          ((nodeS p p' r s μ : ℚ) / nodeS p p' r s a) ^ (m + 1)) -
        fVal a μ m / m.factorial * ((nodeS p p' r s μ : ℚ) / nodeS p p' r s a) ^ m +
        fVal (true, a.2 + k) μ m / m.factorial *
            ((nodeS p p' r s μ : ℚ) / nodeS p p' r s (true, a.2 + k)) ^ m *
          (((nodeS p p' r s (true, a.2 + k) : ℚ) / nodeS p p' r s a) ^ (m + 1) *
            kap a (true, a.2 + k) μ) +
        fVal (false, a.2 + k) μ m / m.factorial *
            ((nodeS p p' r s μ : ℚ) / nodeS p p' r s (false, a.2 + k)) ^ m *
          (((nodeS p p' r s (false, a.2 + k) : ℚ) / nodeS p p' r s a) ^ (m + 1) *
            kap a (false, a.2 + k) μ)) *
        ((m.factorial : ℚ) * nodeS p p' r s a * ((nodeS p p' r s a : ℚ) / nodeS p p' r s μ) ^ m) := by
    push_cast
    simp only [div_pow]
    field_simp
    ring
  rw [e, h2, zero_mul]

/-- (8.2) divided by `2pp'`: `Ecoef` vanishes at the class centres of the model. -/
theorem Ecoef_model {a μ : Node} (haμ : a.2 < μ.2) (m : ℕ) (hj : m + 1 < μ.2 - a.2) :
    Ecoef a μ m (((p' : ℚ) * r - p * s) / (2 * p * p'))
      (((p' : ℚ) * r + p * s - p * p') / (2 * p * p')) = 0 := by
  have h := rec82 hK hH hset haμ m hj
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hN : (2 * (p : ℚ) * p') ≠ 0 := by positivity
  have hS : ∀ x : Node, (nodeS p p' r s x : ℚ) = (2 * (p : ℚ) * p') *
      (cls x (((p' : ℚ) * r - p * s) / (2 * p * p')) (((p' : ℚ) * r + p * s - p * p') / (2 * p * p')) +
        nodePos x) := by
    intro x
    rw [nodeS_pos]
    unfold cls
    split_ifs <;> field_simp <;> ring
  rw [Fintype.sum_bool, hS μ, hS a, hS (true, _), hS (false, _)] at h
  have h' : (2 * (p : ℚ) * p') *
      Ecoef a μ m (((p' : ℚ) * r - p * s) / (2 * p * p'))
        (((p' : ℚ) * r + p * s - p * p') / (2 * p * p')) = 0 := by
    unfold Ecoef
    rw [Fintype.sum_bool]
    linear_combination h
  exact (mul_eq_zero.1 h').resolve_left hN

end Model

theorem exists_model (p p' r s : ℕ) (h : 2 ≤ p ∧ 2 ≤ p' ∧ Nat.Coprime p p' ∧ 0 < r ∧ r < p ∧ 0 < s ∧
    s < p' ∧ p' * r + p * s < p * p') : ∃ b : ℂ, MinimalSetting p p' r s b := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (-(p' : ℂ) / p) (show 0 < 2 by norm_num)
  exact ⟨b, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, hb⟩

/-- The three models `(2,3)`, `(2,5)`, `(3,4)` at `h_{1,1}`: (8.2) holds for all class centres. -/
theorem Ecoef_zero (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {a μ : Node}
    (haμ : a.2 < μ.2) (m : ℕ) (hj : m + 1 < μ.2 - a.2) (α β : ℚ) : Ecoef a μ m α β = 0 := by
  obtain ⟨b1, h1⟩ := exists_model 2 3 1 1 (by decide)
  obtain ⟨b2, h2⟩ := exists_model 2 5 1 1 (by decide)
  obtain ⟨b3, h3⟩ := exists_model 3 4 1 1 (by decide)
  have e1 := Ecoef_model hK hH h1 haμ m hj
  have e2 := Ecoef_model hK hH h2 haμ m hj
  have e3 := Ecoef_model hK hH h3 haμ m hj
  rw [Ecoef_affine] at e1 e2 e3
  rw [Ecoef_affine]
  norm_num at e1 e2 e3
  have hC0 : Ecoef a μ m 1 0 - Ecoef a μ m 0 0 = 0 := by linarith
  have hC1 : Ecoef a μ m 0 1 - Ecoef a μ m 0 0 = 0 := by linarith
  have hC2 : Ecoef a μ m 0 0 = 0 := by linarith
  rw [hC0, hC1, hC2]
  ring

end Virasoro
