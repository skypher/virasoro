import Virasoro.Proofs.Sec8BMoments
import Virasoro.Proofs.Sec8DiagRec

/-!
# Section 8.2: Theorem 8.11(ii)

Lemma 8.7(i) at the boundary divided by `Top(μ_i→μ_k)`, with Lemma 8.7(ii) at the boundary and
Proposition 8.6 at the boundary: one node `ν = μ_{k-j}` in the layer `L_a + D - j`, and
`f_j(i,k) T_k = f_{j-1}(i,k) T_i - κ̂(i,ν,k) f_{j-1}(ν,k) T_ν`.  The numbers `f` and `κ̂` depend
only on the positions `π`; with `T_m = x₀ + π_m N₀` the identity is affine in `x₀`, and the two
boundary weights `x₀ = 2, 4` of `(p,p') = (2,3)` give `f_j = f_{j-1} - κ̂ f_{j-1}(ν,k)` and
`f_j π_k = f_{j-1} π_i - κ̂ f_{j-1}(ν,k) π_ν`.  Eliminating the last term,
`f_j(i,k)(π_k - π_{k-j}) = f_{j-1}(i,k)(π_i - π_{k-j})`, and induction from `f_0 = 1`.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' x₀ : ℕ} {b : ℂ}

/-- `c^{(D-j)}_{μ_i→μ_k,j}(b⋆)/Top(μ_i→μ_k) = f_j(i,k)/j! (T_k/T_i)^j`. -/
def cvB (p p' x₀ : ℕ) (i k j : ℕ) : ℚ :=
  fValB i k j / j.factorial * ((bT p p' x₀ k : ℚ) / bT p p' x₀ i) ^ j

section Model

variable (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
  (hB : BoundarySetting p p' x₀ b)
include hK hH hB

theorem b_chain_val {i k : ℕ} (hik : i < k) (j : ℕ) (hj : j < k - i) :
    (bChain p p' x₀ b i k (k - i - j) j).coeff 0 =
      ((cvB p p' x₀ i k j : ℚ) : Kd) * bTop p p' x₀ b i k := by
  have hX := b_values_ii hK hH hB hik j hj
  have hTi : (bT p p' x₀ i : ℚ) ≠ 0 := by exact_mod_cast bT_ne hB i
  have hTk : (bT p p' x₀ k : ℚ) ≠ 0 := by exact_mod_cast bT_ne hB k
  have hf : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hcq : (j.factorial : ℚ) * ((bT p p' x₀ i : ℚ) / bT p p' x₀ k) ^ j ≠ 0 :=
    mul_ne_zero hf (pow_ne_zero _ (div_ne_zero hTi hTk))
  have hrat : ((j.factorial : ℚ) * ((bT p p' x₀ i : ℚ) / bT p p' x₀ k) ^ j) *
      cvB p p' x₀ i k j = fValB i k j := by
    unfold cvB
    rw [div_pow, div_pow]
    field_simp
  have hc : (((j.factorial : ℚ) * ((bT p p' x₀ i : ℚ) / bT p p' x₀ k) ^ j : ℚ) : Kd) ≠ 0 := by
    exact_mod_cast hcq
  apply mul_left_cancel₀ hc
  rw [← mul_assoc, ← Rat.cast_mul, hrat, ← hX]
  push_cast
  ring

/-- (8.2) at the boundary, in the model `(p, p', x₀)`. -/
theorem b_rec {i k : ℕ} (hik : i < k) (m : ℕ) (hj : m + 1 < k - i) :
    fValB i k (m + 1) * (bT p p' x₀ k : ℚ) - fValB i k m * bT p p' x₀ i +
      bKappa i (k - (m + 1)) k * fValB (k - (m + 1)) k m * (bT p p' x₀ (k - (m + 1)) : ℚ) = 0 := by
  obtain ⟨k', hk'⟩ : ∃ k', k - i - (m + 1) = k' := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν, k - (m + 1) = ν := ⟨_, rfl⟩
  rw [hν]
  have hνeq : i + k' = ν := by omega
  have hi := b_values_i hK hH hB hik k' (m + 1) (by omega) (by omega) (by omega)
  simp only [Nat.add_sub_cancel] at hi
  rw [hνeq] at hi
  have hX := b_chain_val hK hH hB hik (m + 1) (by omega)
  rw [hk'] at hX
  have hY := b_chain_val hK hH hB hik m (by omega)
  rw [show k - i - m = k' + 1 by omega] at hY
  have hZ := b_chain_val hK hH hB (show ν < k by omega) m (by omega)
  rw [show k - ν - m = 1 by omega] at hZ
  have hκ := b_top_identity hB hK hH (show i < ν by omega) (show ν < k by omega)
  have hT := (b_thm_i hB hK hH hik).2.2
  rw [hX, hY, hZ] at hi
  have h0 : (((m : Kd) + 1) * ((cvB p p' x₀ i k (m + 1) : ℚ) : Kd) - ((cvB p p' x₀ i k m : ℚ) : Kd) +
      ((cvB p p' x₀ ν k m : ℚ) : Kd) * ((bKfac p p' x₀ i ν k : ℚ) : Kd)) *
        bTop p p' x₀ b i k = 0 := by
    push_cast at hi
    linear_combination hi - ((cvB p p' x₀ ν k m : ℚ) : Kd) * hκ
  have h1 : ((((m : ℚ) + 1) * cvB p p' x₀ i k (m + 1) - cvB p p' x₀ i k m +
      cvB p p' x₀ ν k m * bKfac p p' x₀ i ν k : ℚ) : Kd) = 0 := by
    have := (mul_eq_zero.1 h0).resolve_right hT
    push_cast
    exact this
  have h2 := Rat.cast_eq_zero.1 h1
  have hTi : (bT p p' x₀ i : ℚ) ≠ 0 := by exact_mod_cast bT_ne hB i
  have hTk : (bT p p' x₀ k : ℚ) ≠ 0 := by exact_mod_cast bT_ne hB k
  have hTν : (bT p p' x₀ ν : ℚ) ≠ 0 := by exact_mod_cast bT_ne hB ν
  have hfm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
  have hD : k - ν = m + 1 := by omega
  unfold cvB bKfac at h2
  rw [hD, Nat.factorial_succ] at h2
  have e : fValB i k (m + 1) * (bT p p' x₀ k : ℚ) - fValB i k m * bT p p' x₀ i +
      bKappa i ν k * fValB ν k m * (bT p p' x₀ ν : ℚ) =
      (((m : ℚ) + 1) * (fValB i k (m + 1) / ((m + 1 : ℕ) * m.factorial : ℕ) *
          ((bT p p' x₀ k : ℚ) / bT p p' x₀ i) ^ (m + 1)) -
        fValB i k m / m.factorial * ((bT p p' x₀ k : ℚ) / bT p p' x₀ i) ^ m +
        fValB ν k m / m.factorial * ((bT p p' x₀ k : ℚ) / bT p p' x₀ ν) ^ m *
          (((bT p p' x₀ ν : ℚ) / bT p p' x₀ i) ^ (m + 1) * bKappa i ν k)) *
        ((m.factorial : ℚ) * bT p p' x₀ i * ((bT p p' x₀ i : ℚ) / bT p p' x₀ k) ^ m) := by
    push_cast
    simp only [div_pow]
    field_simp
    ring
  rw [e, h2, zero_mul]

end Model

theorem exists_bsetting (p p' x₀ : ℕ) (h : 2 ≤ p ∧ 2 ≤ p' ∧ Nat.Coprime p p' ∧ 0 < x₀ ∧
    x₀ < p * p' ∧ (p ∣ x₀ ↔ ¬ p' ∣ x₀)) : ∃ b : ℂ, BoundarySetting p p' x₀ b := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (-(p' : ℂ) / p) (show 0 < 2 by norm_num)
  exact ⟨b, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hb⟩

/-- The two boundary weights `x₀ = 2, 4` of `(2,3)`: both coefficients of the affine identity
vanish. -/
theorem b_rec_pi (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {i k : ℕ}
    (hik : i < k) (m : ℕ) (hj : m + 1 < k - i) :
    fValB i k (m + 1) - fValB i k m + bKappa i (k - (m + 1)) k * fValB (k - (m + 1)) k m = 0 ∧
      fValB i k (m + 1) * bPi k - fValB i k m * bPi i +
        bKappa i (k - (m + 1)) k * fValB (k - (m + 1)) k m * bPi (k - (m + 1)) = 0 := by
  obtain ⟨b2, h2⟩ := exists_bsetting 2 3 2 (by decide)
  obtain ⟨b4, h4⟩ := exists_bsetting 2 3 4 (by decide)
  have e2 := b_rec hK hH h2 hik m hj
  have e4 := b_rec hK hH h4 hik m hj
  simp only [bT] at e2 e4
  push_cast at e2 e4
  constructor
  · linear_combination (e4 - e2) / 2
  · linear_combination (2 * e2 - e4) / 12

/-- The closed form of `f_j(i,k)`. -/
theorem fValB_closed (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {i k : ℕ}
    (hik : i < k) : ∀ j : ℕ, j < k - i →
    fValB i k j = ∏ m ∈ Finset.Icc 1 j, (((bPi i : ℚ) - bPi (k - m)) / ((bPi k : ℚ) - bPi (k - m))) := by
  intro j
  induction j with
  | zero => intro _; simp [fValB]
  | succ m ih =>
    intro hj
    obtain ⟨A, B⟩ := b_rec_pi hK hH hik m hj
    have hm := ih (by omega)
    have hkey : fValB i k (m + 1) * ((bPi k : ℚ) - bPi (k - (m + 1))) =
        fValB i k m * ((bPi i : ℚ) - bPi (k - (m + 1))) := by
      linear_combination B - (bPi (k - (m + 1)) : ℚ) * A
    have hne : (bPi k : ℚ) - bPi (k - (m + 1)) ≠ 0 := by
      refine sub_ne_zero.2 fun e => ?_
      have := bPi_injective (by exact_mod_cast e : bPi k = bPi (k - (m + 1)))
      omega
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), ← hm, mul_div_assoc', eq_div_iff hne]
    exact hkey

/-- Theorem 8.11(ii). -/
theorem b_thm_ii (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hB : BoundarySetting p p' x₀ b) {i k j : ℕ} (hik : i < k) (hj : j < k - i) :
    (bChain p p' x₀ b i k (k - i - j) j).coeff 0 =
      ((1 / j.factorial * ((bT p p' x₀ k : ℚ) / bT p p' x₀ i) ^ j *
          ∏ m ∈ Finset.Icc 1 j, (((bPi i : ℚ) - bPi (k - m)) / ((bPi k : ℚ) - bPi (k - m))) : ℚ) :
        Kd) * bTop p p' x₀ b i k := by
  rw [b_chain_val hK hH hB hik j hj]
  congr 2
  unfold cvB
  rw [fValB_closed hK hH hik j hj]
  ring

end Virasoro
