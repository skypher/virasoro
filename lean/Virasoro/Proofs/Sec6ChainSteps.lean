import Virasoro.Proofs.Sec6ChainConst
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Proposition 6.7: the colliding chains by integrality (paper.tex l.1150–1156)

A step `g = (u,v)` from a weight of momentum `x` has `(p'u − pv)² = x²`; by integrality of `u, v`
and coprimality of `p, p'`, the momentum `p'u + pv` reached lies in a fixed class modulo
`N₀ = 2pp'` (`ChainEval.next_step`).  The first steps from `λ` are the labels
`g_i = (r + ip, s + ip')` (`i ≥ 0`) and `(|i|p − r, |i|p' − s)` (`i < 0`), with
`p'u + pv = ±(n₁ + iN₀)` (`ChainEval.gL`, `ChainEval.mem_firstSteps_iff`); then
`ρ_{g_i} = ∓n₀/(2(p'−p))` and `4p'² ḣ_{g_i} = p'² − p² − n₀(n₁ + iN₀)`.
-/

namespace Virasoro.ChainEval

/-- The setting of the chains: `p, p' ≥ 2` coprime, `0 < r < p`, `0 < s < p'`. -/
structure Setup (p p' r s : ℕ) : Prop where
  hp : 2 ≤ p
  hp' : 2 ≤ p'
  cop : Nat.Coprime p p'
  hr : 0 < r
  hrp : r < p
  hs : 0 < s
  hsp : s < p'

/-- `n₀ = p'r − ps`. -/
def n0 (p p' r s : ℕ) : ℤ := (p' : ℤ) * r - (p : ℤ) * s

/-- `n₁ = p'r + ps`. -/
def n1 (p p' r s : ℕ) : ℤ := (p' : ℤ) * r + (p : ℤ) * s

/-- `N₀ = 2pp'`. -/
def N0 (p p' : ℕ) : ℤ := 2 * (p : ℤ) * p'

variable {p p' r s : ℕ}

theorem Setup.N0_pos (h : Setup p p' r s) : 0 < N0 p p' := by
  have h1 : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have h2 : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  unfold N0
  positivity

theorem Setup.sum_lt (h : Setup p p' r s) : n1 p p' r s + n0 p p' r s < N0 p p' := by
  have h1 : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  have h2 : (r : ℤ) < p := by exact_mod_cast h.hrp
  unfold n1 n0 N0
  nlinarith

theorem Setup.diff_lt (h : Setup p p' r s) : n1 p p' r s - n0 p p' r s < N0 p p' := by
  have h1 : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have h2 : (s : ℤ) < p' := by exact_mod_cast h.hsp
  unfold n1 n0 N0
  nlinarith

theorem Setup.sum_pos (h : Setup p p' r s) : 0 < n1 p p' r s + n0 p p' r s := by
  have h1 : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  have h2 : (0 : ℤ) < r := by exact_mod_cast h.hr
  unfold n1 n0
  nlinarith

theorem Setup.diff_pos (h : Setup p p' r s) : 0 < n1 p p' r s - n0 p p' r s := by
  have h1 : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have h2 : (0 : ℤ) < s := by exact_mod_cast h.hs
  unfold n1 n0
  nlinarith

theorem Setup.isCoprime (h : Setup p p' r s) : IsCoprime (p : ℤ) (p' : ℤ) :=
  Nat.isCoprime_iff_coprime.2 h.cop

/-- `p'u − pv = p'u₁ − pv₁` forces `(u,v) = (u₁ + ip, v₁ + ip')`. -/
theorem Setup.step_param (h : Setup p p' r s) {u v u1 v1 : ℤ}
    (he : (p' : ℤ) * u - (p : ℤ) * v = (p' : ℤ) * u1 - (p : ℤ) * v1) :
    ∃ i : ℤ, u = u1 + i * p ∧ v = v1 + i * p' := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (by have := h.hp; omega : p ≠ 0)
  have hdvd : (p : ℤ) ∣ (u - u1) * p' := ⟨v - v1, by linear_combination he⟩
  obtain ⟨i, hi⟩ := h.isCoprime.dvd_of_dvd_mul_right hdvd
  refine ⟨i, by linear_combination hi, ?_⟩
  have h2 : (p : ℤ) * (v - v1) = (p : ℤ) * (i * p') := by
    linear_combination (p' : ℤ) * hi - he
  have h3 := mul_left_cancel₀ hp0 h2
  linear_combination h3

/-- The step after a label of momenta `(p'u₁ − pv₁, p'u₁ + pv₁)` (paper.tex l.1150–1153). -/
theorem Setup.next_step (h : Setup p p' r s) {u v u1 v1 : ℤ}
    (he : ((p' : ℤ) * u - (p : ℤ) * v) ^ 2 = ((p' : ℤ) * u1 + (p : ℤ) * v1) ^ 2) :
    ∃ i : ℤ, (u = u1 + i * p ∧ v = -v1 + i * p') ∨ (u = -u1 + i * p ∧ v = v1 + i * p') := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 he with h1 | h1
  · obtain ⟨i, hi⟩ := h.step_param (u := u) (v := v) (u1 := u1) (v1 := -v1) (by linear_combination h1)
    exact ⟨i, Or.inl hi⟩
  · obtain ⟨i, hi⟩ := h.step_param (u := u) (v := v) (u1 := -u1) (v1 := v1) (by linear_combination h1)
    exact ⟨i, Or.inr hi⟩

/-- `4pp' ℓ_g = (p'u + pv)² − (p'u − pv)²`. -/
theorem lvl_eq (p p' : ℕ) (g : Label) :
    2 * N0 p p' * (g.lvl : ℤ) =
      ((p' : ℤ) * g.1 + (p : ℤ) * g.2) ^ 2 - ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 := by
  unfold N0 Label.lvl
  push_cast
  ring

theorem mem_labels_iff (N : ℕ) (g : Label) :
    g ∈ labels N ↔ 1 ≤ g.1 ∧ 1 ≤ g.2 ∧ g.lvl ≤ N := by
  unfold labels Label.lvl
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, h2, _⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨⟨h1, ?_⟩, h2, ?_⟩, h3⟩
    · exact le_trans (Nat.le_mul_of_pos_right _ (by omega)) h3
    · exact le_trans (Nat.le_mul_of_pos_left _ (by omega)) h3

/-- The first steps: `g_i = (r + ip, s + ip')` for `i ≥ 0`, `(|i|p − r, |i|p' − s)` for
`i < 0`. -/
def gL (p p' r s : ℕ) (i : ℤ) : Label :=
  if 0 ≤ i then (r + i.toNat * p, s + i.toNat * p')
  else ((-i).toNat * p - r, (-i).toNat * p' - s)

theorem gL_nonneg {i : ℤ} (hi : 0 ≤ i) :
    ((gL p p' r s i).1 : ℤ) = r + i * p ∧ ((gL p p' r s i).2 : ℤ) = s + i * p' := by
  rw [gL, if_pos hi]
  push_cast
  rw [Int.toNat_of_nonneg hi]
  exact ⟨rfl, rfl⟩

theorem Setup.gL_neg (h : Setup p p' r s) {i : ℤ} (hi : i < 0) :
    ((gL p p' r s i).1 : ℤ) = -r - i * p ∧ ((gL p p' r s i).2 : ℤ) = -s - i * p' := by
  have h1 : 1 ≤ (-i).toNat := by omega
  have hr : r ≤ (-i).toNat * p := le_trans h.hrp.le (Nat.le_mul_of_pos_left _ h1)
  have hs : s ≤ (-i).toNat * p' := le_trans h.hsp.le (Nat.le_mul_of_pos_left _ h1)
  rw [gL, if_neg (not_le.2 hi)]
  rw [Nat.cast_sub hr, Nat.cast_sub hs]
  push_cast
  rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -i)]
  constructor <;> ring

/-- The sign `ε_i` of the momentum `n₁ + iN₀` reached by `g_i`. -/
def sgnI (i : ℤ) : ℤ := if 0 ≤ i then 1 else -1

theorem sgnI_sq (i : ℤ) : sgnI i ^ 2 = 1 := by
  unfold sgnI
  split_ifs <;> norm_num

theorem Setup.gL_diff (h : Setup p p' r s) (i : ℤ) :
    (p' : ℤ) * (gL p p' r s i).1 - (p : ℤ) * (gL p p' r s i).2 = sgnI i * n0 p p' r s := by
  unfold sgnI n0
  rcases le_or_gt 0 i with hi | hi
  · obtain ⟨h1, h2⟩ := gL_nonneg (p := p) (p' := p') (r := r) (s := s) hi
    rw [if_pos hi, h1, h2]
    ring
  · obtain ⟨h1, h2⟩ := h.gL_neg hi
    rw [if_neg (not_le.2 hi), h1, h2]
    ring

theorem Setup.gL_sum (h : Setup p p' r s) (i : ℤ) :
    (p' : ℤ) * (gL p p' r s i).1 + (p : ℤ) * (gL p p' r s i).2 =
      sgnI i * (n1 p p' r s + i * N0 p p') := by
  unfold sgnI n1 N0
  rcases le_or_gt 0 i with hi | hi
  · obtain ⟨h1, h2⟩ := gL_nonneg (p := p) (p' := p') (r := r) (s := s) hi
    rw [if_pos hi, h1, h2]
    ring
  · obtain ⟨h1, h2⟩ := h.gL_neg hi
    rw [if_neg (not_le.2 hi), h1, h2]
    ring

theorem Setup.gL_pos (h : Setup p p' r s) (i : ℤ) :
    1 ≤ (gL p p' r s i).1 ∧ 1 ≤ (gL p p' r s i).2 := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have hp' : (0 : ℤ) < p' := by exact_mod_cast (by have := h.hp'; omega : 0 < p')
  have hr : (0 : ℤ) < r := by exact_mod_cast h.hr
  have hs : (0 : ℤ) < s := by exact_mod_cast h.hs
  have hrp : (r : ℤ) < p := by exact_mod_cast h.hrp
  have hsp : (s : ℤ) < p' := by exact_mod_cast h.hsp
  rcases le_or_gt 0 i with hi | hi
  · obtain ⟨h1, h2⟩ := gL_nonneg (p := p) (p' := p') (r := r) (s := s) hi
    constructor
    · have : (1 : ℤ) ≤ (gL p p' r s i).1 := by rw [h1]; nlinarith
      exact_mod_cast this
    · have : (1 : ℤ) ≤ (gL p p' r s i).2 := by rw [h2]; nlinarith
      exact_mod_cast this
  · obtain ⟨h1, h2⟩ := h.gL_neg hi
    constructor
    · have : (1 : ℤ) ≤ (gL p p' r s i).1 := by rw [h1]; nlinarith
      exact_mod_cast this
    · have : (1 : ℤ) ≤ (gL p p' r s i).2 := by rw [h2]; nlinarith
      exact_mod_cast this

/-- `g_i` is a first step at level `N` exactly when `(n₁ + iN₀)² ≤ n₀² + 2N₀N`. -/
theorem Setup.gL_mem (h : Setup p p' r s) (N : ℕ) (i : ℤ) :
    gL p p' r s i ∈ firstSteps p p' N (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) ↔
      (n1 p p' r s + i * N0 p p') ^ 2 ≤ n0 p p' r s ^ 2 + 2 * N0 p p' * N := by
  have hl := lvl_eq p p' (gL p p' r s i)
  rw [h.gL_sum, h.gL_diff, mul_pow, mul_pow, sgnI_sq, one_mul, one_mul] at hl
  have hN := h.N0_pos
  rw [firstSteps, Finset.mem_filter, mem_labels_iff, h.gL_diff, mul_pow, sgnI_sq, one_mul]
  constructor
  · rintro ⟨⟨_, _, h3⟩, _⟩
    have h3' : ((gL p p' r s i).lvl : ℤ) ≤ N := by exact_mod_cast h3
    nlinarith
  · intro h3
    refine ⟨⟨(h.gL_pos i).1, (h.gL_pos i).2, ?_⟩, rfl⟩
    have h3' : ((gL p p' r s i).lvl : ℤ) ≤ N := by
      by_contra hc
      have hc := not_le.1 hc
      nlinarith
    exact_mod_cast h3'

/-- Every first step is some `g_i` (paper.tex l.1150–1153). -/
theorem Setup.firstSteps_sub (h : Setup p p' r s) (N : ℕ) {g : Label}
    (hg : g ∈ firstSteps p p' N (((p' : ℤ) * r - (p : ℤ) * s) ^ 2)) :
    ∃ i : ℤ, g = gL p p' r s i := by
  rw [firstSteps, Finset.mem_filter, mem_labels_iff] at hg
  obtain ⟨⟨hu, hv, _⟩, he⟩ := hg
  have hu' : (1 : ℤ) ≤ g.1 := by exact_mod_cast hu
  have hv' : (1 : ℤ) ≤ g.2 := by exact_mod_cast hv
  have hp : (0 : ℤ) < p := by exact_mod_cast (by have := h.hp; omega : 0 < p)
  have hr : (0 : ℤ) < r := by exact_mod_cast h.hr
  have hrp : (r : ℤ) < p := by exact_mod_cast h.hrp
  have he' : ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = ((p' : ℤ) * r + (p : ℤ) * (-(s : ℤ))) ^ 2 := by
    rw [he]
    ring
  obtain ⟨i, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := h.next_step he'
  · have hi : 0 ≤ i := by
      by_contra hc
      have hc := not_le.1 hc
      nlinarith
    refine ⟨i, Prod.ext ?_ ?_⟩
    · have := (gL_nonneg (p := p) (p' := p') (r := r) (s := s) hi).1
      exact_mod_cast h1.trans this.symm
    · have := (gL_nonneg (p := p) (p' := p') (r := r) (s := s) hi).2
      exact_mod_cast (h2.trans (by ring)).trans this.symm
  · have hi : 0 < i := by
      by_contra hc
      have hc := not_lt.1 hc
      nlinarith
    refine ⟨-i, Prod.ext ?_ ?_⟩
    · have := (h.gL_neg (by omega : -i < 0)).1
      exact_mod_cast (h1.trans (by ring)).trans this.symm
    · have := (h.gL_neg (by omega : -i < 0)).2
      exact_mod_cast (h2.trans (by ring)).trans this.symm

end Virasoro.ChainEval
