import Virasoro.Statements.Sec3
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Proofs: Section 3 (minimal-model and Ising collision classes)
-/

namespace Virasoro

/-- For coprime `p, p'` with `p ≠ 0`: `p' x = p y` iff `(x, y) = (p ℓ, p' ℓ)` for some `ℓ`. -/
theorem coprime_ratio (p p' : ℤ) (hp : p ≠ 0) (hcop : IsCoprime p p') (x y : ℤ) :
    p' * x = p * y ↔ ∃ l : ℤ, x = p * l ∧ y = p' * l := by
  constructor
  · intro h
    have hdvd : p ∣ x := hcop.dvd_of_dvd_mul_left ⟨y, h⟩
    obtain ⟨l, rfl⟩ := hdvd
    refine ⟨l, rfl, ?_⟩
    have : p * (p' * l) = p * y := by rw [← h]; ring
    exact (mul_left_cancel₀ hp this).symm
  · rintro ⟨l, rfl, rfl⟩
    ring

/-- The Diophantine classification behind Proposition 3.2. -/
theorem sq_class (p p' : ℤ) (hp : p ≠ 0) (hcop : IsCoprime p p') (r s r' s' : ℤ) :
    (p' * r - p * s) ^ 2 = (p' * r' - p * s') ^ 2 ↔
      ∃ l : ℤ, (r' = r + p * l ∧ s' = s + p' * l) ∨ (r' = p * l - r ∧ s' = p' * l - s) := by
  rw [eq_comm, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (h | h)
    · have : p' * (r' - r) = p * (s' - s) := by linarith
      obtain ⟨l, h1, h2⟩ := (coprime_ratio p p' hp hcop _ _).1 this
      exact ⟨l, Or.inl ⟨by linarith, by linarith⟩⟩
    · have : p' * (r' + r) = p * (s' + s) := by linarith
      obtain ⟨l, h1, h2⟩ := (coprime_ratio p p' hp hcop _ _).1 this
      exact ⟨l, Or.inr ⟨by linarith, by linarith⟩⟩
  · rintro ⟨l, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · left; ring
    · right; ring

/-- The Kac weight at `b² = -p'/p`. -/
theorem kacH_minimal (p p' : ℂ) (hp : p ≠ 0) (hp' : p' ≠ 0) (b : ℂ) (hb : b ^ 2 = -p' / p)
    (r s : ℂ) :
    ((b + b⁻¹) ^ 2 - (r * b + s * b⁻¹) ^ 2) / 4 =
      ((p' * r - p * s) ^ 2 - (p' - p) ^ 2) / (4 * p * p') := by
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0] at hb
    have : (-p' / p : ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hp') hp
    exact this (by rw [← hb]; simp)
  have hinv : (b⁻¹) ^ 2 = -p / p' := by
    rw [inv_pow, hb]
    field_simp
  have e1 : (b + b⁻¹) ^ 2 = b ^ 2 + 2 + (b⁻¹) ^ 2 := by
    have : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
    linear_combination 2 * this
  have e2 : (r * b + s * b⁻¹) ^ 2 = r ^ 2 * b ^ 2 + 2 * r * s + s ^ 2 * (b⁻¹) ^ 2 := by
    have : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
    linear_combination 2 * r * s * this
  rw [e1, e2, hb, hinv]
  field_simp
  ring

theorem kacC_minimal (p p' : ℂ) (hp : p ≠ 0) (hp' : p' ≠ 0) (b : ℂ) (hb : b ^ 2 = -p' / p) :
    kacC b = 1 - 6 * (p' - p) ^ 2 / (p * p') := by
  have hb0 : b ≠ 0 := by
    intro h0
    rw [h0] at hb
    have : (-p' / p : ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hp') hp
    exact this (by rw [← hb]; simp)
  have hinv : (b⁻¹) ^ 2 = -p / p' := by
    rw [inv_pow, hb]
    field_simp
  have e1 : (b + b⁻¹) ^ 2 = b ^ 2 + 2 + (b⁻¹) ^ 2 := by
    have : b * b⁻¹ = 1 := mul_inv_cancel₀ hb0
    linear_combination 2 * this
  rw [kacC, e1, hb, hinv]
  field_simp
  ring

/-- Paper label: prop:minimal-collisions -/
theorem prop_minimal_collisions : Stmt_prop_minimal_collisions := by
  intro p p' hp hp' hcop b hb
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hp'C : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp'.ne'
  have hH : ∀ r s : ℤ,
      kacH r s b = (((p' : ℂ) * r - p * s) ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p') := by
    intro r s
    exact kacH_minimal p p' hpC hp'C b hb r s
  refine ⟨kacC_minimal p p' hpC hp'C b hb, hH, ?_⟩
  intro r s r' s' _ _ _ _
  rw [hH, hH]
  have hcopZ : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hpZ : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne'
  rw [← sq_class (p : ℤ) (p' : ℤ) hpZ hcopZ r s r' s']
  have hden : (4 * (p : ℂ) * p') ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hpC) hp'C
  rw [div_left_inj' hden, sub_left_inj]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h

theorem b0_sq : b0 ^ 2 = -(4 : ℂ) / 3 := by
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have h30 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at h3
    norm_num at h3
  rw [b0, div_pow, mul_pow, Complex.I_sq, h3]
  norm_num

theorem b0_ne_zero : b0 ≠ 0 := by
  intro h
  have := b0_sq
  rw [h] at this
  norm_num at this

/-- The Ising values of Definition 3.1: `c(b₀) = 1/2` and `Δ_{r,s} = h_{r,s}(b₀)`. -/
theorem def_fixed_specialization_ising : Stmt_def_fixed_specialization_ising := by
  have hb : b0 ^ 2 = -((4 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) := by rw [b0_sq]; norm_num
  obtain ⟨hc, hH, -⟩ := prop_minimal_collisions 3 4 (by norm_num) (by norm_num) (by norm_num) b0 hb
  refine ⟨?_, ?_⟩
  · rw [hc]; norm_num
  · intro r s
    rw [hH, isingDelta]
    push_cast
    ring

theorem isingDelta_eq_iff (r s r' s' : ℤ) :
    isingDelta r s = isingDelta r' s' ↔ (4 * r - 3 * s) ^ 2 = (4 * r' - 3 * s') ^ 2 := by
  unfold isingDelta
  rw [div_left_inj' (by norm_num : (48 : ℚ) ≠ 0), sub_left_inj]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) h

theorem isingDelta_eq_lam (r s : ℤ) : isingDelta r s = isingLam (4 * r - 3 * s).natAbs := by
  unfold isingDelta isingLam
  congr 2
  have : (((4 * r - 3 * s).natAbs : ℤ) : ℚ) ^ 2 = ((4 * r - 3 * s : ℤ) : ℚ) ^ 2 := by
    rw [← Int.cast_pow, ← Int.cast_pow, Int.natAbs_sq]
  rw [Int.cast_natCast] at this
  rw [this]
  push_cast
  ring

/-- Paper label: cor:ising-classes -/
theorem cor_ising_classes : Stmt_cor_ising_classes := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r s r' s' _ _ _ _
    rw [isingDelta_eq_iff]
    have hcop : IsCoprime (3 : ℤ) (4 : ℤ) := by
      refine ⟨-1, 1, by norm_num⟩
    exact sq_class 3 4 (by norm_num) hcop r s r' s'
  · intro r s _ _
    exact isingDelta_eq_lam r s
  · ext x
    constructor
    · rintro ⟨r, s, _, _, rfl⟩
      exact ⟨_, (isingDelta_eq_lam r s).symm⟩
    · rintro ⟨n, rfl⟩
      refine ⟨(n : ℤ) + 3, (n : ℤ) + 4, by positivity, by positivity, ?_⟩
      rw [isingDelta_eq_lam]
      congr 1
      have : (4 * ((n : ℤ) + 3) - 3 * ((n : ℤ) + 4)) = (n : ℤ) := by ring
      rw [this, Int.natAbs_natCast]
  · intro r s hr hs
    have hinj : Function.Injective (fun l : ℕ => ((r + 3 * (l : ℤ), s + 4 * (l : ℤ)) : ℤ × ℤ)) := by
      intro l l' h
      simp only [Prod.mk.injEq] at h
      have := h.1
      omega
    refine Set.infinite_of_injective_forall_mem hinj ?_
    intro l
    refine ⟨by positivity, by positivity, ?_⟩
    show isingDelta (r + 3 * (l : ℤ)) (s + 4 * (l : ℤ)) = isingDelta r s
    rw [isingDelta_eq_iff]
    ring
  · intro N
    have hfin : ((Finset.Icc (1 : ℤ) N ×ˢ Finset.Icc (1 : ℤ) N).image
        fun q : ℤ × ℤ => isingDelta q.1 q.2 : Set ℚ).Finite := Finset.finite_toSet _
    refine hfin.subset ?_
    rintro x ⟨r, s, hr, hs, hrs, rfl⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_Icc, Prod.exists]
    refine ⟨r, s, ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩⟩, rfl⟩
    · nlinarith
    · nlinarith

example : Stmt_prop_minimal_collisions := prop_minimal_collisions
example : Stmt_cor_ising_classes := cor_ising_classes

end Virasoro
