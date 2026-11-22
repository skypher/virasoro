import Virasoro.Proofs.Sec6TTRoots
import Virasoro.Proofs.Sec6DDeriv

/-!
# Proposition 6.9, Case 1: `s ∈ {1, p'−1}` (paper.tex l.1448–1463)

The orders `e_± = ord_{d₁} τ^±_k` differ; extracting `[(d−d₁)^{min e}]P_N` kills the branch of
higher order and leaves a nonzero multiple of `H_{M^{min}}(c⋆, μ^{min}_k, d₁) ≠ 0`
(Proposition 6.8(iii)).
-/

namespace Virasoro

namespace TT

open Polynomial Finset

theorem d1_eq {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') :
    dQ p p' ((p' : ℤ) - 3 * p) = -1 + 2 * p / p' := by
  have h1 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have h2 : (p' : ℚ) ≠ 0 := by exact_mod_cast hp'.ne'
  rw [dQ]
  push_cast
  field_simp
  ring

theorem d2_eq {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') :
    dQ p p' ((p' : ℤ) + 3 * p) = 2 + 2 * p / p' := by
  have h1 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have h2 : (p' : ℚ) ≠ 0 := by exact_mod_cast hp'.ne'
  rw [dQ]
  push_cast
  field_simp
  ring

/-- Proposition 6.8(iii) in the rational model: `H_M(c⋆, d_m, d_ν) ≠ 0` and its `ℓ`-adic
valuation, `d₀ = d_{p'−3p}`, `d₁ = d_{p'+3p}` (`ν = 1, 2` of the paper). -/
theorem H_at (h68 : Stmt_prop_h13_nonvanishing) {p p' : ℕ} (hp : 2 ≤ p) (hp' : 2 ≤ p')
    (hcop : Nat.Coprime p p') {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ∣ p') (m : ℤ)
    {M : ℕ} (hM : 1 ≤ M) (hdet : ∀ M' ≤ M, (gram (cs p p') (dQ p p' m) M').det ≠ 0)
    (ν : Fin 2) :
    let dν : ℚ := if ν = 0 then dQ p p' ((p' : ℤ) - 3 * p) else dQ p p' ((p' : ℤ) + 3 * p)
    (HpolyD (cs p p') (dQ p p' m) M).eval dν ≠ 0 ∧
      padicValRat ℓ ((HpolyD (cs p p') (dQ p p' m) M).eval dν) =
        -(padicValNat ℓ M.factorial : ℤ) - (M : ℤ) * (padicValNat ℓ p' : ℤ)
          - ∑ u ∈ Finset.Icc 1 M, (padicValInt ℓ (m ^ 2 - ((p' : ℤ) * u - p) ^ 2) : ℤ) := by
  intro dν
  obtain ⟨P, -, -, -, h3, -⟩ := h68
  have h := h3 p p' hp hp' hcop M m hM
  simp only at h
  obtain ⟨-, hne, hval⟩ := (h (hdet M le_rfl)).2 ℓ hℓ hℓ2 hℓp ν
  have hev : ∀ d : ℚ, RatFunc.eval (RingHom.id ℚ) (dQ p p' m) (Hrat (cs p p') d M) =
      (HpolyD (cs p p') (dQ p p' m) M).eval d := by
    intro d
    rw [eval_HpolyD]
    exact evalAt_Hrat hdet
  have hd : dν = if ν = 0 then -1 + 2 * (p : ℚ) / p' else 2 + 2 * (p : ℚ) / p' := by
    simp only [dν]
    rw [d1_eq (by omega) (by omega), d2_eq (by omega) (by omega)]
  rw [hd, ← hev]
  exact ⟨hne, hval⟩

/-- Two branches of different order at `z`, each times a factor nonzero at `z`, do not cancel. -/
theorem two_branch_ne {z : ℚ} {A₁ A₂ Q₁ Q₂ G₁ G₂ : ℚ[X]} {e₁ e₂ : ℕ} (h₁ : SplitAt z A₁ e₁ Q₁)
    (h₂ : SplitAt z A₂ e₂ Q₂) (hne : e₁ ≠ e₂) (hG₁ : G₁.eval z ≠ 0) (hG₂ : G₂.eval z ≠ 0) :
    A₁ * G₁ + A₂ * G₂ ≠ 0 := by
  have hX : ∀ n : ℕ, (X - C z) ^ n ≠ 0 := fun n => pow_ne_zero n (X_sub_C_ne_zero z)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    intro h0
    have e : A₁ * G₁ + A₂ * G₂ =
        (X - C z) ^ e₁ * (Q₁ * G₁ + (X - C z) ^ (d + 1) * (Q₂ * G₂)) := by
      rw [h₁.1, h₂.1, show e₁ + d + 1 = e₁ + (d + 1) by omega, pow_add]
      ring
    rw [e] at h0
    have h1 := (mul_eq_zero.1 h0).resolve_left (hX e₁)
    have h2 := congrArg (eval z) h1
    rw [eval_add, eval_mul, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow (Nat.succ_ne_zero d), zero_mul, add_zero, eval_zero] at h2
    exact mul_ne_zero h₁.2 hG₁ h2
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    intro h0
    have e : A₁ * G₁ + A₂ * G₂ =
        (X - C z) ^ e₂ * ((X - C z) ^ (d + 1) * (Q₁ * G₁) + Q₂ * G₂) := by
      rw [h₁.1, h₂.1, show e₂ + d + 1 = e₂ + (d + 1) by omega, pow_add]
      ring
    rw [e] at h0
    have h1 := (mul_eq_zero.1 h0).resolve_left (hX e₂)
    have h2 := congrArg (eval z) h1
    simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow (Nat.succ_ne_zero d), zero_mul, zero_add, eval_zero] at h2
    exact mul_ne_zero h₂.2 hG₂ h2

theorem three_le_of_odd_prime {p' ℓ : ℕ} (hp' : 2 ≤ p') (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓp : ℓ ∣ p') : 3 ≤ p' := by
  have h1 := hℓ.two_le
  have h2 := Nat.le_of_dvd (by omega) hℓp
  omega

/-- `coreP` as a sum of the two branches, each times its factor `H/[d^k]τ`. -/
theorem coreP_eq (p p' r s k N : ℕ) :
    coreP p p' r s k N =
      tauQ p p' r s true k * (C ((tauQ p p' r s true k).coeff k)⁻¹ *
        HpolyD (cs p p') (muQ p p' r s true k) (N - ellPlus p p' r s k)) +
      tauQ p p' r s false k * (C ((-1 : ℚ) ^ k * ((tauQ p p' r s false k).coeff k)⁻¹) *
        HpolyD (cs p p') (muQ p p' r s false k) (N - ellMinus p p' r s k)) := by
  rw [coreP, map_mul]
  ring

/-- The factors `H^±(d_ν)/[d^k]τ^±` are nonzero at `d_ν`. -/
theorem branch_ne (h68 : Stmt_prop_h13_nonvanishing) {p p' r s k N : ℕ}
    (hyp : CoreHyp p p' r s k N) (ε : Bool) (ν : Fin 2) :
    (C ((if ε then 1 else (-1 : ℚ) ^ k) * ((tauQ p p' r s ε k).coeff k)⁻¹) *
      HpolyD (cs p p') (muQ p p' r s ε k) (N - ellOrb p p' r s ε k)).eval
        (if ν = 0 then dQ p p' ((p' : ℤ) - 3 * p) else dQ p p' ((p' : ℤ) + 3 * p)) ≠ 0 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, ⟨ℓ, hℓ, hℓ2, hℓp⟩, hk, hN1, hN2, hdet, hc0, hck⟩ :=
    hyp
  have hM : 1 ≤ N - ellOrb p p' r s ε k := by
    cases ε
    · rw [ellOrb_false hk]
      have := le_max_right (ellPlus p p' r s k) (ellMinus p p' r s k)
      omega
    · rw [ellOrb_true hk]
      have := le_max_left (ellPlus p p' r s k) (ellMinus p p' r s k)
      omega
  have hH := (H_at h68 hp hp' hcop hℓ hℓ2 hℓp (nOrb p p' r s ε k) hM (hdet ε) ν).1
  rw [eval_mul, eval_C]
  refine mul_ne_zero (mul_ne_zero ?_ (inv_ne_zero (hck ε))) hH
  split_ifs <;> simp

/-- Proposition 6.9, Case 1 (paper.tex l.1448–1463). -/
theorem core_case1 (h68 : Stmt_prop_h13_nonvanishing) {p p' r s k N : ℕ}
    (hyp : CoreHyp p p' r s k N) (hs1 : s = 1 ∨ s = p' - 1) : coreP p p' r s k N ≠ 0 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, ⟨ℓ, hℓ, hℓ2, hℓp⟩, hk, hN1, hN2, hdet, hc0, hck⟩ :=
    id hyp
  have hp3 := three_le_of_odd_prime hp' hℓ hℓ2 hℓp
  obtain ⟨Q₁, hQ₁⟩ := tau_split_d1 hp hp3 hcop hr hrp hs hsp true hk
  obtain ⟨Q₂, hQ₂⟩ := tau_split_d1 hp hp3 hcop hr hrp hs hsp false hk
  have hG₁ := branch_ne h68 hyp true 0
  have hG₂ := branch_ne h68 hyp false 0
  simp only [if_true, Bool.false_eq_true, if_false, one_mul, ellOrb_true hk,
    ellOrb_false hk] at hG₁ hG₂
  rw [coreP_eq]
  refine two_branch_ne hQ₁ hQ₂ ?_ hG₁ hG₂
  by_cases hodd : k % 2 = 1
  · have h1 : e1 p' s true k = k - 1 + (if 2 ≤ s then 1 else 0) := by
      rw [e1, if_pos (Or.inl ⟨hodd, rfl⟩)]
    have h2 : e1 p' s false k = k - 1 + (if s + 2 ≤ p' then 1 else 0) := by
      rw [e1, if_neg (show ¬((k % 2 = 1 ∧ false = true) ∨ (k % 2 = 0 ∧ false = false)) by
        simp [hodd])]
    rw [h1, h2]
    rcases hs1 with rfl | rfl <;> split_ifs <;> omega
  · have h1 : e1 p' s true k = k - 1 + (if s + 2 ≤ p' then 1 else 0) := by
      rw [e1, if_neg (show ¬((k % 2 = 1 ∧ true = true) ∨ (k % 2 = 0 ∧ true = false)) by
        simp [hodd])]
    have h2 : e1 p' s false k = k - 1 + (if 2 ≤ s then 1 else 0) := by
      rw [e1, if_pos (Or.inr ⟨by omega, rfl⟩)]
    rw [h1, h2]
    rcases hs1 with rfl | rfl <;> split_ifs <;> omega

end TT

end Virasoro
