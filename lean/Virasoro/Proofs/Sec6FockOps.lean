import Virasoro.NormalOrder
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The Fock module `𝓕(α)` of Proposition 6.8(i) (paper.tex l.1261–1264)

The space is `R[x₁, x₂, …]` for a commutative `ℚ`-algebra `R` holding `q₀` and `α`.  The
Heisenberg modes act by `a_{-n} = x_n ·`, `a_n = n ∂/∂x_n` (`n ≥ 1`), `a_0 = α`, so that
`[a_m, a_n] = m δ_{m+n,0}`, and
`L_n = ½ ∑_k :a_k a_{n-k}: − q₀ (n+1) a_n`.
The normally ordered sum is split into the terms with one creation and one annihilation mode
(a derivation of the polynomial ring), the two terms with a zero mode, and the finitely many
terms with two modes of the same sign.

This file proves `[L_n, a_m] = −m a_{n+m} − q₀ n(n+1) δ_{n+m,0}`.
-/

namespace Virasoro.TFock

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- `ℤ → ℕ+`, the identity on positive integers. -/
def pn (n : ℤ) : ℕ+ := n.toNat.toPNat'

theorem pn_coe (j : ℕ+) : pn ((j : ℕ) : ℤ) = j := by simp [pn]

theorem coe_pn {n : ℤ} (h : 0 < n) : (((pn n : ℕ+) : ℕ) : ℤ) = n := by
  unfold pn
  rw [PNat.toPNat'_coe (by omega)]
  omega

/-- The Heisenberg mode `a_n` on `𝓕(α)`. -/
noncomputable def hOp (al : R) (n : ℤ) : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R :=
  if 0 < n then (n : R) • (pderiv (pn n) : Derivation R (MvPolynomial ℕ+ R) _).toLinearMap
  else if n = 0 then al • LinearMap.id
  else LinearMap.mulLeft R (X (pn (-n)))

theorem hOp_pos (al : R) {n : ℤ} (h : 0 < n) (f : MvPolynomial ℕ+ R) :
    hOp al n f = (n : R) • pderiv (pn n) f := by
  unfold hOp
  rw [if_pos h]
  rfl

theorem hOp_zero (al : R) (f : MvPolynomial ℕ+ R) : hOp al 0 f = al • f := by
  unfold hOp
  rw [if_neg (lt_irrefl 0), if_pos rfl]
  rfl

theorem hOp_neg (al : R) {n : ℤ} (h : n < 0) (f : MvPolynomial ℕ+ R) :
    hOp al n f = X (pn (-n)) * f := by
  unfold hOp
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

theorem hOp_neg_coe (al : R) (j : ℕ+) (f : MvPolynomial ℕ+ R) :
    hOp al (-((j : ℕ) : ℤ)) f = X j * f := by
  have hj : (0 : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast j.pos
  rw [hOp_neg al (by omega), neg_neg, pn_coe]

theorem hOp_one_pos (al : R) {n : ℤ} (h : 0 < n) : hOp al n (1 : MvPolynomial ℕ+ R) = 0 := by
  rw [hOp_pos al h]
  simp

/-- `[a_l, x_j] = j δ_{l,j}`. -/
theorem hOp_X (al : R) (l : ℤ) (j : ℕ+) (f : MvPolynomial ℕ+ R) :
    hOp al l (X j * f) =
      X j * hOp al l f + (if l = ((j : ℕ) : ℤ) then ((j : ℕ) : R) • f else 0) := by
  have hj : (0 : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast j.pos
  by_cases hl : 0 < l
  · rw [hOp_pos al hl, hOp_pos al hl, Derivation.leibniz, pderiv_X]
    by_cases h : l = ((j : ℕ) : ℤ)
    · have hpn : pn l = j := by rw [h, pn_coe]
      have hc : (l : R) = ((j : ℕ) : R) := by rw [h]; push_cast; rfl
      rw [if_pos h, hpn, Pi.single_eq_same, hc]
      simp only [smul_eq_C_mul, smul_eq_mul]
      ring
    · have hpn : j ≠ pn l := by
        intro h'
        apply h
        rw [h', coe_pn hl]
      rw [if_neg h, Pi.single_eq_of_ne hpn]
      simp only [smul_eq_C_mul, smul_eq_mul]
      ring
  · have hne : l ≠ ((j : ℕ) : ℤ) := by omega
    rw [if_neg hne, add_zero]
    by_cases h0 : l = 0
    · subst h0
      rw [hOp_zero, hOp_zero, mul_smul_comm]
    · rw [hOp_neg al (by omega), hOp_neg al (by omega)]
      ring

/-- An operator that commutes with every `x_j` and kills `1` is zero. -/
theorem op_ext (T : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R)
    (hX : ∀ (j : ℕ+) (f : MvPolynomial ℕ+ R), T (X j * f) = X j * T f) (h1 : T 1 = 0)
    (f : MvPolynomial ℕ+ R) : T f = 0 := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have : (C a : MvPolynomial ℕ+ R) = a • (1 : MvPolynomial ℕ+ R) := by
      rw [smul_eq_C_mul, mul_one]
    rw [this, map_smul, h1, smul_zero]
  | add p q hp hq => rw [map_add, hp, hq, add_zero]
  | mul_X p j hp => rw [mul_comm, hX, hp, mul_zero]

/-- The Heisenberg relations `[a_k, a_l] = k δ_{k+l,0}`. -/
theorem hOp_comm (al : R) (k l : ℤ) (f : MvPolynomial ℕ+ R) :
    hOp al k (hOp al l f) = hOp al l (hOp al k f) + (if k + l = 0 then (k : R) • f else 0) := by
  rcases lt_trichotomy l 0 with hl | hl | hl
  · have e : l = -(((pn (-l) : ℕ+) : ℕ) : ℤ) := by rw [coe_pn (by omega)]; ring
    have hc : (((pn (-l) : ℕ+) : ℕ) : R) = (k : R) ∨ k + l ≠ 0 := by
      by_cases h : k + l = 0
      · left
        have : k = (((pn (-l) : ℕ+) : ℕ) : ℤ) := by rw [coe_pn (by omega)]; omega
        rw [this]
        push_cast
        rfl
      · right; exact h
    rw [hOp_neg al hl, hOp_neg al hl, hOp_X]
    congr 1
    by_cases h : k + l = 0
    · rw [if_pos h, if_pos (by rw [coe_pn (by omega)]; omega)]
      rcases hc with hc | hc
      · rw [hc]
      · exact absurd h hc
    · rw [if_neg h, if_neg (by rw [coe_pn (by omega)]; omega)]
  · subst hl
    rw [hOp_zero, hOp_zero, map_smul, add_zero]
    by_cases h : k = 0
    · subst h; simp
    · rw [if_neg h, add_zero]
  · rcases lt_trichotomy k 0 with hk | hk | hk
    · rw [hOp_neg al hk, hOp_neg al hk, hOp_X]
      by_cases h : k + l = 0
      · have hl' : l = (((pn (-k) : ℕ+) : ℕ) : ℤ) := by rw [coe_pn (by omega)]; omega
        have hc : (((pn (-k) : ℕ+) : ℕ) : R) = -(k : R) := by
          have : (((pn (-k) : ℕ+) : ℕ) : ℤ) = -k := coe_pn (by omega)
          have h2 := congrArg (Int.cast : ℤ → R) this
          push_cast at h2
          exact h2
        rw [if_pos h, if_pos hl', hc]
        simp only [smul_eq_C_mul, map_neg]
        ring
      · rw [if_neg h, if_neg (by rw [coe_pn (by omega)]; omega)]
        ring
    · subst hk
      rw [hOp_zero, hOp_zero, map_smul, if_neg (by omega), add_zero]
    · rw [if_neg (by omega), add_zero]
      have key := op_ext (hOp al k ∘ₗ hOp al l - hOp al l ∘ₗ hOp al k) (fun j g => by
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, hOp_X, map_add]
        have e1 : hOp al k (if l = ((j : ℕ) : ℤ) then ((j : ℕ) : R) • g else 0) =
            if l = ((j : ℕ) : ℤ) then ((j : ℕ) : R) • hOp al k g else 0 := by
          split_ifs <;> simp
        have e2 : hOp al l (if k = ((j : ℕ) : ℤ) then ((j : ℕ) : R) • g else 0) =
            if k = ((j : ℕ) : ℤ) then ((j : ℕ) : R) • hOp al l g else 0 := by
          split_ifs <;> simp
        rw [e1, e2]
        ring) (by
        simp only [LinearMap.sub_apply, LinearMap.comp_apply, hOp_one_pos al hl,
          hOp_one_pos al hk, map_zero, sub_zero]) f
      simp only [LinearMap.sub_apply, LinearMap.comp_apply] at key
      exact sub_eq_zero.1 key

/-- `a_m` applied to a scalar multiple. -/
theorem hOp_ite (al : R) (m : ℤ) (P : Prop) [Decidable P] (g : MvPolynomial ℕ+ R) :
    hOp al m (if P then g else 0) = if P then hOp al m g else 0 := by
  split_ifs <;> simp

/-- The derivation `∑_{k ≥ 1, n+k ≥ 1} a_{-k} a_{n+k}`: `x_j ↦ j x_{j-n}` for `j > n`. -/
noncomputable def dOp (n : ℤ) : Derivation R (MvPolynomial ℕ+ R) (MvPolynomial ℕ+ R) :=
  mkDerivation R fun j : ℕ+ =>
    if n < ((j : ℕ) : ℤ) then ((j : ℕ) : R) • X (pn (((j : ℕ) : ℤ) - n)) else 0

theorem dOp_X_mul (n : ℤ) (j : ℕ+) (f : MvPolynomial ℕ+ R) :
    dOp n (X j * f) = X j * dOp n f +
      (if n < ((j : ℕ) : ℤ) then ((j : ℕ) : R) • (X (pn (((j : ℕ) : ℤ) - n)) * f) else 0) := by
  rw [Derivation.leibniz, dOp, mkDerivation_X]
  split_ifs
  · simp only [smul_eq_C_mul, smul_eq_mul]
    ring
  · simp

variable [Algebra ℚ R]

variable (R) in
/-- `1/2 ∈ R`. -/
noncomputable def half : R := algebraMap ℚ R (1 / 2)

theorem two_mul_half : (2 : R) * half R = 1 := by
  unfold half
  rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
  norm_num

/-- The terms of `L_n` with a zero mode: `(α − q₀(n+1)) a_n` for `n ≠ 0`, and `½α² − q₀α`. -/
noncomputable def zOp (al q : R) (n : ℤ) : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R :=
  if n = 0 then (half R * al ^ 2 - q * al) • LinearMap.id
  else (al - q * ((n : R) + 1)) • hOp al n

/-- The terms of `∑_k a_k a_{n-k}` with both modes of the sign of `n`. -/
noncomputable def qOp (al : R) (n : ℤ) : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R :=
  ∑ k ∈ Finset.Ioo (min n 0) (max n 0), hOp al k ∘ₗ hOp al (n - k)

/-- `L_n = ½ ∑_k :a_k a_{n-k}: − q₀ (n+1) a_n` on `𝓕(α)` (paper.tex l.1263). -/
noncomputable def LOp (al q : R) (n : ℤ) : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R :=
  ((dOp n : Derivation R (MvPolynomial ℕ+ R) (MvPolynomial ℕ+ R)) :
    MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R) + zOp al q n + half R • qOp al n

theorem LOp_apply (al q : R) (n : ℤ) (f : MvPolynomial ℕ+ R) :
    LOp al q n f = dOp n f + zOp al q n f + half R • qOp al n f := rfl

omit [Algebra ℚ R] in
theorem qOp_apply (al : R) (n : ℤ) (f : MvPolynomial ℕ+ R) :
    qOp al n f = ∑ k ∈ Finset.Ioo (min n 0) (max n 0), hOp al k (hOp al (n - k) f) := by
  simp [qOp, LinearMap.sum_apply]

theorem zOp_X (al q : R) (n : ℤ) (j : ℕ+) (f : MvPolynomial ℕ+ R) :
    zOp al q n (X j * f) = X j * zOp al q n f +
      (if n = ((j : ℕ) : ℤ) then ((al - q * ((n : R) + 1)) * ((j : ℕ) : R)) • f else 0) := by
  have hj : (0 : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast j.pos
  unfold zOp
  by_cases h0 : n = 0
  · rw [if_pos h0, if_neg (by omega), add_zero]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, mul_smul_comm]
  · rw [if_neg h0]
    simp only [LinearMap.smul_apply, hOp_X]
    split_ifs
    · simp only [smul_eq_C_mul, map_mul]
      ring
    · simp only [smul_eq_C_mul, add_zero]
      ring

theorem qOp_X (al : R) (n : ℤ) (j : ℕ+) (f : MvPolynomial ℕ+ R) :
    qOp al n (X j * f) = X j * qOp al n f +
      (if ((j : ℕ) : ℤ) < n then ((2 : R) * ((j : ℕ) : R)) • hOp al (n - ((j : ℕ) : ℤ)) f
        else 0) := by
  have hj : (0 : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast j.pos
  rw [qOp_apply, qOp_apply, Finset.mul_sum]
  have h1 : ∀ k ∈ Finset.Ioo (min n 0) (max n 0), hOp al k (hOp al (n - k) (X j * f)) =
      X j * hOp al k (hOp al (n - k) f) +
        ((if k = ((j : ℕ) : ℤ) then ((j : ℕ) : R) • hOp al (n - k) f else 0) +
         (if k = n - ((j : ℕ) : ℤ) then ((j : ℕ) : R) • hOp al k f else 0)) := by
    intro k _
    rw [hOp_X, map_add, hOp_X, hOp_ite, map_smul]
    have : (n - k = ((j : ℕ) : ℤ)) ↔ (k = n - ((j : ℕ) : ℤ)) := by omega
    rw [if_congr this rfl rfl]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  congr 1
  by_cases h : ((j : ℕ) : ℤ) < n
  · rw [if_pos h, if_pos (by rw [Finset.mem_Ioo]; omega), if_pos (by rw [Finset.mem_Ioo]; omega)]
    rw [← add_smul]
    congr 1
    ring
  · rw [if_neg h, if_neg (by rw [Finset.mem_Ioo]; omega), if_neg (by rw [Finset.mem_Ioo]; omega),
      add_zero]

end Virasoro.TFock
