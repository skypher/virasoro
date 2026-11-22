import Virasoro.Proofs.Sec6H13ChainWard
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Proposition 6.8(ii): the second `𝔰𝔩₂` identity (paper.tex l.1342–1343)

`L_1^r L_{−1}^b = ∑_k C(r,k) (b!/(b−k)!) L_{−1}^{b−k} (∏_{u<k}(2L_0 + b + r − k − 1 − u)) L_1^{r−k}`,
by induction on the exponent `r`.  It is proved in a ring with elements `E`, `F`, `K` such that
`EF = FE + K`, `KF = F(K+2)`, `EK = (K+2)E` (`H13C.sl2_normal_order`), and holds in `VirEnv R c`
with `E = L_1`, `F = L_{−1}`, `K = 2L_0` (`H13C.L1_pow_mul_Lm1_pow`).  The products of the
commuting factors `2L_0 + s` are values `q(K)` of polynomials `q ∈ ℤ[X]`.
-/

namespace Virasoro.H13C

open Polynomial Finset

section Abstract

variable {A : Type*} [Ring A] {E F K : A}

theorem aeval_mul_F (hKF : K * F = F * (K + 2)) (q : ℤ[X]) :
    aeval K q * F = F * aeval K (q.comp (X + 2)) := by
  have e : aeval K (X + 2 : ℤ[X]) = K + 2 := by rw [map_add, aeval_X, map_ofNat]
  refine Polynomial.induction_on q (fun a => ?_) (fun p q hp hq => ?_) (fun n a ih => ?_)
  · rw [C_comp, aeval_C]
    exact Algebra.commutes a F
  · rw [add_comp, map_add, map_add, add_mul, mul_add, hp, hq]
  · have hL : aeval K (C a * X ^ (n + 1)) = aeval K (C a * X ^ n) * K := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    have hR : aeval K ((C a * X ^ (n + 1)).comp (X + 2)) =
        aeval K ((C a * X ^ n).comp (X + 2)) * (K + 2) := by
      rw [pow_succ, ← mul_assoc, mul_comp, X_comp, map_mul, e]
    rw [hL, hR, mul_assoc, hKF, ← mul_assoc, ih, mul_assoc]

theorem E_mul_aeval (hEK : E * K = (K + 2) * E) (q : ℤ[X]) :
    E * aeval K q = aeval K (q.comp (X + 2)) * E := by
  have e : aeval K (X + 2 : ℤ[X]) = K + 2 := by rw [map_add, aeval_X, map_ofNat]
  refine Polynomial.induction_on q (fun a => ?_) (fun p q hp hq => ?_) (fun n a ih => ?_)
  · rw [C_comp, aeval_C]
    exact (Algebra.commutes a E).symm
  · rw [add_comp, map_add, map_add, add_mul, mul_add, hp, hq]
  · have hL : aeval K (C a * X ^ (n + 1)) = aeval K (C a * X ^ n) * K := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    have hR : aeval K ((C a * X ^ (n + 1)).comp (X + 2)) =
        aeval K ((C a * X ^ n).comp (X + 2)) * (K + 2) := by
      rw [pow_succ, ← mul_assoc, mul_comp, X_comp, map_mul, e]
    rw [hL, hR, ← mul_assoc, ih, mul_assoc, hEK, mul_assoc]

/-- `E F^{n+1} = F^{n+1} E + (n+1) F^n (K + n)`. -/
theorem E_mul_F_pow (hEF : E * F = F * E + K) (hKF : K * F = F * (K + 2)) (n : ℕ) :
    E * F ^ (n + 1) = F ^ (n + 1) * E + (n + 1) • (F ^ n * K) + (n * (n + 1)) • F ^ n := by
  induction n with
  | zero => simp [hEF]
  | succ n ih =>
    have h1 : F ^ (n + 1) * E * F = F ^ (n + 1 + 1) * E + F ^ (n + 1) * K := by
      rw [mul_assoc, hEF, mul_add, ← mul_assoc, ← pow_succ]
    have h3 : F ^ n * F = F ^ (n + 1) := (pow_succ F n).symm
    have h2 : F ^ n * K * F = F ^ (n + 1) * K + 2 • F ^ (n + 1) := by
      rw [mul_assoc, hKF, ← mul_assoc, h3, mul_add, mul_two, two_nsmul]
    have hl : E * F ^ (n + 1 + 1) = E * F ^ (n + 1) * F := by rw [pow_succ F (n + 1), mul_assoc]
    rw [hl, ih, add_mul, add_mul, smul_mul_assoc, smul_mul_assoc, h1, h2, h3]
    module

/-- `E F^n = F^n E + n F^{n−1} (K + n − 1)`, with `K + n − 1` the value of `X + (n − 1)`. -/
theorem E_mul_F_pow_aeval (hEF : E * F = F * E + K) (hKF : K * F = F * (K + 2)) (n : ℕ) :
    E * F ^ n = F ^ n * E + n • (F ^ (n - 1) * aeval K (X + C ((n : ℤ) - 1) : ℤ[X])) := by
  cases n with
  | zero => simp
  | succ n =>
    have e : aeval K (X + C (((n + 1 : ℕ) : ℤ) - 1) : ℤ[X]) = K + (n : A) := by simp
    have e2 : F ^ n * (n : A) = n • F ^ n := (nsmul_eq_mul' _ _).symm
    rw [E_mul_F_pow hEF hKF, Nat.add_sub_cancel, e, mul_add (F ^ n) K (n : A), e2]
    module

/-- `q_{r,k} = ∏_{u<k}(X + b + r − k − 1 − u)`. -/
noncomputable def qPoly (b r k : ℕ) : ℤ[X] :=
  ∏ u ∈ range k, (X + C ((b : ℤ) + r - k - 1 - u))

theorem qPoly_comp_succ (b r k : ℕ) :
    (qPoly b r (k + 1)).comp (X + 2) = qPoly b r k * (X + C ((b : ℤ) + r - k)) := by
  rw [qPoly, Polynomial.prod_comp, prod_range_succ', qPoly]
  congr 1
  · refine prod_congr rfl fun u _ => ?_
    rw [add_comp, X_comp, C_comp, add_assoc]
    congr 1
    rw [show (2 : ℤ[X]) = C 2 from rfl, ← C_add]
    congr 1
    push_cast
    ring
  · rw [add_comp, X_comp, C_comp, add_assoc]
    congr 1
    rw [show (2 : ℤ[X]) = C 2 from rfl, ← C_add]
    congr 1
    push_cast
    ring

theorem qPoly_succ_succ (b r k : ℕ) :
    qPoly b (r + 1) (k + 1) = qPoly b r k * (X + C ((b : ℤ) + r - k - 1 - k)) := by
  rw [qPoly, prod_range_succ, qPoly]
  congr 1
  · refine prod_congr rfl fun u _ => ?_
    congr 2
    push_cast
    ring
  · congr 2
    push_cast
    ring

/-- The identity of coefficients behind the induction step: `C(r,k+1)(k+1) = C(r,k)(r−k)`. -/
theorem qPoly_step (b r k : ℕ) (hk : k ≤ r) :
    (r.choose (k + 1) * b.descFactorial (k + 1)) • (qPoly b r (k + 1)).comp (X + 2) +
      (r.choose k * b.descFactorial k * (b - k)) •
        ((X + C (((b - k : ℕ) : ℤ) - 1)) * qPoly b r k) =
      ((r + 1).choose (k + 1) * b.descFactorial (k + 1)) • qPoly b (r + 1) (k + 1) := by
  rcases Nat.lt_or_ge k b with hkb | hkb
  · have hd : b.descFactorial (k + 1) = (b - k) * b.descFactorial k := Nat.descFactorial_succ b k
    have hc : (r.choose (k + 1) : ℤ[X]) * ((k : ℤ[X]) + 1) =
        (r.choose k : ℤ[X]) * ((r : ℤ[X]) - k) := by
      have h := Nat.choose_succ_right_eq r k
      have h' : ((r.choose (k + 1) * (k + 1) : ℕ) : ℤ[X]) = ((r.choose k * (r - k) : ℕ) : ℤ[X]) :=
        congrArg _ h
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk] at h'
      push_cast at h'
      exact h'
    rw [qPoly_comp_succ, qPoly_succ_succ, Nat.choose_succ_succ, hd, nsmul_eq_mul, nsmul_eq_mul,
      nsmul_eq_mul]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hkb.le, map_add, map_sub, map_natCast,
      map_one]
    linear_combination (((b : ℤ[X]) - k) * (b.descFactorial k : ℤ[X]) * qPoly b r k) * hc
  · have hd : b.descFactorial (k + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    have hbk : b - k = 0 := Nat.sub_eq_zero_of_le hkb
    rw [hd, hbk, mul_zero, mul_zero, mul_zero, zero_smul, zero_smul, zero_smul, add_zero]

/-- The summand `F^{b−k} q_{r,k}(K) E^{r−k}`. -/
noncomputable def sl2Term (E F K : A) (b r k : ℕ) : A :=
  F ^ (b - k) * aeval K (qPoly b r k) * E ^ (r - k)

theorem E_mul_sl2Term (hEF : E * F = F * E + K) (hKF : K * F = F * (K + 2))
    (hEK : E * K = (K + 2) * E) (b r k : ℕ) (hk : k ≤ r) :
    E * sl2Term E F K b r k =
      F ^ (b - k) * aeval K ((qPoly b r k).comp (X + 2)) * E ^ (r + 1 - k) +
      (b - k) • (F ^ (b - (k + 1)) *
        aeval K ((X + C (((b - k : ℕ) : ℤ) - 1)) * qPoly b r k) * E ^ (r + 1 - (k + 1))) := by
  have e1 : r + 1 - k = r - k + 1 := Nat.succ_sub hk
  have e2 : r + 1 - (k + 1) = r - k := Nat.add_sub_add_right r 1 k
  have e3 : b - (k + 1) = b - k - 1 := rfl
  rw [sl2Term, ← mul_assoc, ← mul_assoc, E_mul_F_pow_aeval hEF hKF, add_mul, add_mul, e1, e2, e3,
    mul_assoc (F ^ (b - k)) E, E_mul_aeval hEK, pow_succ', map_mul, smul_mul_assoc,
    smul_mul_assoc]
  simp only [mul_assoc]

/-- `E^r F^b = ∑_k C(r,k) (b!/(b−k)!) F^{b−k} (∏_{u<k}(K + b + r − k − 1 − u)) E^{r−k}`
(paper.tex l.1342–1343, with `K = 2L_0`). -/
theorem sl2_normal_order (hEF : E * F = F * E + K) (hKF : K * F = F * (K + 2))
    (hEK : E * K = (K + 2) * E) (b r : ℕ) :
    E ^ r * F ^ b =
      ∑ k ∈ range (r + 1), (r.choose k * b.descFactorial k) • sl2Term E F K b r k := by
  induction r with
  | zero => simp [sl2Term, qPoly]
  | succ r ih =>
    have hstep : ∀ k ∈ range (r + 1), E * ((r.choose k * b.descFactorial k) • sl2Term E F K b r k) =
        (r.choose k * b.descFactorial k) •
          (F ^ (b - k) * aeval K ((qPoly b r k).comp (X + 2)) * E ^ (r + 1 - k)) +
        (r.choose k * b.descFactorial k * (b - k)) • (F ^ (b - (k + 1)) *
          aeval K ((X + C (((b - k : ℕ) : ℤ) - 1)) * qPoly b r k) * E ^ (r + 1 - (k + 1))) := by
      intro k hk
      rw [mul_smul_comm, E_mul_sl2Term hEF hKF hEK b r k (Nat.lt_succ_iff.1 (mem_range.1 hk)),
        smul_add, smul_smul]
    rw [pow_succ', mul_assoc, ih, mul_sum, sum_congr rfl hstep, sum_add_distrib,
      sum_range_succ' _ (r + 1), sum_range_succ' _ r]
    have hlast : ∑ k ∈ range r, (r.choose (k + 1) * b.descFactorial (k + 1)) •
        (F ^ (b - (k + 1)) * aeval K ((qPoly b r (k + 1)).comp (X + 2)) * E ^ (r + 1 - (k + 1))) =
        ∑ k ∈ range (r + 1), (r.choose (k + 1) * b.descFactorial (k + 1)) •
        (F ^ (b - (k + 1)) * aeval K ((qPoly b r (k + 1)).comp (X + 2)) *
          E ^ (r + 1 - (k + 1))) := by
      rw [sum_range_succ _ r, Nat.choose_succ_self, zero_mul, zero_smul, add_zero]
    have hcomb : ∀ k ∈ range (r + 1),
        (r.choose (k + 1) * b.descFactorial (k + 1)) •
          (F ^ (b - (k + 1)) * aeval K ((qPoly b r (k + 1)).comp (X + 2)) *
            E ^ (r + 1 - (k + 1))) +
        (r.choose k * b.descFactorial k * (b - k)) • (F ^ (b - (k + 1)) *
          aeval K ((X + C (((b - k : ℕ) : ℤ) - 1)) * qPoly b r k) * E ^ (r + 1 - (k + 1))) =
        ((r + 1).choose (k + 1) * b.descFactorial (k + 1)) • sl2Term E F K b (r + 1) (k + 1) := by
      intro k hk
      have hq := congrArg (aeval K) (qPoly_step b r k (Nat.lt_succ_iff.1 (mem_range.1 hk)))
      rw [map_add, map_nsmul, map_nsmul, map_nsmul] at hq
      rw [sl2Term]
      calc _ = F ^ (b - (k + 1)) * ((r.choose (k + 1) * b.descFactorial (k + 1)) •
              aeval K ((qPoly b r (k + 1)).comp (X + 2)) +
            (r.choose k * b.descFactorial k * (b - k)) •
              aeval K ((X + C (((b - k : ℕ) : ℤ) - 1)) * qPoly b r k)) * E ^ (r + 1 - (k + 1)) := by
            simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [hq, mul_smul_comm, smul_mul_assoc]
    rw [hlast, add_right_comm, ← sum_add_distrib, sum_congr rfl hcomb]
    simp [sl2Term, qPoly]

end Abstract

/-! ### Commuting a power past an element from the right (l.1334–1335) -/

section Mirror

variable {A : Type*} [Ring A]

/-- `(−ad(x))^q (X)`, with `−ad(x)(Z) = Zx − xZ`. -/
def nadp (x : A) (q : ℕ) (X : A) : A := (fun Z => Z * x - x * Z)^[q] X

theorem nadp_succ (x : A) (q : ℕ) (X : A) :
    nadp x (q + 1) X = nadp x q X * x - x * nadp x q X :=
  Function.iterate_succ_apply' _ _ _

/-- `X x^a = ∑_q C(a,q) x^{a−q} (−ad(x))^q(X)`: right multiplication by `x` is left
multiplication by `x` plus `−ad(x)`, and these two commute. -/
theorem mul_pow_eq_sum_nad (x X : A) (a : ℕ) :
    X * x ^ a = ∑ q ∈ range (a + 1), a.choose q • (x ^ (a - q) * nadp x q X) := by
  have hc : Commute (LinearMap.mulRight ℤ x - LinearMap.mulLeft ℤ x) (LinearMap.mulLeft ℤ x) :=
    (LinearMap.commute_mulLeft_right x x).symm.sub_left (Commute.refl _)
  have hR : ∀ (n : ℕ) (Z : A), (LinearMap.mulRight ℤ x ^ n) Z = Z * x ^ n := by
    intro n
    induction n with
    | zero => intro Z; simp
    | succ n ih =>
      intro Z
      rw [pow_succ, Module.End.mul_apply, LinearMap.mulRight_apply, ih, pow_succ', mul_assoc]
  have hL : ∀ (n : ℕ) (Z : A), (LinearMap.mulLeft ℤ x ^ n) Z = x ^ n * Z := by
    intro n
    induction n with
    | zero => intro Z; simp
    | succ n ih =>
      intro Z
      rw [pow_succ, Module.End.mul_apply, LinearMap.mulLeft_apply, ih, pow_succ, mul_assoc]
  have hD : ∀ n : ℕ, ((LinearMap.mulRight ℤ x - LinearMap.mulLeft ℤ x) ^ n) X = nadp x n X := by
    intro n
    induction n with
    | zero => simp [nadp]
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, nadp_succ, LinearMap.sub_apply,
        LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  have h := hc.add_pow a
  rw [sub_add_cancel] at h
  have h2 := congrArg (fun f : Module.End ℤ A => f X) h
  simp only [LinearMap.sum_apply] at h2
  rw [hR] at h2
  rw [h2]
  refine sum_congr rfl fun q _ => ?_
  rw [(hc.pow_pow q (a - q)).eq, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.natCast_apply, map_nsmul, map_nsmul, hL, hD]

end Mirror

/-! ### In the enveloping algebra -/

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `L_1^r L_{−1}^b` in normal order (paper.tex l.1342–1343). -/
theorem L1_pow_mul_Lm1_pow (c : R) (b r : ℕ) :
    VirEnv.L c 1 ^ r * VirEnv.L c (-1) ^ b =
      ∑ k ∈ range (r + 1), (r.choose k * b.descFactorial k) •
        sl2Term (VirEnv.L c 1) (VirEnv.L c (-1)) (2 * VirEnv.L c 0) b r k := by
  have h10 : VirEnv.L c 1 * VirEnv.L c 0 = VirEnv.L c 0 * VirEnv.L c 1 + VirEnv.L c 1 := by
    rw [VirEnv.L_mul_L, if_neg (by decide), add_zero]
    congr 1
    have e : ((1 - 0 : ℤ) : R) = 1 := by norm_num
    rw [e]
    exact one_smul R _
  have h0m : VirEnv.L c 0 * VirEnv.L c (-1) = VirEnv.L c (-1) * VirEnv.L c 0 + VirEnv.L c (-1) := by
    rw [VirEnv.L_mul_L, if_neg (by decide), add_zero]
    congr 1
    have e : ((0 - -1 : ℤ) : R) = 1 := by norm_num
    rw [e]
    exact one_smul R _
  have h1m : VirEnv.L c 1 * VirEnv.L c (-1) =
      VirEnv.L c (-1) * VirEnv.L c 1 + 2 * VirEnv.L c 0 := by
    rw [VirEnv.L_mul_L, if_pos (by decide), centralTerm_one, map_zero, add_zero]
    congr 1
    have e : ((1 - -1 : ℤ) : R) = 2 := by norm_num
    rw [e, two_mul]
    exact two_smul R _
  refine sl2_normal_order h1m ?_ ?_ b r
  · rw [two_mul, add_mul, h0m, mul_add, mul_add, mul_two]
    abel
  · rw [two_mul, mul_add, h10, add_mul, add_mul, two_mul]
    abel

end Virasoro.H13C
