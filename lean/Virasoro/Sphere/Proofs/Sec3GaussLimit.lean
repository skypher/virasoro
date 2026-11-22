import Virasoro.Sphere.Proofs.Sec3LamInfty
import Virasoro.Proofs.LargeWeight
import Virasoro.Proofs.EvalLemmas

/-!
# Limits along `λ → +∞` of rational functions regular at `λ = ∞`

sphere/paper.tex l.546–553, l.680–682: the limit (3.5) is taken coefficient by coefficient in
`z`, and each coefficient is a rational function of `λ`.  A rational function that is regular at
`λ = ∞` converges along real `λ → +∞` to the constant term of its expansion in `t = 1/λ`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset Filter Topology

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩

theorem regVal_sum {α : Type*} {s : Finset α} {f : α → LL} {v : α → ℂ}
    (h : ∀ i ∈ s, RegVal (f i) (v i)) : RegVal (∑ i ∈ s, f i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (regVal_C (0 : ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `t^m p(1/t)` is regular at `t = 0` with value `p_m`, for a polynomial of degree at most
`m`. -/
theorem regVal_EInf_poly (p : Polynomial ℂ) (m : ℕ) (hp : p.natDegree ≤ m) :
    RegVal (EInf (algebraMap (Polynomial ℂ) KK p) * tL ^ m) (p.coeff m) := by
  have h1 : p = ∑ k ∈ range (m + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k :=
    p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hp)
  have h2 : EInf (algebraMap (Polynomial ℂ) KK p) * tL ^ m =
      ∑ k ∈ range (m + 1), HahnSeries.C (p.coeff k) * tL ^ (m - k) := by
    conv_lhs => rw [h1]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    rw [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_mul, map_pow, EInf_C,
      EInf_X, mul_assoc]
    congr 1
    rw [inv_pow, ← Nat.sub_add_cancel hk', pow_add, Nat.add_sub_cancel, mul_comm (tL ^ (m - k)),
      inv_mul_cancel_left₀ (pow_ne_zero _ tL_ne_zero)]
  have h3 : p.coeff m = ∑ k ∈ range (m + 1), if k = m then p.coeff k else 0 := by
    rw [Finset.sum_ite_eq' (range (m + 1)) m]
    simp
  rw [h2, h3]
  refine regVal_sum fun k hk => ?_
  split_ifs with hkm
  · subst hkm
    simpa using regVal_C (p.coeff k)
  · have hk' : k < m := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hkm
    have h4 := (regVal_C (p.coeff k)).mul (regVal_tL.pow (m - k))
    rwa [zero_pow (by omega), mul_zero] at h4

theorem tendsto_ofReal_cobounded :
    Tendsto (fun lam : ℝ => (lam : ℂ)) atTop (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simp only [Complex.norm_real]
  exact tendsto_norm_atTop_atTop

/-- A rational function regular at `λ = ∞` tends, along real `λ → +∞`, to the constant term of
its expansion at `∞`. -/
theorem tendsto_evalAt_of_regularAtInfty (r : KK) (h : RegularAtInfty r) :
    Tendsto (fun lam : ℝ => evalAt (lam : ℂ) r) atTop (𝓝 (inftyCoeff r 0)) := by
  set p := r.num with hp
  set q := r.denom with hq
  set m := max p.natDegree q.natDegree with hm
  have hq0 : q ≠ 0 := RatFunc.denom_ne_zero r
  have hr : r = algebraMap _ KK p / algebraMap _ KK q := (RatFunc.num_div_denom r).symm
  have hP := regVal_EInf_poly p m (le_max_left _ _)
  have hQ := regVal_EInf_poly q m (le_max_right _ _)
  have hmul : EInf r * (EInf (algebraMap _ KK q) * tL ^ m) =
      EInf (algebraMap _ KK p) * tL ^ m := by
    rw [← mul_assoc, ← map_mul]
    congr 2
    rw [hr, div_mul_cancel₀]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hq0
  have hreg := (regularAtInfty_iff r).1 h
  have hqm : q.coeff m ≠ 0 := by
    intro h0
    have hpm : p.coeff m ≠ 0 := by
      rcases le_total p.natDegree q.natDegree with hle | hle
      · rw [hm, max_eq_right hle, Polynomial.coeff_natDegree,
          Polynomial.leadingCoeff_eq_zero] at h0
        exact absurd h0 hq0
      · rw [hm, max_eq_left hle, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_ne_zero]
        intro hp0
        have hq1 : q.natDegree = 0 := by
          rw [hp0] at hle
          simpa using hle
        have hm0 : m = q.natDegree := by rw [hm, hp0, hq1]; simp
        rw [hm0, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_eq_zero] at h0
        exact hq0 h0
    have h1 : OrdGE (EInf (algebraMap _ KK q) * tL ^ m) 1 := by
      rw [ordGE_iff]
      intro n hn
      rcases lt_or_eq_of_le (show n ≤ 0 by omega) with h2 | h2
      · exact hQ.1.coeff_eq_zero h2
      · rw [h2, hQ.2, h0]
    have h2 := hreg.mul h1
    rw [hmul] at h2
    exact hpm (hP.2 ▸ h2.coeff_eq_zero (by norm_num))
  have hval : RegVal (EInf r) (p.coeff m / q.coeff m) := by
    have h1 : EInf r = (EInf (algebraMap _ KK p) * tL ^ m) /
        (EInf (algebraMap _ KK q) * tL ^ m) := by
      rw [eq_div_iff, hmul]
      intro h0
      rw [h0] at hQ
      exact hqm (by simpa using hQ.2.symm)
    rw [h1]
    exact hP.div hQ hqm
  rw [inftyCoeff_eq, hval.2]
  have h1 := (tendsto_eval_div_pow p m (le_max_left _ _)).comp tendsto_ofReal_cobounded
  have h2 := (tendsto_eval_div_pow q m (le_max_right _ _)).comp tendsto_ofReal_cobounded
  refine (h1.div h2 hqm).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  have hl : ((lam : ℂ)) ^ m ≠ 0 := pow_ne_zero _ (by exact_mod_cast hlam.ne')
  simp only [Function.comp_apply, Pi.div_apply]
  rw [div_div_div_cancel_right₀ hl]
  simp [evalAt, RatFunc.eval, hp, hq, Polynomial.eval₂_id]

end Virasoro.Sphere
