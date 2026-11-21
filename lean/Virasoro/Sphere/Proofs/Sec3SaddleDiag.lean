import Virasoro.Sphere.Proofs.FpowBinom
import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Sphere paper Lemma 3.4(i), the diagonal of `B(p,q)` (`sphere/paper.tex` l.749–750)

Setting `q = p` in (3.4) gives `-½B(p,p) = p²/(16(1-p)²) = ∑_{k≥2} (k-1)/16 p^k`, that is
`-½∑_{n=1}^{k-1} B_{n,k-n} = (k-1)/16`.  The substitution `q = p` is the algebra map
`diag : ℚ[[p,q]] → ℚ[[x]]`, `p, q ↦ x`.

Consumer: the second conjunct of part (i) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem hasSubst_diag :
    MvPowerSeries.HasSubst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries ℚ)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => PowerSeries.constantCoeff_X

/-- The substitution `p, q ↦ x`. -/
noncomputable def diag (f : MvPowerSeries (Fin 2) ℚ) : PowerSeries ℚ :=
  MvPowerSeries.subst (fun _ : Fin 2 => (PowerSeries.X : PowerSeries ℚ)) f

theorem diag_eq (f : MvPowerSeries (Fin 2) ℚ) :
    diag f = MvPowerSeries.substAlgHom hasSubst_diag f := by
  rw [diag, MvPowerSeries.coe_substAlgHom]

theorem coeff_diag (f : MvPowerSeries (Fin 2) ℚ) (k : ℕ) :
    PowerSeries.coeff k (diag f) =
      ∑ ij ∈ antidiagonal k,
        MvPowerSeries.coeff (Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2) f := by
  show MvPowerSeries.coeff (Finsupp.single () k) (diag f) = _
  rw [diag, MvPowerSeries.coeff_subst hasSubst_diag]
  have key : ∀ d : Fin 2 →₀ ℕ,
      MvPowerSeries.coeff (Finsupp.single () k)
        (d.prod fun _ e => (PowerSeries.X : PowerSeries ℚ) ^ e) =
        if d 0 + d 1 = k then 1 else 0 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, ← pow_add]
    have := PowerSeries.coeff_X_pow (R := ℚ) k (d 0 + d 1)
    rw [PowerSeries.coeff] at this
    rw [this]
    simp only [eq_comm]
  simp only [key, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_sum_of_support_subset
    (s := (antidiagonal k).image fun ij => Finsupp.single 0 ij.1 + Finsupp.single 1 ij.2)]
  · rw [Finset.sum_image]
    · refine sum_congr rfl fun ij h => ?_
      have := HasAntidiagonal.mem_antidiagonal.1 h
      simp [this]
    · intro a _ b _ h
      have h0 := DFunLike.congr_fun h 0
      have h1 := DFunLike.congr_fun h 1
      simp at h0 h1
      exact Prod.ext h0 h1
  · intro d hd
    have hk : d 0 + d 1 = k := by
      by_contra h
      exact hd (by simp [h])
    simp only [coe_image, Set.mem_image, mem_coe, HasAntidiagonal.mem_antidiagonal]
    refine ⟨(d 0, d 1), hk, ?_⟩
    ext i
    fin_cases i <;> simp

/-- `√(1-x)` in one variable. -/
noncomputable def sOne : PowerSeries ℚ :=
  (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (-(PowerSeries.X : PowerSeries ℚ))

theorem hasSubst_negX1 : PowerSeries.HasSubst (-(PowerSeries.X : PowerSeries ℚ)) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

theorem sOne_sq : sOne ^ 2 = 1 - PowerSeries.X := by
  have h1 : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) * PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) =
      1 + PowerSeries.X := by
    rw [← PowerSeries.binomialSeries_add]
    have := PowerSeries.binomialSeries_nat (R := ℚ) (A := ℚ) 1
    norm_num at this ⊢
    exact this
  rw [sOne, pow_two, ← PowerSeries.subst_mul hasSubst_negX1, h1,
    PowerSeries.subst_add hasSubst_negX1, PowerSeries.subst_X hasSubst_negX1]
  rw [← PowerSeries.coe_substAlgHom hasSubst_negX1, map_one]
  ring

theorem diag_sqrtOneSub (i : Fin 2) : diag (sqrtOneSub i) = sOne := by
  rw [sqrtOneSub_eq_subst, diag, sOne, PowerSeries.subst, PowerSeries.subst,
    MvPowerSeries.subst_comp_subst_apply (hasSubst_negX i).const hasSubst_diag]
  congr 1
  funext _
  rw [← MvPowerSeries.coe_substAlgHom hasSubst_diag, map_neg, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_X hasSubst_diag]

theorem diag_X (i : Fin 2) : diag (MvPowerSeries.X i) = PowerSeries.X := by
  rw [diag, MvPowerSeries.subst_X hasSubst_diag]

theorem constantCoeff_sqrtOneSub (i : Fin 2) :
    MvPowerSeries.constantCoeff (sqrtOneSub i) = 1 := by
  show sqrtOneSub i 0 = 1
  simp [sqrtOneSub, gbinom]

/-- The denominator of `B(p,q)`. -/
noncomputable def Bden : MvPowerSeries (Fin 2) ℚ :=
  2 * sqrtOneSub 0 * sqrtOneSub 1 * (sqrtOneSub 0 + sqrtOneSub 1) ^ 2

theorem constantCoeff_Bden : MvPowerSeries.constantCoeff Bden = 8 := by
  simp only [Bden, map_mul, map_pow, map_add, constantCoeff_sqrtOneSub, map_ofNat]
  norm_num

theorem Bgf_mul_Bden : Bgf * Bden = -(MvPowerSeries.X 0 * MvPowerSeries.X 1) := by
  have h : MvPowerSeries.constantCoeff Bden ≠ 0 := by rw [constantCoeff_Bden]; norm_num
  rw [Bgf, ← Bden, mul_assoc, MvPowerSeries.inv_mul_cancel _ h, mul_one]

theorem diag_Bgf_mul :
    diag Bgf * (8 * (1 - PowerSeries.X) ^ 2) = -(PowerSeries.X * PowerSeries.X) := by
  have h := congrArg (MvPowerSeries.substAlgHom hasSubst_diag) Bgf_mul_Bden
  rw [map_mul, map_neg, map_mul, Bden] at h
  simp only [map_mul, map_pow, map_add, map_ofNat, ← diag_eq, diag_sqrtOneSub, diag_X] at h
  rw [← h, ← sOne_sq]
  ring

/-- The series `-∑_{k≥1} (k-1)/8 x^k`. -/
noncomputable def diagSer : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k = 0 then 0 else -((k : ℚ) - 1) / 8

theorem diagSer_mul :
    diagSer * (8 * (1 - PowerSeries.X) ^ 2) = -(PowerSeries.X * PowerSeries.X) := by
  have e : diagSer * (8 * (1 - PowerSeries.X) ^ 2) =
      PowerSeries.C 8 * diagSer - PowerSeries.C 16 * (diagSer * PowerSeries.X) +
        PowerSeries.C 8 * (diagSer * PowerSeries.X ^ 2) := by
    have h8 : (PowerSeries.C (8 : ℚ) : PowerSeries ℚ) = 8 := map_ofNat _ 8
    have h16 : (PowerSeries.C (16 : ℚ) : PowerSeries ℚ) = 16 := map_ofNat _ 16
    rw [h8, h16]
    ring
  rw [e, ← pow_two]
  ext n
  simp only [map_sub, map_add, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_mul_X_pow', diagSer, PowerSeries.coeff_mk]
  rcases n with _ | _ | _ | n
  · simp [PowerSeries.coeff_zero_mul_X]
  · simp [PowerSeries.coeff_succ_mul_X]
  · simp [PowerSeries.coeff_succ_mul_X]
    norm_num
  · simp [PowerSeries.coeff_succ_mul_X]
    ring

theorem diag_Bgf : diag Bgf = diagSer := by
  have hne : (8 * (1 - PowerSeries.X) ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    rw [← map_ofNat (PowerSeries.C (R := ℚ)) 8] at h
    have := congrArg PowerSeries.constantCoeff h
    simp at this
  exact mul_right_cancel₀ hne (diag_Bgf_mul.trans diagSer_mul.symm)

theorem Bcoef_zero_left (n : ℕ) : Bcoef 0 n = 0 := by
  rw [Bcoef, Bgf, neg_mul, map_neg, neg_eq_zero, mul_assoc, MvPowerSeries.coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  rw [MvPowerSeries.coeff_X]
  have h0 : p.1 0 = 0 := by
    have := DFunLike.congr_fun (HasAntidiagonal.mem_antidiagonal.1 hp) 0
    simp at this
    omega
  rw [if_neg (fun h => by rw [h] at h0; simp at h0), zero_mul]

theorem Bcoef_zero_right (m : ℕ) : Bcoef m 0 = 0 := by
  rw [Bcoef, Bgf, neg_mul, map_neg, neg_eq_zero, mul_comm (MvPowerSeries.X 0), mul_assoc,
    MvPowerSeries.coeff_mul]
  refine sum_eq_zero fun p hp => ?_
  rw [MvPowerSeries.coeff_X]
  have h0 : p.1 1 = 0 := by
    have := DFunLike.congr_fun (HasAntidiagonal.mem_antidiagonal.1 hp) 1
    simp at this
    omega
  rw [if_neg (fun h => by rw [h] at h0; simp at h0), zero_mul]

/-- Lemma 3.4(i), second claim: `-½∑_{n=1}^{k-1} B_{n,k-n} = (k-1)/16` for `k ≥ 1`. -/
theorem sum_Bcoef_diag (k : ℕ) (hk : 1 ≤ k) :
    -(1 / 2 : ℚ) * ∑ n ∈ Icc 1 (k - 1), Bcoef n (k - n) = ((k : ℚ) - 1) / 16 := by
  have h1 : ∑ n ∈ Icc 1 (k - 1), Bcoef n (k - n) = ∑ n ∈ range (k + 1), Bcoef n (k - n) := by
    refine sum_subset (fun n hn => by simp at hn ⊢; omega) fun n hn hn' => ?_
    simp only [mem_range, mem_Icc, not_and, not_le] at hn hn'
    by_cases h0 : n = 0
    · rw [h0, Bcoef_zero_left]
    · have : k - n = 0 := by omega
      rw [this, Bcoef_zero_right]
  have h2 := coeff_diag Bgf k
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => MvPowerSeries.coeff (Finsupp.single 0 i + Finsupp.single 1 j) Bgf) k,
    diag_Bgf, diagSer, PowerSeries.coeff_mk, if_neg (by omega)] at h2
  rw [h1]
  show -(1 / 2 : ℚ) * ∑ n ∈ range (k + 1),
    MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 (k - n)) Bgf = _
  rw [← h2]
  ring

end Virasoro.Sphere
