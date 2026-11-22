import Virasoro.Sphere.Proofs.Sec3LamFinal
import Virasoro.Sphere.Statements.Sec3d

/-!
# Sphere paper Lemma 3.6 (sphere/paper.tex l.974–1010): reduction to the linear equations

The paper's proof: `L_k^{(0)}` is a derivation, so `L_k^{(0)}(2 log(1 - g(1))) = k` and
`L_k^{(0)}(2 log(1 - g(-1))) = -1` are equivalent to `L_k^{(0)}g(1) = -(k/2)(1 - g(1))` and
`L_k^{(0)}g(-1) = ½(1 - g(-1))` (l.991–994); these are checked on generating functions
(l.981–990, l.995–1006); then uniqueness of `S_1^{(2)}, S_2^{(2)}` (Lemma 3.3) gives the series.
Here the derivation step and the uniqueness step are carried out; the two linear equations
are the statement `Stmt_sub_ext_linear`.
-/

namespace Virasoro.Sphere

open Finset

local notation "KK" => RatFunc ℂ

/-- The linear equations of sphere/paper.tex l.981–1006: for every `k ≥ 1`,
`L_k^{(0)}g(1) = -(k/2)(1 - g(1))` and `L_k^{(0)}g(-1) = ½(1 - g(-1))`. -/
def Stmt_sub_ext_linear : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    L0 k (gAt 1) = -(((k : ℂ) / 2) • (1 - gAt 1)) ∧
    L0 k (gAt (-1)) = (1 / 2 : ℂ) • (1 - gAt (-1))

/-- `L_k^{(0)}` is a derivation: `L_k^{(0)}(f(g)) = f'(g) L_k^{(0)}g`. -/
theorem L0_subst (k : ℕ) (f : PowerSeries ℂ) (g : MvPowerSeries ℕ+ ℂ)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    L0 k (f.subst g) = (PowerSeries.derivative ℂ f).subst g * L0 k g := by
  have hpd : ∀ j, pdA j (f.subst g) = (PowerSeries.derivative ℂ f).subst g * pdA j g :=
    fun j => pderiv_subst hg f _
  rw [L0_eq, L0_eq, shiftA_of_pd k _ _ g hpd, levelA_of_pd _ _ g hpd]
  simp_rw [hpd]
  have hs : ∑ n ∈ Icc 1 (k - 1),
      pdA n S0 * ((PowerSeries.derivative ℂ f).subst g * pdA (k - n) g) =
      (PowerSeries.derivative ℂ f).subst g * ∑ n ∈ Icc 1 (k - 1), pdA n S0 * pdA (k - n) g := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hs]
  simp only [MvPowerSeries.smul_eq_C_mul]
  ring

theorem deriv_log_subst_mul {τ : Type*} (g : MvPowerSeries τ ℂ)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    (PowerSeries.derivative ℂ (PowerSeries.log ℂ)).subst g * (1 + g) = 1 := by
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero hg
  have h1 := congrArg (PowerSeries.subst g) (deriv_log_mul (A := ℂ))
  rwa [← PowerSeries.coe_substAlgHom hs, map_mul, map_add, map_one, PowerSeries.substAlgHom_X,
    PowerSeries.coe_substAlgHom hs] at h1

theorem constantCoeff_linSeries (c : ℕ → ℂ) : MvPowerSeries.constantCoeff (linSeries c) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show linSeries c 0 = 0
  simp [linSeries]

theorem constantCoeff_neg_gAt (s : ℂ) : MvPowerSeries.constantCoeff (-gAt s) = 0 := by
  rw [map_neg, gAt, constantCoeff_linSeries, neg_zero]

/-- `L_k^{(0)}(log(1 - g)) = c` when `L_k^{(0)}g = -c(1 - g)`. -/
theorem L0_log_of_linear (k : ℕ) (s c : ℂ) (h : L0 k (gAt s) = -(c • (1 - gAt s))) :
    L0 k ((PowerSeries.log ℂ).subst (-gAt s)) = MvPowerSeries.C c := by
  have hg := constantCoeff_neg_gAt s
  have hneg : L0 k (-gAt s) = c • (1 - gAt s) := by
    have e : (-gAt s) = (-1 : ℂ) • gAt s := by rw [neg_smul, one_smul]
    rw [e, L0_smul, h, neg_smul, one_smul, neg_neg]
  rw [L0_subst k _ _ hg, hneg, MvPowerSeries.smul_eq_C_mul, sub_eq_add_neg, mul_left_comm,
    deriv_log_subst_mul _ hg, mul_one]

section Uniqueness

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK

/-- The universal series of Lemma 3.3(ii) are determined by `IsExpansionData`. -/
theorem expansionData_unique {S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ}
    (hE : IsExpansionData S1t S2c S21 S22) :
    S1t = S1tDef ∧ S2c = S2cDef ∧ S21 = S21Def ∧ S22 = S22Def := by
  have key : ∀ Δ1 Δ2 : ℝ, S1t = S1tDef ∧
      S2c + ((Δ2 : ℂ) - 1 / 16) • S22 + ((Δ1 : ℂ) - 1 / 16) • S21 =
        S2cDef + ((Δ2 : ℂ) - 1 / 16) • S22Def + ((Δ1 : ℂ) - 1 / 16) • S21Def := by
    intro Δ1 Δ2
    have hW := wardRat_isWard hF hK 1 one_pos (Δ1 : ℂ) (Δ2 : ℂ)
    obtain ⟨h1, h2⟩ := hE 1 one_pos Δ1 Δ2 _ hW
    have h1' := Sord_one_eq hF hK hW
    have h2' := Sord_two_eq hF hK hW
    rw [h1'] at h1
    rw [h2'] at h2
    simp only [Complex.ofReal_one, one_smul, one_pow] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  have h00 := (key (1 / 16) (1 / 16)).2
  have h01 := (key (1 / 16) (17 / 16)).2
  have h10 := (key (17 / 16) (1 / 16)).2
  have z0 : (((1 / 16 : ℝ) : ℂ)) - 1 / 16 = 0 := by push_cast; ring
  have z1 : (((17 / 16 : ℝ) : ℂ)) - 1 / 16 = 1 := by push_cast; ring
  rw [z0, zero_smul, zero_smul, zero_smul, zero_smul, add_zero, add_zero, add_zero,
    add_zero] at h00
  rw [z0, z1, zero_smul, zero_smul, one_smul, one_smul, add_zero, add_zero, h00] at h01
  rw [z0, z1, zero_smul, zero_smul, one_smul, one_smul, add_zero, add_zero, h00] at h10
  exact ⟨(key 0 0).1, h00, add_left_cancel h10, add_left_cancel h01⟩

/-- The series identities of Lemma 3.6 from the linear equations (l.991–994, l.1007–1008). -/
theorem ext_exponents_series (hlin : Stmt_sub_ext_linear) {S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ}
    (hE : IsExpansionData S1t S2c S21 S22) :
    S22 = (2 : ℂ) • (PowerSeries.log ℂ).subst (-gAt 1) ∧
    S21 = (2 : ℂ) • (PowerSeries.log ℂ).subst (-gAt (-1)) := by
  obtain ⟨-, -, e21, e22⟩ := expansionData_unique hF hK hE
  have hz : ∀ s : ℂ, MvPowerSeries.coeff 0 ((PowerSeries.log ℂ).subst (-gAt s)) = 0 := fun s => by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.constantCoeff_subst_eq_zero (constantCoeff_neg_gAt s) _
      PowerSeries.constantCoeff_log
  have hc0 := coeff_zero_S2c hF hK
  constructor
  · rw [e22, ← sub_eq_zero]
    refine eq_zero_of_L0 _ (fun k hk => ?_) ?_
    · rw [L0_sub, L0_smul, L0_S22 hF hK k hk, L0_log_of_linear k 1 ((k : ℂ) / 2) (hlin k hk).1,
        MvPowerSeries.smul_eq_C_mul, ← map_mul, ← map_sub]
      rw [show (k : ℂ) - 2 * ((k : ℂ) / 2) = 0 by ring, map_zero]
    · rw [map_sub, MvPowerSeries.coeff_smul, hz, S22Def, map_sub, hc0,
        coeff_zero_Sord (ward_ref hF hK _ _), mul_zero, sub_zero, sub_zero]
  · rw [e21, ← sub_eq_zero]
    refine eq_zero_of_L0 _ (fun k hk => ?_) ?_
    · have h2 : L0 k (gAt (-1)) = -((-(1 / 2 : ℂ)) • (1 - gAt (-1))) := by
        rw [(hlin k hk).2, neg_smul, neg_neg]
      rw [L0_sub, L0_smul, L0_S21 hF hK k hk, L0_log_of_linear k (-1) (-(1 / 2)) h2,
        MvPowerSeries.smul_eq_C_mul, ← map_mul]
      rw [show (2 : ℂ) * -(1 / 2) = -1 by ring, map_neg, map_one, sub_self]
    · rw [map_sub, MvPowerSeries.coeff_smul, hz, S21Def, map_sub, hc0,
        coeff_zero_Sord (ward_ref hF hK _ _), mul_zero, sub_zero, sub_zero]

end Uniqueness

end Virasoro.Sphere
