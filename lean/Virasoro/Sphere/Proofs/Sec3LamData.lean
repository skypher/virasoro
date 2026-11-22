import Virasoro.Sphere.Proofs.Sec3LamOrders

/-!
# The universal series `S̃^{(1)}`, `S_c^{(2)}`, `S_1^{(2)}`, `S_2^{(2)}` (Lemma 3.3(ii))

sphere/paper.tex l.612–635.  `S^{(1)} = μ S̃^{(1)}` is independent of `(Δ₁, Δ₂)`; the involution
`ι` fixes `S^{(0)}` and commutes with `L_k^{(0)}`, while negating `k∂_k S^{(0)}`, so by
uniqueness `ι(S̃^{(1)}) = -S̃^{(1)}`.  At order `λ⁻²` the source is affine-linear in
`(μ², Δ₁ - 1/16, Δ₂ - 1/16)` and `ι`-even; uniqueness gives the decomposition and the
`ι`-evenness of `S^{(2)}`.
-/

namespace Virasoro.Sphere

open Finset

local notation "KK" => RatFunc ℂ

/-! ### Linearity of `L_k^{(0)}` and uniqueness -/

theorem L0_add (k : ℕ) (T T' : MvPowerSeries ℕ+ ℂ) : L0 k (T + T') = L0 k T + L0 k T' :=
  (L0lin k).map_add T T'

theorem L0_sub (k : ℕ) (T T' : MvPowerSeries ℕ+ ℂ) : L0 k (T - T') = L0 k T - L0 k T' :=
  (L0lin k).map_sub T T'

theorem L0_smul (k : ℕ) (z : ℂ) (T : MvPowerSeries ℕ+ ℂ) : L0 k (z • T) = z • L0 k T :=
  (L0lin k).map_smul z T

/-- A series with zero constant term annihilated by all `L_k^{(0)}`, `k ≥ 1`, vanishes. -/
theorem eq_zero_of_L0 (D : MvPowerSeries ℕ+ ℂ) (h : ∀ k : ℕ, 1 ≤ k → L0 k D = 0)
    (h0 : MvPowerSeries.coeff 0 D = 0) : D = 0 := by
  ext α
  by_cases hα : α = 0
  · rw [hα, h0, map_zero]
  · rw [L0_unique D h α hα, map_zero]

/-! ### The involution `ι` -/

theorem coeff_iota (T : MvPowerSeries ℕ+ ℂ) (α : ℕ+ →₀ ℕ) :
    MvPowerSeries.coeff α (iota T) =
      (-1) ^ α.degree * (starRingEnd ℂ) (MvPowerSeries.coeff α T) := rfl

/-- `ι` as an additive map. -/
noncomputable def iotaHom : MvPowerSeries ℕ+ ℂ →+ MvPowerSeries ℕ+ ℂ where
  toFun := iota
  map_zero' := by
    ext α
    rw [coeff_iota]
    simp
  map_add' T T' := by
    ext α
    simp only [coeff_iota, map_add, mul_add]

theorem iota_add (T T' : MvPowerSeries ℕ+ ℂ) : iota (T + T') = iota T + iota T' :=
  iotaHom.map_add T T'

theorem iota_sub (T T' : MvPowerSeries ℕ+ ℂ) : iota (T - T') = iota T - iota T' :=
  iotaHom.map_sub T T'

theorem iota_neg (T : MvPowerSeries ℕ+ ℂ) : iota (-T) = -iota T := iotaHom.map_neg T

theorem iota_sum {ι' : Type*} (s : Finset ι') (f : ι' → MvPowerSeries ℕ+ ℂ) :
    iota (∑ i ∈ s, f i) = ∑ i ∈ s, iota (f i) := map_sum iotaHom f s

theorem iota_smul (z : ℂ) (T : MvPowerSeries ℕ+ ℂ) :
    iota (z • T) = (starRingEnd ℂ) z • iota T := by
  ext α
  simp only [coeff_iota, MvPowerSeries.coeff_smul, map_mul]
  ring

theorem iota_mul (f g : MvPowerSeries ℕ+ ℂ) : iota (f * g) = iota f * iota g := by
  classical
  ext α
  rw [coeff_iota, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  rw [coeff_iota, coeff_iota, map_mul, ← hp', map_add, pow_add]
  ring

theorem iota_C (z : ℂ) : iota (MvPowerSeries.C z) = MvPowerSeries.C ((starRingEnd ℂ) z) := by
  classical
  ext α
  rw [coeff_iota, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  split_ifs with h0
  · rw [h0]
    simp
  · simp

theorem iota_pd (n : ℕ) (T : MvPowerSeries ℕ+ ℂ) : iota (pdA n T) = -pdA n (iota T) := by
  ext α
  rw [coeff_iota, coeff_pdA, map_neg, coeff_pdA, coeff_iota, map_mul, map_add, map_add,
    Finsupp.degree_single, pow_succ, map_natCast, map_one]
  ring

theorem pd_iota (n : ℕ) (T : MvPowerSeries ℕ+ ℂ) : pdA n (iota T) = -iota (pdA n T) := by
  rw [iota_pd, neg_neg]

theorem iota_shift (k : ℕ) (T : MvPowerSeries ℕ+ ℂ) : iota (shiftA k T) = shiftA k (iota T) := by
  ext α
  rw [coeff_iota, coeff_shiftA, coeff_shiftA, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hd : α.degree = (α - Finsupp.single j 1 : ℕ+ →₀ ℕ).degree + 1 := by
    have := congrArg Finsupp.degree (sub_add_single hj)
    rw [map_add, Finsupp.degree_single] at this
    omega
  rw [pd_iota, map_neg, coeff_iota, map_mul, map_natCast, hd, pow_succ]
  ring

theorem iota_level (T : MvPowerSeries ℕ+ ℂ) : iota (levelA T) = levelA (iota T) := by
  ext α
  rw [coeff_iota, coeff_levelA, coeff_levelA, coeff_iota, map_mul, map_natCast]
  ring

theorem conj_Acoef (m : ℕ) : (starRingEnd ℂ) (Acoef m) = -Acoef m := by
  rw [Acoef, map_mul, map_mul, map_neg, map_ofNat, Complex.conj_I, map_ratCast]
  ring

theorem pdA_neg {A : Type*} [CommRing A] (n : ℕ) (T : MvPowerSeries ℕ+ A) :
    pdA n (-T) = -pdA n T := map_neg _ _

theorem iota_S0 : iota S0 = S0 := by
  ext α
  rw [coeff_iota]
  show (-1) ^ α.degree * (starRingEnd ℂ) (S0 α) = S0 α
  unfold S0
  split_ifs with h1 h2
  · rw [h1, map_sum]
    simp [conj_Acoef]
  · rw [h2, map_sum]
    simp only [map_sum, apply_ite (starRingEnd ℂ), map_zero, map_ratCast]
    norm_num
  · simp

theorem iota_L0 (k : ℕ) (T : MvPowerSeries ℕ+ ℂ) : iota (L0 k T) = L0 k (iota T) := by
  rw [L0_eq, L0_eq, iota_sub, iota_sub, iota_add, iota_smul, iota_smul, iota_pd, iota_shift,
    iota_level, iota_sum]
  have hs : ∀ n, iota (pdA n S0 * pdA (k - n) T) = pdA n S0 * pdA (k - n) (iota T) := by
    intro n
    rw [iota_mul, iota_pd, iota_pd, iota_S0, neg_mul_neg]
  have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  simp only [hs, Complex.conj_I, h2, neg_smul, smul_neg, neg_neg]

theorem coeff_zero_iota (T : MvPowerSeries ℕ+ ℂ) (h : MvPowerSeries.coeff 0 T = 0) :
    MvPowerSeries.coeff 0 (iota T) = 0 := by
  rw [coeff_iota, h]
  simp

/-! ### The universal series -/

section Data

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

/-- `S̃^{(1)}`: the order-`λ⁻¹` coefficient at `μ = 1`. -/
noncomputable def S1tDef : MvPowerSeries ℕ+ ℂ := Sord (wardRat 1 0 0) 1

/-- `S_c^{(2)}`: the order-`λ⁻²` coefficient at `μ = 1`, `Δ₁ = Δ₂ = 1/16`. -/
noncomputable def S2cDef : MvPowerSeries ℕ+ ℂ := Sord (wardRat 1 (1 / 16) (1 / 16)) 2

/-- `S_2^{(2)}`. -/
noncomputable def S22Def : MvPowerSeries ℕ+ ℂ := Sord (wardRat 1 (1 / 16) (17 / 16)) 2 - S2cDef

/-- `S_1^{(2)}`. -/
noncomputable def S21Def : MvPowerSeries ℕ+ ℂ := Sord (wardRat 1 (17 / 16) (1 / 16)) 2 - S2cDef

/-- The source at order `λ⁻²` per unit `μ²`:
`k∂_k S̃^{(1)} - ¼∑(∂_n S̃^{(1)})(∂_{k-n}S̃^{(1)}) - 1`. -/
noncomputable def Gsrc (k : ℕ) : MvPowerSeries ℕ+ ℂ :=
  (k : ℂ) • pdA k S1tDef - (1 / 4 : ℂ) • ∑ n ∈ Icc 1 (k - 1), pdA n S1tDef * pdA (k - n) S1tDef - 1

include hF hK

theorem ward_ref (Δa Δb : ℂ) :
    IsWardSeries (RatFunc.C (1 : ℂ)) (RatFunc.X : KK) (RatFunc.C Δa) (RatFunc.C Δb)
      (wardRat 1 Δa Δb) := by
  have h := wardRat_isWard hF hK 1 one_pos Δa Δb
  rwa [Complex.ofReal_one] at h

theorem L0_S1t (k : ℕ) (hk : 1 ≤ k) : L0 k S1tDef = -((k : ℂ) • pdA k S0) := by
  have h := L0_Sord_one (ward_ref hF hK 0 0) k hk
  rwa [one_mul] at h

/-- `S^{(1)} = μ S̃^{(1)}`. -/
theorem Sord_one_eq {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F) :
    Sord F 1 = μ • S1tDef := by
  rw [← sub_eq_zero]
  refine eq_zero_of_L0 _ (fun k hk => ?_) ?_
  · rw [L0_sub, L0_smul, L0_Sord_one h k hk, L0_S1t hF hK k hk, smul_neg, smul_smul, sub_neg_eq_add,
      neg_add_cancel]
  · rw [map_sub, coeff_zero_Sord h, MvPowerSeries.coeff_smul,
      S1tDef, coeff_zero_Sord (ward_ref hF hK 0 0), mul_zero, sub_zero]

/-- Order `λ⁻²` with `S^{(1)} = μS̃^{(1)}`. -/
theorem L0_Sord_two' {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)
    (k : ℕ) (hk : 1 ≤ k) :
    L0 k (Sord F 2) = -(μ ^ 2 • Gsrc k) +
      MvPowerSeries.C ((k : ℂ) * (Δ2 - 1 / 16) - (Δ1 - 1 / 16)) := by
  have e := L0_Sord_two h k hk
  rw [Sord_one_eq hF hK h] at e
  have hc : μ ^ 2 + ((k : ℂ) * Δ2 - Δ1) - ((k : ℂ) - 1) / 16 =
      μ ^ 2 + ((k : ℂ) * (Δ2 - 1 / 16) - (Δ1 - 1 / 16)) := by ring
  rw [hc] at e
  generalize (k : ℂ) * (Δ2 - 1 / 16) - (Δ1 - 1 / 16) = c' at e ⊢
  rw [e, Gsrc]
  simp only [pdA_smul, smul_mul_smul_comm, ← Finset.smul_sum]
  simp only [MvPowerSeries.smul_eq_C_mul, map_add, map_mul, map_pow]
  ring

theorem L0_S2c (k : ℕ) (hk : 1 ≤ k) : L0 k S2cDef = -Gsrc k := by
  have h := L0_Sord_two' hF hK (ward_ref hF hK (1 / 16) (1 / 16)) k hk
  rw [S2cDef, h]
  simp

theorem L0_S22 (k : ℕ) (hk : 1 ≤ k) : L0 k S22Def = MvPowerSeries.C (k : ℂ) := by
  have h := L0_Sord_two' hF hK (ward_ref hF hK (1 / 16) (17 / 16)) k hk
  rw [S22Def, L0_sub, L0_S2c hF hK k hk, h]
  have e : (k : ℂ) * (17 / 16 - 1 / 16) - (1 / 16 - 1 / 16) = (k : ℂ) := by ring
  rw [e]
  simp

theorem L0_S21 (k : ℕ) (hk : 1 ≤ k) : L0 k S21Def = -1 := by
  have h := L0_Sord_two' hF hK (ward_ref hF hK (17 / 16) (1 / 16)) k hk
  rw [S21Def, L0_sub, L0_S2c hF hK k hk, h]
  have e : (k : ℂ) * (1 / 16 - 1 / 16) - (17 / 16 - 1 / 16) = -1 := by ring
  rw [e]
  simp

theorem coeff_zero_S2c : MvPowerSeries.coeff 0 S2cDef = 0 :=
  coeff_zero_Sord (ward_ref hF hK _ _) 2

/-- `S^{(2)} = μ² S_c^{(2)} + (Δ₂ - 1/16) S_2^{(2)} + (Δ₁ - 1/16) S_1^{(2)}`. -/
theorem Sord_two_eq {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F) :
    Sord F 2 = μ ^ 2 • S2cDef + (Δ2 - 1 / 16) • S22Def + (Δ1 - 1 / 16) • S21Def := by
  rw [← sub_eq_zero]
  refine eq_zero_of_L0 _ (fun k hk => ?_) ?_
  · rw [L0_sub, L0_add, L0_add, L0_smul, L0_smul, L0_smul, L0_Sord_two' hF hK h k hk,
      L0_S2c hF hK k hk, L0_S22 hF hK k hk, L0_S21 hF hK k hk]
    simp only [MvPowerSeries.smul_eq_C_mul, map_sub, map_mul]
    ring
  · simp only [map_sub, map_add, MvPowerSeries.coeff_smul, coeff_zero_Sord h, S22Def, S21Def,
      coeff_zero_S2c hF hK, coeff_zero_Sord (ward_ref hF hK _ _), mul_zero, sub_zero, add_zero]

/-- `ι(S̃^{(1)}) = -S̃^{(1)}`. -/
theorem iota_S1t : iota S1tDef = -S1tDef := by
  rw [← add_eq_zero_iff_eq_neg]
  refine eq_zero_of_L0 _ (fun k hk => ?_) ?_
  · rw [L0_add, ← iota_L0, L0_S1t hF hK k hk, iota_neg, iota_smul, iota_pd, iota_S0, map_natCast]
    simp
  · have h01 : MvPowerSeries.coeff 0 S1tDef = 0 := coeff_zero_Sord (ward_ref hF hK 0 0) 1
    rw [map_add, coeff_zero_iota _ h01, h01, zero_add]

theorem iota_Gsrc (k : ℕ) : iota (Gsrc k) = Gsrc k := by
  have h4 : (starRingEnd ℂ) (1 / 4 : ℂ) = 1 / 4 := by
    rw [map_div₀, map_one, map_ofNat]
  have h1 : iota (1 : MvPowerSeries ℕ+ ℂ) = 1 := by
    have := iota_C 1
    rwa [map_one, map_one] at this
  have hs : ∀ n, iota (pdA n S1tDef * pdA (k - n) S1tDef) =
      pdA n S1tDef * pdA (k - n) S1tDef := by
    intro n
    rw [iota_mul, iota_pd, iota_pd, iota_S1t hF hK, pdA_neg, pdA_neg, neg_neg, neg_neg]
  rw [Gsrc, iota_sub, iota_sub, iota_smul, iota_smul, iota_sum, h1, h4, map_natCast, iota_pd,
    iota_S1t hF hK, pdA_neg, neg_neg]
  simp only [hs]

/-- `S^{(2)}` is `ι`-even at real parameters. -/
theorem iota_Sord_two {μ Δ1 Δ2 : ℝ} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : KK) (RatFunc.C (Δ1 : ℂ))
      (RatFunc.C (Δ2 : ℂ)) F) : iota (Sord F 2) = Sord F 2 := by
  rw [← sub_eq_zero]
  refine eq_zero_of_L0 _ (fun k hk => ?_) ?_
  · rw [L0_sub, ← iota_L0, L0_Sord_two' hF hK h k hk, iota_add, iota_neg, iota_smul,
      iota_Gsrc hF hK, iota_C]
    have e1 : (starRingEnd ℂ) ((μ : ℂ) ^ 2) = (μ : ℂ) ^ 2 := by
      rw [map_pow, Complex.conj_ofReal]
    have e2 : (starRingEnd ℂ) ((k : ℂ) * ((Δ2 : ℂ) - 1 / 16) - ((Δ1 : ℂ) - 1 / 16)) =
        (k : ℂ) * ((Δ2 : ℂ) - 1 / 16) - ((Δ1 : ℂ) - 1 / 16) := by
      simp only [map_sub, map_mul, map_natCast, Complex.conj_ofReal, map_div₀, map_one,
        map_ofNat]
    rw [e1, e2, sub_self]
  · rw [map_sub, coeff_zero_iota _ (coeff_zero_Sord h 2), coeff_zero_Sord h, sub_zero]

/-- Step (ii-b) of Lemma 3.3. -/
theorem sub_lam_orders : Stmt_sub_lam_orders := by
  refine ⟨S1tDef, S2cDef, S21Def, S22Def, ?_, iota_S1t hF hK, fun k hk =>
    ⟨L0_S22 hF hK k hk, L0_S21 hF hK k hk⟩, fun μ _ Δ1 Δ2 F h => iota_Sord_two hF hK h⟩
  intro μ _ Δ1 Δ2 F h
  exact ⟨Sord_one_eq hF hK h, Sord_two_eq hF hK h⟩

end Data

end Virasoro.Sphere
