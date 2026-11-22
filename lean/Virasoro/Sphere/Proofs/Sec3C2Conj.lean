import Virasoro.Sphere.Proofs.Sec3C2Udag
import Virasoro.Sphere.Proofs.Sec3C2Current
import Virasoro.Sphere.Proofs.Sec3C2WickTools

/-!
# Lemma 3.7, Step 3: `U(W)^† α(x) (U(W)^†)^{-1} = f'(x;W) α(f(x;W))` (sphere paper)

sphere/paper.tex l.1119–1127.  Series in the `W_m` with operator coefficients form the ring
`OpS`.  `Ψ(W,x) = U(W)^† α(x) (U(W)^†)^{-1}` and `f'(x;W) α(f(x;W))` both solve
`D_k Ψ = -∂_x(x^{1-k} Ψ)` with `Ψ(0,x) = α(x)`; on the coefficient of `x^{-N-1}` the system reads
`D_k Ψ_N = N Ψ_{N-k}`.  The degree-triangular uniqueness gives their equality.
-/

namespace Virasoro.Sphere

open MvPolynomial Finset

/-- Formal series in the `W_m` whose coefficients are operators on `ℱ^{(2)}`. -/
abbrev OpS : Type := MvPowerSeries ℕ+ (Module.End ℂ Fock)

/-- `U(W)^†` as a series: the family `β ↦ U_β^†`. -/
noncomputable def UdS (U : Fock →ₗ[ℂ] HH) : OpS := fun β => Udg U β

/-- The coefficient of `W^β x^{-N-1}` in `f'(x;W) α(f(x;W))`, `f(x;W) = x exp(-∑_m W_m x^{-m})`,
as a multiple of `α_{N-|β|}` (sphere/paper.tex l.1121–1123).  With `M = N - |β|`:
`f^{-M}` has the coefficient `(M^{deg β}/β!) x^{-M-|β|}` at `W^β`, and
`f' f^{-M-1} = -(1/M) ∂_x f^{-M}`, which gives `(N/M) M^{deg β}/β!`.  For `M = 0` the mode
`α_0 = 0` does not occur. -/
noncomputable def thc (β : ℕ+ →₀ ℕ) (N : ℤ) : ℂ :=
  if N = (lvl β : ℤ) then 0
  else (N : ℂ) / ((N : ℂ) - (lvl β : ℂ)) * linExpCoef (fun _ => (N : ℂ) - (lvl β : ℂ)) β

/-- `f'(x;W) α(f(x;W))` at `x^{-N-1}`: the family `β ↦ thc β N • α_{N-|β|}`. -/
noncomputable def thF (N : ℤ) : (ℕ+ →₀ ℕ) → Module.End ℂ Fock :=
  fun β => thc β N • alphaOp (N - (lvl β : ℤ))

/-- `f'(x;W) α(f(x;W))` at `x^{-N-1}` as a series. -/
noncomputable def ThS (N : ℤ) : OpS := thF N

/-- The family of coefficients of a series. -/
noncomputable def cfs (Φ : OpS) : (ℕ+ →₀ ℕ) → Module.End ℂ Fock :=
  fun β => MvPowerSeries.coeff β Φ

section GenericRing

variable {R : Type*} [Ring R]

theorem inv_ode (k : ℕ) (A V L : MvPowerSeries ℕ+ R) (hAV : A * V = 1) (hVA : V * A = 1)
    (hA : DkS k A = -(A * L)) (h1 : DkS k (1 : MvPowerSeries ℕ+ R) = 0) : DkS k V = L * V := by
  have h := DkS_mul k A V
  rw [hAV, h1, hA] at h
  have h2 : A * DkS k V = A * L * V := by
    rw [eq_neg_of_add_eq_zero_right h.symm]
    noncomm_ring
  calc DkS k V = V * A * DkS k V := by rw [hVA, one_mul]
    _ = V * (A * L * V) := by rw [mul_assoc, h2]
    _ = V * A * (L * V) := by simp only [mul_assoc]
    _ = L * V := by rw [hVA, one_mul]

theorem conj_ode (k : ℕ) (A V L a : MvPowerSeries ℕ+ R) (hA : DkS k A = -(A * L))
    (hV : DkS k V = L * V) (ha : DkS k a = 0) :
    DkS k (A * a * V) = A * (a * L - L * a) * V := by
  rw [DkS_mul, DkS_mul, ha, hV, hA, mul_zero, add_zero]
  noncomm_ring

end GenericRing

/-! ### `D_k` on `OpS` -/

theorem DkS_C (k : ℕ) (a : Module.End ℂ Fock) : DkS k (MvPowerSeries.C a : OpS) = 0 := by
  classical
  have hz : ∀ (i : ℕ+) (δ : ℕ+ →₀ ℕ),
      MvPowerSeries.coeff δ (pdS i (MvPowerSeries.C a : OpS)) = 0 := by
    intro i δ
    rw [coeff_pdN, MvPowerSeries.coeff_C, if_neg (add_single_ne_zero δ i), smul_zero]
  refine MvPowerSeries.ext fun β => ?_
  rw [coeff_DkF, hz, zero_add, map_zero]
  exact Finset.sum_eq_zero fun m _ => by rw [hz, smul_zero]

theorem DkS_add (k : ℕ) (Φ Φ' : OpS) : DkS k (Φ + Φ') = DkS k Φ + DkS k Φ' := by
  refine MvPowerSeries.ext fun β => ?_
  exact DkF_add' k Φ Φ' β

theorem DkS_neg (k : ℕ) (Φ : OpS) : DkS k (-Φ) = -DkS k Φ := by
  have h := DkS_add k Φ (-Φ)
  have h0 : DkS k (0 : OpS) = 0 := by
    refine MvPowerSeries.ext fun β => ?_
    exact DkF_zero' k β
  rw [add_neg_cancel, h0] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem C_smul' (c : ℂ) (a : Module.End ℂ Fock) :
    (MvPowerSeries.C (c • a) : OpS) = c • MvPowerSeries.C a := by
  classical
  refine MvPowerSeries.ext fun β => ?_
  rw [MvPowerSeries.coeff_C]
  show _ = c • MvPowerSeries.coeff β (MvPowerSeries.C a : OpS)
  rw [MvPowerSeries.coeff_C]
  split_ifs <;> simp

section Conj

variable {U : Fock →ₗ[ℂ] HH} (hU : IsDiffeoU U) (hF : Cited_FeiginFuchsOperators)

include hU

theorem constantCoeff_UdS : MvPowerSeries.constantCoeff (UdS U) = ((1 : (Module.End ℂ Fock)ˣ) :
    Module.End ℂ Fock) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact Udg_zero hU

/-- `(U(W)^†)^{-1}`, which exists because `U(0)^† = id`. -/
noncomputable def VdS (U : Fock →ₗ[ℂ] HH) : OpS := MvPowerSeries.invOfUnit (UdS U) 1

theorem UdS_mul_VdS : UdS U * VdS U = 1 :=
  MvPowerSeries.mul_invOfUnit _ _ (constantCoeff_UdS hU)

theorem VdS_mul_UdS : VdS U * UdS U = 1 :=
  MvPowerSeries.invOfUnit_mul _ _ (constantCoeff_UdS hU)

include hF

theorem UdS_ode (k : ℕ) (hk : 1 ≤ k) :
    DkS k (UdS U) = -(UdS U * MvPowerSeries.C (ffOp (0 : ℂ) 0 (-(k : ℤ)))) := by
  refine MvPowerSeries.ext fun β => ?_
  rw [map_neg, MvPowerSeries.coeff_mul_C]
  exact Udg_ode hU hF k hk β

theorem VdS_ode (k : ℕ) (hk : 1 ≤ k) :
    DkS k (VdS U) = MvPowerSeries.C (ffOp (0 : ℂ) 0 (-(k : ℤ))) * VdS U :=
  inv_ode k _ _ _ (UdS_mul_VdS hU) (VdS_mul_UdS hU) (UdS_ode hU hF k hk) (DkS_C k 1)

/-- `Ψ(W,x) = U(W)^† α(x) (U(W)^†)^{-1}` at `x^{-N-1}`. -/
noncomputable def PsS (U : Fock →ₗ[ℂ] HH) (N : ℤ) : OpS :=
  UdS U * MvPowerSeries.C (alphaOp N) * VdS U

/-- `D_k Ψ = -∂_x(x^{1-k} Ψ)` at `x^{-N-1}` (sphere/paper.tex l.1120). -/
theorem PsS_ode (k : ℕ) (hk : 1 ≤ k) (N : ℤ) :
    DkS k (PsS U N) = (N : ℂ) • PsS U (N - k) := by
  have hc : alphaOp N * ffOp (0 : ℂ) 0 (-(k : ℤ)) - ffOp (0 : ℂ) 0 (-(k : ℤ)) * alphaOp N =
      (N : ℂ) • alphaOp (N - k) := by
    refine LinearMap.ext fun f => ?_
    have h := ffOp_alphaOp k hk N f
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply]
    rw [← neg_sub, h, neg_smul, neg_neg]
  unfold PsS
  have hC : (MvPowerSeries.C ((N : ℂ) • alphaOp (N - k)) : OpS) =
      MvPowerSeries.C (alphaOp N) * MvPowerSeries.C (ffOp (0 : ℂ) 0 (-(k : ℤ))) -
        MvPowerSeries.C (ffOp (0 : ℂ) 0 (-(k : ℤ))) * MvPowerSeries.C (alphaOp N) := by
    rw [← map_mul, ← map_mul, ← map_sub, hc]
  have e : (N : ℂ) • (UdS U * MvPowerSeries.C (alphaOp (N - k)) * VdS U) =
      UdS U * MvPowerSeries.C ((N : ℂ) • alphaOp (N - k)) * VdS U := by
    rw [C_smul', mul_smul_comm, smul_mul_assoc]
  rw [conj_ode k _ _ _ _ (UdS_ode hU hF k hk) (VdS_ode hU hF k hk) (DkS_C k _), e, hC]

end Conj

/-! ### `f'(x;W) α(f(x;W))` -/

theorem lvl_eq_sum (β : ℕ+ →₀ ℕ) : (lvl β : ℂ) = ∑ m ∈ β.support, ((m : ℕ) : ℂ) * (β m : ℂ) := by
  rw [lvl, Finsupp.weight_apply, Finsupp.sum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [fockWeight, smul_eq_mul]
  push_cast
  ring

/-- `D_k(f' α(f)) = -∂_x(x^{1-k} f' α(f))` at `x^{-N-1}`, from `D_k f = -x^{1-k} f'`
(sphere/paper.tex l.1121–1123), on the coefficients. -/
theorem ThS_ode (k : ℕ) (hk : 1 ≤ k) (N : ℤ) (β : ℕ+ →₀ ℕ) :
    DkF k (thF N) β = (N : ℂ) • thF (N - k) β := by
  have hjk : ∀ j : ℕ, 1 ≤ j → ((j.toPNat' : ℕ+) : ℕ) = j := fun j hj => PNat.toPNat'_coe hj
  have hl1 : lvl (β + Finsupp.single k.toPNat' 1) = lvl β + k := by
    rw [lvl_add, lvl_single, hjk k hk]
  have hl2 : ∀ m ∈ β.support,
      lvl (β - Finsupp.single m 1 + Finsupp.single ((m : ℕ) + k).toPNat' 1) = lvl β + k := by
    intro m hm
    have e := congrArg lvl (sub_add_single hm)
    rw [lvl_add, lvl_single] at e
    rw [lvl_add, lvl_single, hjk _ (by omega)]
    omega
  have hidx : ∀ j : ℕ, j = lvl β + k → N - (j : ℤ) = N - k - (lvl β : ℤ) := fun j hj => by
    rw [hj]
    push_cast
    ring
  unfold DkF pdN
  simp only [thF]
  rw [hidx _ hl1, Finset.sum_congr rfl fun m hm => by rw [hidx _ (hl2 m hm)]]
  by_cases hM : N - k - (lvl β : ℤ) = 0
  · have h0 : alphaOp (N - k - (lvl β : ℤ)) = 0 := by
      rw [hM, alphaOp, if_neg (by omega), if_neg (by omega)]
    rw [h0]
    simp
  set M : ℂ := (N : ℂ) - k - (lvl β : ℂ) with hMdef
  have hM0 : M ≠ 0 := by
    intro h
    apply hM
    have : ((N - k - (lvl β : ℤ) : ℤ) : ℂ) = 0 := by
      push_cast
      exact h
    exact_mod_cast this
  have ht1 : thc (β + Finsupp.single k.toPNat' 1) N =
      (N : ℂ) / M * linExpCoef (fun _ => M) (β + Finsupp.single k.toPNat' 1) := by
    rw [thc, if_neg (by rw [hl1]; push_cast; omega), hl1]
    push_cast
    rw [hMdef]
    ring_nf
  have ht2 : ∀ m ∈ β.support,
      thc (β - Finsupp.single m 1 + Finsupp.single ((m : ℕ) + k).toPNat' 1) N =
      (N : ℂ) / M * linExpCoef (fun _ => M)
        (β - Finsupp.single m 1 + Finsupp.single ((m : ℕ) + k).toPNat' 1) := by
    intro m hm
    rw [thc, if_neg (by rw [hl2 m hm]; push_cast; omega), hl2 m hm]
    push_cast
    rw [hMdef]
    ring_nf
  have ht3 : thc β (N - k) = ((N : ℂ) - k) / M * linExpCoef (fun _ => M) β := by
    rw [thc, if_neg (by omega)]
    push_cast
    rw [hMdef]
  have hL1 : linExpCoef (fun _ => M) (β + Finsupp.single k.toPNat' 1) *
      ((β k.toPNat' : ℂ) + 1) = linExpCoef (fun _ => M) β * M :=
    linExpCoef_add_single _ β _
  have hL2 : ∀ m ∈ β.support, linExpCoef (fun _ => M)
        (β - Finsupp.single m 1 + Finsupp.single ((m : ℕ) + k).toPNat' 1) *
      (((β - Finsupp.single m 1 : ℕ+ →₀ ℕ) ((m : ℕ) + k).toPNat' : ℂ) + 1) =
      linExpCoef (fun _ => M) β * (β m : ℂ) := by
    intro m hm
    have h1 := linExpCoef_add_single (fun _ => M) (β - Finsupp.single m 1)
      ((m : ℕ) + k).toPNat'
    have h2 := linExpCoef_add_single (fun _ => M) (β - Finsupp.single m 1) m
    rw [sub_add_single hm] at h2
    have h3 : (((β - Finsupp.single m 1 : ℕ+ →₀ ℕ) m : ℕ) : ℂ) + 1 = (β m : ℂ) := by
      have h4 := Finsupp.mem_support_iff.mp hm
      rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
      have : β m - 1 + 1 = β m := by omega
      exact_mod_cast this
    rw [h3] at h2
    rw [h1, ← h2]
  simp only [← smul_assoc, ← Finset.sum_smul, ← add_smul, smul_smul]
  congr 1
  simp only [nsmul_eq_mul, smul_eq_mul, ht1, ht3]
  rw [Finset.sum_congr rfl fun m hm => by rw [ht2 m hm]]
  have hsum : ∑ m ∈ β.support, (((m : ℕ) * ((β - Finsupp.single m 1 : ℕ+ →₀ ℕ)
        ((m : ℕ) + k).toPNat' + 1) : ℕ) : ℂ) * ((N : ℂ) / M * linExpCoef (fun _ => M)
          (β - Finsupp.single m 1 + Finsupp.single ((m : ℕ) + k).toPNat' 1)) =
      (N : ℂ) / M * linExpCoef (fun _ => M) β * (lvl β : ℂ) := by
    rw [lvl_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h := hL2 m hm
    generalize ((β - Finsupp.single m 1 : ℕ+ →₀ ℕ) ((m : ℕ) + k).toPNat') = x at h ⊢
    push_cast
    linear_combination ((m : ℕ) : ℂ) * ((N : ℂ) / M) * h
  rw [hsum]
  push_cast
  have hl : (lvl β : ℂ) = (N : ℂ) - k - M := by
    rw [hMdef]
    ring
  rw [hl]
  linear_combination ((N : ℂ) / M) * hL1

theorem thc_zero (N : ℤ) (hN : N ≠ 0) : thc 0 N = 1 := by
  have h0 : lvl (0 : ℕ+ →₀ ℕ) = 0 := map_zero _
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  rw [thc, h0, if_neg (by simpa using hN)]
  simp [linExpCoef, hN']

theorem ThS_zero (N : ℤ) : thF N 0 = alphaOp N := by
  have h0 : lvl (0 : ℕ+ →₀ ℕ) = 0 := map_zero _
  unfold thF
  rw [h0]
  simp only [Nat.cast_zero, sub_zero]
  by_cases hN : N = 0
  · subst hN
    have hA : alphaOp 0 = 0 := by
      rw [alphaOp, if_neg (by omega), if_neg (by omega)]
    rw [hA, smul_zero]
  · rw [thc_zero N hN, one_smul]

/-! ### The conjugation identity -/

section Main

variable {U : Fock →ₗ[ℂ] HH} (hU : IsDiffeoU U) (hF : Cited_FeiginFuchsOperators)

include hU hF

/-- `U(W)^† α(x) (U(W)^†)^{-1} = f'(x;W) α(f(x;W))` (sphere/paper.tex l.1123–1127), at each
`x^{-N-1}`. -/
theorem PsS_eq_ThS (N : ℤ) : PsS U N = ThS N := by
  classical
  let en : (ℕ+ →₀ ℕ) → (ℕ+ →₀ ℕ) → (Module.End ℂ Fock →+ ℂ) := fun γ α =>
    { toFun := fun T => coeff γ (T (monomial α 1))
      map_zero' := by simp
      map_add' := fun S T => by rw [LinearMap.add_apply, coeff_add] }
  have key := fam_unique (ι := ℤ × (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ))
    (fun i β => en i.2.1 i.2.2 (cfs (PsS U i.1) β) - en i.2.1 i.2.2 (cfs (ThS i.1) β))
    (fun _ _ => True) ?_ ?_
  · refine MvPowerSeries.ext fun β => ?_
    refine LinearMap.ext fun f => ?_
    induction f using MvPolynomial.induction_on' with
    | add p q hp hq => rw [map_add, map_add, hp, hq]
    | monomial α c =>
      have hm : monomial α c = c • monomial α (1 : ℂ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hm, map_smul, map_smul]
      congr 1
      ext γ
      have h := key (lvl β) (N, γ, α) trivial β rfl
      exact sub_eq_zero.mp h
  · rintro ⟨N, γ, α⟩ -
    have h1 : cfs (PsS U N) 0 = alphaOp N := by
      show MvPowerSeries.coeff 0 (PsS U N) = _
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PsS, map_mul, map_mul,
        MvPowerSeries.constantCoeff_C, constantCoeff_UdS hU, VdS,
        MvPowerSeries.constantCoeff_invOfUnit]
      simp
    have h2 : cfs (ThS N) 0 = alphaOp N := ThS_zero N
    simp only
    rw [h1, h2, sub_self]
  · rintro ⟨N, γ, α⟩ w - k hk δ hδ ih
    have e1 : DkF k (cfs (PsS U N)) δ = (N : ℂ) • cfs (PsS U (N - k)) δ :=
      congrArg (MvPowerSeries.coeff δ) (PsS_ode hU hF k hk N)
    have e2 : DkF k (cfs (ThS N)) δ = (N : ℂ) • cfs (ThS (N - k)) δ := ThS_ode k hk N δ
    have h3 : DkF k (fun β => en γ α (cfs (PsS U N) β) - en γ α (cfs (ThS N) β)) δ =
        en γ α (DkF k (cfs (PsS U N)) δ) - en γ α (DkF k (cfs (ThS N)) δ) := by
      rw [DkF_map, DkF_map]
      simp only [DkF, pdN, smul_sub, Finset.sum_sub_distrib]
      abel
    simp only
    rw [h3, e1, e2]
    have h4 := ih (N - k, γ, α) (lvl δ) (by omega) trivial δ rfl
    simp only at h4
    have h5 : ∀ T : Module.End ℂ Fock, en γ α ((N : ℂ) • T) = (N : ℂ) * en γ α T := fun T => by
      show coeff γ (((N : ℂ) • T) (monomial α 1)) = _
      rw [LinearMap.smul_apply, coeff_smul, smul_eq_mul]
      rfl
    rw [h5, h5, ← mul_sub, h4, mul_zero]

/-- `U(W)^† α_N = (f' α(f))_N U(W)^†` on the coefficient of `W^β`. -/
theorem Udg_alphaOp (N : ℤ) (β : ℕ+ →₀ ℕ) :
    Udg U β ∘ₗ alphaOp N = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β,
      thF N p.1 ∘ₗ Udg U p.2 := by
  classical
  have h : UdS U * MvPowerSeries.C (alphaOp N) = ThS N * UdS U := by
    rw [← PsS_eq_ThS hU hF N, PsS, mul_assoc, mul_assoc, VdS_mul_UdS hU, mul_one]
  have h1 := congrArg (MvPowerSeries.coeff β) h
  rw [MvPowerSeries.coeff_mul_C, MvPowerSeries.coeff_mul] at h1
  exact h1

end Main

end Virasoro.Sphere
