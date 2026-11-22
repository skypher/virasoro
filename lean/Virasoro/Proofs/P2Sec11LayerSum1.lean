import Virasoro.Proofs.P2Sec11LayerTrace
import Virasoro.Proofs.TopLayerCoeffF

/-!
# Proposition 11.2(ii), first step: tools (paper.tex l.2461–2485)

* a rational function whose Laurent expansion at `a` is a power series `Φ` is regular at `a`
  with value `Φ(0)`;
* the Jantzen vertex form `ρ^{(i)}` computed with power-series families:
  `ρ_x(a(x),b(x)) = x^i ρ^{(i)}(a(0),b(0)) + O(x^{i+1})` (l.2478), from part (i).
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial Verma

section Eval

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- If the Laurent expansion of `f` at `a` is a power series `Φ`, then `f` has no pole at `a`
and `f(a) = Φ(0)`. -/
theorem regular_of_expandAt {f : RatFunc 𝔽} {a : 𝔽} {Φ : PowerSeries 𝔽}
    (h : expandAt f a = HahnSeries.ofPowerSeries ℤ 𝔽 Φ) :
    poleOrder f a = 0 ∧ RatFunc.eval (RingHom.id 𝔽) a f = PowerSeries.constantCoeff Φ := by
  constructor
  · unfold poleOrder
    rw [h]
    have h0 := ordGE_ofPowerSeries Φ
    by_cases hΦ : HahnSeries.ofPowerSeries ℤ 𝔽 Φ = 0
    · rw [hΦ]; simp
    · have : (0 : ℤ) ≤ (HahnSeries.ofPowerSeries ℤ 𝔽 Φ).order := by
        by_contra hlt
        push_neg at hlt
        exact hΦ (HahnSeries.coeff_order_eq_zero.mp (ordGE_iff.1 h0 _ hlt))
      omega
  · have hden : f.denom ≠ 0 := RatFunc.denom_ne_zero f
    have hs0 : HahnSeries.ofPowerSeries ℤ 𝔽 (shiftPS a f.denom) ≠ 0 := fun h0 =>
      shiftPS_ne_zero a hden (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by rw [h0, map_zero]))
    have e : shiftPS a f.num = shiftPS a f.denom * Φ := by
      apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      have hf : expandHom a f = HahnSeries.ofPowerSeries ℤ 𝔽 (shiftPS a f.num) /
          HahnSeries.ofPowerSeries ℤ 𝔽 (shiftPS a f.denom) := by
        conv_lhs => rw [← RatFunc.num_div_denom f]
        rw [map_div₀, expandHom_algebraMap, expandHom_algebraMap]
      rw [map_mul, ← h, expandAt_eq, hf, mul_div_cancel₀ _ hs0]
    have e0 := congrArg PowerSeries.constantCoeff e
    rw [map_mul, constantCoeff_shiftPS, constantCoeff_shiftPS] at e0
    have hne : f.denom.eval a ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at e0
      obtain ⟨u, v, huv⟩ := RatFunc.isCoprime_num_denom f
      have := congrArg (Polynomial.eval a) huv
      rw [eval_add, eval_mul, eval_mul, e0, hz, mul_zero, mul_zero, add_zero, eval_one] at this
      exact zero_ne_one this
    rw [RatFunc.eval, eval₂_id, eval₂_id, e0, mul_div_cancel_left₀ _ hne]

end Eval

variable {c μ d : ℂ}

/-- The truncation of a power-series family is a polynomial family. -/
theorem trunc_family {N i : ℕ} {v : Nat.Partition N → ℂ} {V : Nat.Partition N → PowerSeries ℂ}
    (hV : PSFam (gramLocal c μ N) i v V) :
    IsJFamily c μ N i v fun Y => PowerSeries.trunc (i + 1) (V Y) := by
  obtain ⟨hV0, hdvd⟩ := hV
  refine ⟨fun Y => ?_, fun Y => ?_⟩
  · rw [← hV0 Y, ← Polynomial.coeff_zero_eq_eval_zero, PowerSeries.coeff_trunc,
      if_pos (by omega), PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    rw [← Polynomial.coeff_coe, coe_mulVec]
    have e : (fun Z => ((PowerSeries.trunc (i + 1) (V Z) : ℂ[X]) : PowerSeries ℂ))
        = V + fun Z => ((PowerSeries.trunc (i + 1) (V Z) : ℂ[X]) : PowerSeries ℂ) - V Z := by
      funext Z
      simp
    rw [e, Matrix.mulVec_add, Pi.add_apply]
    have h1 : (PowerSeries.X : PowerSeries ℂ) ^ i ∣ (gramLocal c μ N).mulVec V Y
        + (gramLocal c μ N).mulVec
          (fun Z => ((PowerSeries.trunc (i + 1) (V Z) : ℂ[X]) : PowerSeries ℂ) - V Z) Y :=
      dvd_add (hdvd Y) (dvd_mulVec (fun Z => X_pow_dvd_coe_trunc_sub (V Z) (by omega)) Y)
    exact (PowerSeries.X_pow_dvd_iff.1 h1) m hm

/-- The torus matrix `ρ_N(c,μ+x,d)` over `ℂ⟦x⟧`. -/
noncomputable def torusLocal (c μ d : ℂ) (N : ℕ) :
    Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries ℂ) :=
  torus (PowerSeries.C c) (PowerSeries.C μ + PowerSeries.X) (PowerSeries.C d) N

theorem torusLocal_eq_map_coe (c μ d : ℂ) (N : ℕ) :
    torusLocal c μ d N = (torusShift c μ d N).map (Polynomial.coeToPowerSeries.ringHom) := by
  have := torus_map (Polynomial.coeToPowerSeries.ringHom (R := ℂ)) (C c) (C μ + X) (C d) N
  rw [torusShift, ← this, torusLocal]
  simp [Polynomial.coeToPowerSeries.ringHom]

/-- Part (i) of Proposition 11.2 for the primary pairing over `ℂ[x]`, as a hypothesis. -/
def VertexPartI (c μ d : ℂ) : Prop :=
  ∀ (i N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
    (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]),
    IsJFamily c μ N₁ i a wa → IsJFamily c μ N₂ i a₂ wb →
      VertexClausesAt c μ d i (pairing (C c) (C μ + X) (C d)) N₁ N₂ a a₂ wa wb

/-- `ρ^{(i)}(u,v)` with any polynomial families, and `ρ_x(𝒥^{(i)},𝒥^{(i)}) ⊂ x^i ℂ[x]`. -/
theorem vform_fam (HV : VertexPartI c μ d) {N i : ℕ} {u v : Nat.Partition N → ℂ}
    {wu wv : Nat.Partition N → ℂ[X]} (hu : IsJFamily c μ N i u wu)
    (hv : IsJFamily c μ N i v wv) :
    (X : ℂ[X]) ^ i ∣ wu ⬝ᵥ (torusShift c μ d N).mulVec wv ∧
      (wu ⬝ᵥ (torusShift c μ d N).mulVec wv).coeff i = vform c μ d N i u v := by
  have hT := isPrimaryPairing_pairing (c := C c) (h := C μ + (X : ℂ[X])) (C d)
  have key : ∀ w w' : Nat.Partition N → ℂ[X],
      pairing (C c) (C μ + X) (C d) (pbwCoord N w) (pbwCoord N w') =
        w ⬝ᵥ (torusShift c μ d N).mulVec w' := fun w w' => primary_pbwCoord hT N w w'
  have h := HV i N N u v wu wv hu hv
  refine ⟨by rw [← key]; exact h.1, ?_⟩
  have hu' : ∃ w, IsJFamily c μ N i u w := ⟨wu, hu⟩
  have hv' : ∃ w, IsJFamily c μ N i v w := ⟨wv, hv⟩
  rw [vform, dif_pos hu', dif_pos hv', vformFam, ← key, ← key]
  exact (h.2.1 _ _ hu'.choose_spec hv'.choose_spec).symm

theorem dvd_dot_left {ι : Type*} [Fintype ι] {R : Type*} [CommRing R] {q : R} {D W : ι → R}
    (h : ∀ j, q ∣ D j) : q ∣ D ⬝ᵥ W :=
  Finset.dvd_sum fun j _ => Dvd.dvd.mul_right (h j) _

theorem dvd_dot_right {ι : Type*} [Fintype ι] {R : Type*} [CommRing R] {q : R} {D W : ι → R}
    (h : ∀ j, q ∣ W j) : q ∣ D ⬝ᵥ W :=
  Finset.dvd_sum fun j _ => Dvd.dvd.mul_left (h j) _

/-- `ρ_x(a(x),b(x)) = x^i ρ^{(i)}(a(0),b(0)) + O(x^{i+1})` for power-series families of order
`i` (l.2478). -/
theorem vform_ps (HV : VertexPartI c μ d) {N i : ℕ} {u v : Nat.Partition N → ℂ}
    {Vu Vv : Nat.Partition N → PowerSeries ℂ} (hu : PSFam (gramLocal c μ N) i u Vu)
    (hv : PSFam (gramLocal c μ N) i v Vv) :
    (PowerSeries.X : PowerSeries ℂ) ^ i ∣ Vu ⬝ᵥ (torusLocal c μ d N).mulVec Vv ∧
      PowerSeries.coeff i (Vu ⬝ᵥ (torusLocal c μ d N).mulVec Vv) = vform c μ d N i u v := by
  set φ := Polynomial.coeToPowerSeries.ringHom (R := ℂ) with hφ
  set wu : Nat.Partition N → ℂ[X] := fun Y => PowerSeries.trunc (i + 1) (Vu Y) with hwu
  set wv : Nat.Partition N → ℂ[X] := fun Y => PowerSeries.trunc (i + 1) (Vv Y) with hwv
  obtain ⟨h1, h2⟩ := vform_fam HV (trunc_family hu) (trunc_family hv)
  set P : ℂ[X] := wu ⬝ᵥ (torusShift c μ d N).mulVec wv with hP
  have hDu : ∀ Y, (PowerSeries.X : PowerSeries ℂ) ^ (i + 1) ∣ φ (wu Y) - Vu Y := fun Y =>
    X_pow_dvd_coe_trunc_sub (Vu Y) le_rfl
  have hDv : ∀ Y, (PowerSeries.X : PowerSeries ℂ) ^ (i + 1) ∣ φ (wv Y) - Vv Y := fun Y =>
    X_pow_dvd_coe_trunc_sub (Vv Y) le_rfl
  have hPc : φ P = (fun Y => φ (wu Y)) ⬝ᵥ (torusLocal c μ d N).mulVec fun Y => φ (wv Y) := by
    rw [hP, RingHom.map_dotProduct, torusLocal_eq_map_coe]
    congr 1
    funext Y
    exact RingHom.map_mulVec φ (torusShift c μ d N) wv Y
  have hsplit : Vu ⬝ᵥ (torusLocal c μ d N).mulVec Vv = φ P -
      (Vu ⬝ᵥ (torusLocal c μ d N).mulVec (fun Y => φ (wv Y) - Vv Y) +
        (fun Y => φ (wu Y) - Vu Y) ⬝ᵥ (torusLocal c μ d N).mulVec fun Y => φ (wv Y)) := by
    have e1 : (fun Y => φ (wv Y)) = Vv + fun Y => φ (wv Y) - Vv Y := by funext Y; simp
    have e2 : (fun Y => φ (wu Y)) = Vu + fun Y => φ (wu Y) - Vu Y := by funext Y; simp
    have e3 : (fun Y => φ (wu Y)) ⬝ᵥ (torusLocal c μ d N).mulVec (fun Y => φ (wv Y)) =
        Vu ⬝ᵥ (torusLocal c μ d N).mulVec Vv +
          Vu ⬝ᵥ (torusLocal c μ d N).mulVec (fun Y => φ (wv Y) - Vv Y) +
          (fun Y => φ (wu Y) - Vu Y) ⬝ᵥ (torusLocal c μ d N).mulVec fun Y => φ (wv Y) := by
      conv_lhs => rw [e2]
      rw [add_dotProduct]
      congr 1
      conv_lhs => rw [e1]
      rw [Matrix.mulVec_add, dotProduct_add]
    rw [hPc, e3]
    ring
  have hE : (PowerSeries.X : PowerSeries ℂ) ^ (i + 1) ∣
      Vu ⬝ᵥ (torusLocal c μ d N).mulVec (fun Y => φ (wv Y) - Vv Y) +
        (fun Y => φ (wu Y) - Vu Y) ⬝ᵥ (torusLocal c μ d N).mulVec fun Y => φ (wv Y) :=
    dvd_add (dvd_dot_right fun j => dvd_mulVec hDv j) (dvd_dot_left hDu)
  have hφX : φ ((X : ℂ[X]) ^ i) = (PowerSeries.X : PowerSeries ℂ) ^ i := by
    simp [hφ, Polynomial.coeToPowerSeries.ringHom]
  constructor
  · rw [hsplit]
    refine dvd_sub ?_ ((pow_dvd_pow _ (Nat.le_succ i)).trans hE)
    rw [← hφX]
    exact map_dvd φ h1
  · rw [hsplit, map_sub, (PowerSeries.X_pow_dvd_iff.1 hE) i (Nat.lt_succ_self i), sub_zero,
      ← h2]
    exact Polynomial.coeff_coe P i

end Virasoro
