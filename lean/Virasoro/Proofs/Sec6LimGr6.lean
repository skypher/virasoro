import Virasoro.Proofs.Sec6LimGr5
import Virasoro.Proofs.Sec6H13Laurent
import Virasoro.Proofs.KacField

/-!
# Proposition 6.7, the chain limit (b): the denominator has the same order on both lines

By the Kac determinant formula `∏_{M ≤ N} det G_M(c(b),Δ) = ∏_M K_M ∏_a (Δ − h_a(b))^{p(M−ℓ_a)}`.
* At `b = b⋆` the factor `Δ − h_a(b⋆)` vanishes to order one at `Δ = λ` exactly when
  `h_a(b⋆) = λ`, so the order is `e = ∑_{M,a : h_a(b⋆)=λ} p(M−ℓ_a)`.
* Along the germ `(b⋆ + t, λ + 2b⋆w t)` the factor `Δ − h_a(b)` is `t·(2b⋆w − 2b⋆ḣ_a + O(t))` when
  `h_a(b⋆) = λ` and a unit otherwise (`w` is transcendental), so the order is the same `e`.
-/

namespace Virasoro.ChainLim

open Polynomial Finset
open scoped LaurentSeries

open Classical in
/-- `e = ∑_{M ≤ N} ∑_{a, h_a(b⋆) = λ} p(M − ℓ_a)`. -/
noncomputable def eRes (bs lam : ℂ) (N : ℕ) : ℕ :=
  ∑ M ∈ range (N + 1), ∑ a ∈ labels M,
    if kacHL a bs = lam then Fintype.card (Nat.Partition (M - a.lvl)) else 0

theorem prod_split {α M : Type*} [CommMonoid M] (s : Finset α) (t : M) (f g : α → M)
    (n : α → ℕ) (P : α → Prop) [DecidablePred P]
    (h : ∀ a ∈ s, f a ^ n a = t ^ (if P a then n a else 0) * g a ^ n a) :
    ∏ a ∈ s, f a ^ n a = t ^ (∑ a ∈ s, if P a then n a else 0) * ∏ a ∈ s, g a ^ n a := by
  rw [prod_congr rfl h, prod_mul_distrib, prod_pow_eq_pow_sum]

theorem prod_split2 {β M : Type*} [CommMonoid M] (s : Finset β) (t : M) (κ G : β → M)
    (e : β → ℕ) :
    ∏ b ∈ s, (κ b * (t ^ e b * G b)) = t ^ (∑ b ∈ s, e b) * ∏ b ∈ s, (κ b * G b) := by
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  exact prod_congr rfl fun b _ => mul_left_comm _ _ _

theorem taylor_prod' {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (r : ℂ) :
    taylor r (∏ i ∈ s, f i) = ∏ i ∈ s, taylor r (f i) := by
  rw [← coe_taylorAlgHom]
  exact map_prod (taylorAlgHom r) f s

open Classical in
/-- At `b = b⋆`: `D(λ + u) = u^e T₁(u)` with `T₁(0) ≠ 0`. -/
theorem kac_taylor (hK : Cited_KacDeterminant) {bs : ℂ} (hbs : bs ≠ 0) (lam : ℂ) (N : ℕ) :
    ∃ T₁ : ℂ[X], taylor lam (denH (C (kacC bs)) X N) = X ^ eRes bs lam N * T₁ ∧
      T₁.eval 0 ≠ 0 := by
  let g : Label → ℂ[X] := fun a => if kacHL a bs = lam then 1 else X + C (lam - kacHL a bs)
  let n : ℕ → Label → ℕ := fun M a => Fintype.card (Nat.Partition (M - a.lvl))
  refine ⟨∏ M ∈ range (N + 1), (C (kacK M : ℂ) * ∏ a ∈ labels M, g a ^ n M a), ?_, ?_⟩
  · have hfac : ∀ M, ∀ a ∈ labels M, taylor lam (X - C (kacHL a bs)) ^ n M a =
        X ^ (if kacHL a bs = lam then n M a else 0) * g a ^ n M a := by
      intro M a _
      rw [map_sub, taylor_X, taylor_C]
      by_cases h : kacHL a bs = lam
      · simp [g, h]
      · simp only [g, if_neg h, pow_zero, one_mul]
        congr 1
        rw [map_sub]
        ring
    have hdet : ∀ M, taylor lam (detR (C (kacC bs)) X M) =
        C (kacK M : ℂ) * (X ^ (∑ a ∈ labels M, if kacHL a bs = lam then n M a else 0) *
          ∏ a ∈ labels M, g a ^ n M a) := by
      intro M
      have e : detR (C (kacC bs)) X M = (gramPoly (kacC bs) M).det := rfl
      rw [e, kac_det_const hK hbs M, kacProd, taylor_mul, taylor_C, taylor_prod']
      simp_rw [taylor_pow]
      rw [prod_split _ X _ g (n M) (fun a => kacHL a bs = lam) (hfac M)]
    rw [denH, taylor_prod']
    simp_rw [hdet]
    rw [prod_split2]
    rfl
  · rw [eval_prod, prod_ne_zero_iff]
    intro M _
    rw [eval_mul, eval_C, eval_prod]
    refine mul_ne_zero (Nat.cast_ne_zero.2 (kacK_ne_zero M)) (prod_ne_zero_iff.2 fun a _ => ?_)
    rw [eval_pow]
    refine pow_ne_zero _ ?_
    by_cases h : kacHL a bs = lam
    · simp [g, h]
    · simp [g, h, sub_ne_zero.2 (Ne.symm h)]

section Germ

variable {K : Type} [Field K] [CharZero K] [Algebra ℂ K]

theorem hdotK_map (p p' : ℕ) (g : Label) :
    hdotK (K := K) p p' g = algebraMap ℂ K (hdotK (K := ℂ) p p' g) := by
  simp only [hdotK, map_div₀, map_sub, map_mul, map_pow, map_one, map_natCast, map_ofNat]

open Classical in
/-- Along the germ: `D(c(b), λ + 2b⋆w t) = t^e V` with `V` regular and `V(0) ≠ 0`. -/
theorem kac_germ (hK : Cited_KacDeterminant) {p p' : ℕ} (hp : (p : ℂ) ≠ 0) (hp' : (p' : ℂ) ≠ 0)
    {bs : ℂ} (hbs : bs ≠ 0) (hrel : (p : ℂ) * bs ^ 2 + p' = 0) {w : K}
    (hw : ∀ z : ℂ, w ≠ algebraMap ℂ K z) (lam : ℂ) (N : ℕ) :
    ∃ V : K⸨X⸩, ∃ v : K, v ≠ 0 ∧ RegVal V v ∧
      denH (kacC (bGerm (algebraMap ℂ K bs)))
        (HahnSeries.C (algebraMap ℂ K lam) + tX * HahnSeries.C (2 * algebraMap ℂ K bs * w)) N =
        tX ^ eRes bs lam N * V := by
  set bK := algebraMap ℂ K bs with hbK
  have hbK0 : bK ≠ 0 := (_root_.map_ne_zero _).2 hbs
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (by exact_mod_cast hp)
  have hp'K : (p' : K) ≠ 0 := Nat.cast_ne_zero.2 (by exact_mod_cast hp')
  have hrelK : (p : K) * bK ^ 2 + p' = 0 := by
    have := congrArg (algebraMap ℂ K) hrel
    simpa [hbK] using this
  set b := bGerm bK with hb
  set Z : K⸨X⸩ := HahnSeries.C (algebraMap ℂ K lam) + tX * HahnSeries.C (2 * bK * w) with hZ
  let n : ℕ → Label → ℕ := fun M a => Fintype.card (Nat.Partition (M - a.lvl))
  let H : Label → K⸨X⸩ := fun a => if kacHL a bs = lam then (Z - kacHL a b) / tX else Z - kacHL a b
  let val : Label → K := fun a =>
    if kacHL a bs = lam then 2 * bK * w - 2 * bK * hdotK p p' a
    else algebraMap ℂ K (lam - kacHL a bs)
  have hX0 : RegVal (tX : K⸨X⸩) 0 := ⟨ordGE_single_one, by simp [tX]⟩
  have hhK : ∀ a : Label, kacHL a bK = algebraMap ℂ K (kacHL a bs) := fun a =>
    (map_kacHL (algebraMap ℂ K) a bs).symm
  have hH : ∀ a : Label, RegVal (H a) (val a) ∧ val a ≠ 0 := by
    intro a
    by_cases h : kacHL a bs = lam
    · have e : (Z - kacHL a b) / tX = HahnSeries.C (2 * bK * w) -
          (kacHL a b - HahnSeries.C (kacHL a bK)) / tX := by
        rw [hhK a, h, hZ]
        field_simp [tX_ne_zero]
        ring
      simp only [H, val, if_pos h]
      refine ⟨?_, ?_⟩
      · rw [e]
        exact (regVal_C _).sub (regVal_kacH_slope hbK0 hpK hp'K hrelK a)
      · rw [← mul_sub]
        refine mul_ne_zero (mul_ne_zero two_ne_zero hbK0) (sub_ne_zero.2 ?_)
        rw [hdotK_map]
        exact hw _
    · simp only [H, val, if_neg h]
      refine ⟨?_, ?_⟩
      · have := ((regVal_C (algebraMap ℂ K lam)).add (hX0.mul (regVal_C (2 * bK * w)))).sub
          (regVal_kacH hbK0 (a.1 : ℤ) (a.2 : ℤ))
        have hv : algebraMap ℂ K (lam - kacHL a bs) =
            algebraMap ℂ K lam + 0 * (2 * bK * w) - kacH (a.1 : ℤ) (a.2 : ℤ) bK := by
          rw [zero_mul, add_zero, map_sub, ← hhK a]
          rfl
        rw [hv]
        exact this
      · exact (_root_.map_ne_zero _).2 (sub_ne_zero.2 (Ne.symm h))
  have hfac : ∀ M, ∀ a ∈ labels M, (Z - kacHL a b) ^ n M a =
      tX ^ (if kacHL a bs = lam then n M a else 0) * H a ^ n M a := by
    intro M a _
    by_cases h : kacHL a bs = lam
    · simp only [H, if_pos h]
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ tX_ne_zero)]
    · simp only [H, if_neg h, pow_zero, one_mul]
  have hdet : ∀ M, detR (kacC b) Z M = (kacK M : K⸨X⸩) *
      (tX ^ (∑ a ∈ labels M, if kacHL a bs = lam then n M a else 0) *
        ∏ a ∈ labels M, H a ^ n M a) := by
    intro M
    have e : detR (kacC b) Z M = (gram (kacC b) Z M).det := rfl
    rw [e, ← gramPoly_det_eval, kac_det_const hK (bGerm_ne_zero hbK0) M, kacProd, eval_mul,
      eval_C, eval_prod]
    simp_rw [eval_pow, eval_sub, eval_X, eval_C]
    rw [prod_split _ tX _ H (n M) (fun a => kacHL a bs = lam) (hfac M)]
  refine ⟨∏ M ∈ range (N + 1), ((kacK M : K⸨X⸩) * ∏ a ∈ labels M, H a ^ n M a),
    ∏ M ∈ range (N + 1), ((kacK M : K) * ∏ a ∈ labels M, val a ^ n M a), ?_, ?_, ?_⟩
  · refine prod_ne_zero_iff.2 fun M _ => mul_ne_zero (Nat.cast_ne_zero.2 (kacK_ne_zero M))
      (prod_ne_zero_iff.2 fun a _ => pow_ne_zero _ (hH a).2)
  · exact RegVal.prod fun M _ => (regVal_natCast _).mul
      (RegVal.prod fun a _ => (hH a).1.pow _)
  · rw [denH]
    simp_rw [hdet]
    rw [prod_split2]
    rfl

end Germ

end Virasoro.ChainLim
