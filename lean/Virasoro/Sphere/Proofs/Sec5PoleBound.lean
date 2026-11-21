import Virasoro.Proofs.PoleBound
import Virasoro.Proofs.Sec5Jantzen
import Virasoro.Sphere.Proofs.Sec2HSeries
import Virasoro.Sphere.Statements.Sec5

/-!
# Sphere paper Theorem 5.1 (`thm:jantzen-bound`): the Jantzen pole-order bound

`sphere/paper.tex` l.1488–1496: `G_N(c⋆,Δ)⁻¹` has a pole of order `j_N(λ)` at `Δ = λ` (torus
Theorem 5.8); `γ_Y` is polynomial in `Δ`, so `ℬ_N` has pole order at most `j_N(λ)`; the
coefficients of `Φ̃⁻¹` are polynomial in `Δ` and `j_m(λ) ≤ j_N(λ)` for `m ≤ N`, so `H_N` has
pole order at most `j_N(λ)`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- If `G_N(c, a + x) S(x) = x^m`, the expansion of `ℬ_N` at `Δ = a` is
`x^{-m} ∑ γ_Y(a+x;Δ₄,Δ₃) S_{Y,Z}(x) γ_Z(a+x;Δ₁,Δ₂)`. -/
theorem expandAt_Bsph_of_scaled (c a : 𝔽) (Δe : Fin 4 → 𝔽) (N m : ℕ)
    (S : Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries 𝔽))
    (hS : gramLocal c a N * S = (PowerSeries.X : PowerSeries 𝔽) ^ m • 1) :
    expandAt (Bsph c Δe N) a = HahnSeries.ofPowerSeries ℤ 𝔽
        (∑ Y, ∑ Z, shiftPS a (gammaPoly (Δe 3) (Δe 2) N Y) * S Y Z *
          shiftPS a (gammaPoly (Δe 0) (Δe 1) N Z)) /
      HahnSeries.single (m : ℤ) (1 : 𝔽) := by
  classical
  set G := gramLocal c a N with hG
  set gL : Nat.Partition N → PowerSeries 𝔽 :=
    fun Y => shiftPS a (gammaPoly (Δe 3) (Δe 2) N Y) with hgL
  set gR : Nat.Partition N → PowerSeries 𝔽 :=
    fun Z => shiftPS a (gammaPoly (Δe 0) (Δe 1) N Z) with hgR
  have hGm : (gramPoly c N).map (shiftPS a) = G := (gramLocal_eq_map c a N).symm
  have hadjm : ∀ Y Z, shiftPS a ((gramPoly c N).adjugate Y Z) = G.adjugate Y Z := by
    intro Y Z
    rw [← hGm]
    have h := RingHom.map_adjugate (shiftPS a) (gramPoly c N)
    exact congrFun (congrFun h Y) Z
  have hnum : shiftPS a (Bnum c Δe N) = ∑ Y, ∑ Z, gL Y * G.adjugate Y Z * gR Z := by
    unfold Bnum
    rw [map_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [map_mul, map_mul, hadjm]
  have hdet : shiftPS a (gramPoly c N).det = G.det := (gramLocal_det c a N).symm
  have hadj : ∀ Y Y', (PowerSeries.X : PowerSeries 𝔽) ^ m * G.adjugate Y Y'
      = G.det * S Y Y' := by
    intro Y Y'
    have h1 : G.adjugate * (G * S) = G.det • S := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [hS, Matrix.mul_smul, Matrix.mul_one] at h1
    have h2 := congrFun (congrFun h1 Y) Y'
    simpa [Matrix.smul_apply, smul_eq_mul] using h2
  set Q : PowerSeries 𝔽 := ∑ Y, ∑ Z, gL Y * S Y Z * gR Z with hQ
  have hmain : (PowerSeries.X : PowerSeries 𝔽) ^ m * shiftPS a (Bnum c Δe N) = G.det * Q := by
    rw [hnum, hQ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    have e : (PowerSeries.X : PowerSeries 𝔽) ^ m * (gL Y * G.adjugate Y Z * gR Z)
        = gL Y * ((PowerSeries.X : PowerSeries 𝔽) ^ m * G.adjugate Y Z) * gR Z := by ring
    rw [e, hadj]
    ring
  have hdet0 : (HahnSeries.ofPowerSeries ℤ 𝔽 G.det) ≠ 0 := by
    intro h0
    exact gramLocal_det_ne_zero c a N
      (HahnSeries.ofPowerSeries_injective (by rw [h0, map_zero]))
  have hX0 : (HahnSeries.single (m : ℤ) (1 : 𝔽) : 𝔽⸨X⸩) ≠ 0 := by
    simp
  rw [expandAt_eq, Bsph, map_div₀, expandHom_algebraMap, expandHom_algebraMap, hdet,
    div_eq_div_iff hdet0 hX0]
  have h3 := congrArg (HahnSeries.ofPowerSeries ℤ 𝔽) hmain
  rw [map_mul, map_mul, HahnSeries.ofPowerSeries_X_pow] at h3
  rw [mul_comm, h3, mul_comm]

/-- If `G_N(c, a + x) S(x) = x^m`, the expansion of `ℬ_N` at `Δ = a` has order at least `-m`. -/
theorem ordGE_expandAt_Bsph (c a : 𝔽) (Δe : Fin 4 → 𝔽) (N m : ℕ)
    (S : Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries 𝔽))
    (hS : gramLocal c a N * S = (PowerSeries.X : PowerSeries 𝔽) ^ m • 1) :
    OrdGE (expandAt (Bsph c Δe N) a) (-(m : ℤ)) := by
  rw [expandAt_Bsph_of_scaled c a Δe N m S hS]
  have := (ordGE_ofPowerSeries (∑ Y, ∑ Z, shiftPS a (gammaPoly (Δe 3) (Δe 2) N Y) * S Y Z *
    shiftPS a (gammaPoly (Δe 0) (Δe 1) N Z))).div (HahnSeries.single (m : ℤ) (1 : 𝔽))
  rwa [HahnSeries.order_single one_ne_zero, zero_sub] at this

/-- The local Shapovalov matrix over `ℂ(Δ₁,…,Δ₄)` is the image of the one over `ℂ`. -/
theorem gramLocal_K4 (c a : ℂ) (N : ℕ) :
    gramLocal (cK c) (cK a) N
      = (gramLocal c a N).map (PowerSeries.map (algebraMap ℂ K4)) := by
  have := gram_map (PowerSeries.map (algebraMap ℂ K4)) (PowerSeries.C c)
    (PowerSeries.C a + PowerSeries.X) N
  rw [map_add, PowerSeries.map_C, PowerSeries.map_C, PowerSeries.map_X] at this
  exact this

/-- The pole order of `ℬ_N(c,Δ,Δ_i)` over `ℂ(Δ₁,…,Δ₄)` at `Δ = a` is at most the pole order of
`G_N(c,Δ)⁻¹` over `ℂ`. -/
theorem ordGE_expandAt_BsphK (c a : ℂ) (N : ℕ) :
    OrdGE (expandAt (Bsph (cK c) ΔK N) (cK a)) (-(poleOrderInv (gramLocal c a N) : ℤ)) := by
  classical
  have h0 := mul_scaledInv (gramLocal_det_ne_zero c a N) (matOrdGE_inv (gramLocal c a N))
  refine ordGE_expandAt_Bsph (cK c) (cK a) ΔK N
    (poleOrderInv (gramLocal c a N))
    ((scaledInv (gramLocal c a N) (poleOrderInv (gramLocal c a N))).map
      (PowerSeries.map (algebraMap ℂ K4))) ?_
  rw [gramLocal_K4, ← Matrix.map_mul, h0]
  refine Matrix.ext fun Y Y' => ?_
  rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.one_apply, smul_eq_mul, smul_eq_mul, map_mul, map_pow, PowerSeries.map_X]
  by_cases hY : Y = Y'
  · rw [if_pos hY, if_pos hY, map_one]
  · rw [if_neg hY, if_neg hY, map_zero]

/-! ### Rational functions regular at a point -/

/-- The subring of the rational functions that are regular at `a`. -/
noncomputable def regRing (a : 𝔽) : Subring (RatFunc 𝔽) where
  carrier := {r | OrdGE (expandHom a r) 0}
  mul_mem' := fun {x y} hx hy => by
    show OrdGE (expandHom a (x * y)) 0
    rw [map_mul]
    simpa using OrdGE.mul hx hy
  one_mem' := by
    show OrdGE (expandHom a 1) 0
    rw [map_one]
    exact ordGE_one
  add_mem' := fun {x y} hx hy => by
    show OrdGE (expandHom a (x + y)) 0
    rw [map_add]
    exact OrdGE.add hx hy
  zero_mem' := by
    show OrdGE (expandHom a 0) 0
    rw [map_zero]
    exact OrdGE.zero _
  neg_mem' := fun {x} hx => by
    show OrdGE (expandHom a (-x)) 0
    rw [map_neg]
    exact OrdGE.neg hx

theorem mem_regRing {a : 𝔽} {r : RatFunc 𝔽} : r ∈ regRing a ↔ OrdGE (expandAt r a) 0 :=
  Iff.rfl

theorem C_mem_regRing (a x : 𝔽) : RatFunc.C x ∈ regRing a := by
  show OrdGE (expandHom a (RatFunc.C x)) 0
  rw [expandHom_C]
  exact ordGE_C x

theorem X_mem_regRing (a : 𝔽) : (RatFunc.X : RatFunc 𝔽) ∈ regRing a := by
  show OrdGE (expandHom a RatFunc.X) 0
  rw [expandHom_X]
  refine OrdGE.add (ordGE_iff.2 fun m hm => ?_) (ordGE_C a)
  rw [HahnSeries.coeff_single_of_ne]
  omega

theorem ratCast_mem_regRing (a : 𝔽) (q : ℚ) : algebraMap ℚ (RatFunc 𝔽) q ∈ regRing a := by
  have h : algebraMap ℚ (RatFunc 𝔽) q = RatFunc.C (algebraMap ℚ 𝔽 q) :=
    RingHom.congr_fun (Subsingleton.elim (algebraMap ℚ (RatFunc 𝔽))
      ((RatFunc.C : 𝔽 →+* RatFunc 𝔽).comp (algebraMap ℚ 𝔽))) q
  rw [h]
  exact C_mem_regRing a _

theorem div_nat_mem_regRing {a : 𝔽} {x : RatFunc 𝔽} (hx : x ∈ regRing a) (n : ℕ) :
    x / (n : RatFunc 𝔽) ∈ regRing a := by
  have h : ((n : RatFunc 𝔽))⁻¹ = RatFunc.C ((n : 𝔽)⁻¹) := by
    rw [map_inv₀, map_natCast]
  rw [div_eq_mul_inv, h]
  exact (regRing a).mul_mem hx (C_mem_regRing a _)

theorem gbinom_mem_regRing {a : 𝔽} {e : RatFunc 𝔽} (he : e ∈ regRing a) (k : ℕ) :
    gbinom e k ∈ regRing a := by
  unfold gbinom
  refine div_nat_mem_regRing ((regRing a).prod_mem fun i _ => ?_) _
  exact (regRing a).sub_mem he (natCast_mem (regRing a) i)

/-- All coefficients of the power series lie in the subring. -/
def CoeffIn (R : Subring (RatFunc 𝔽)) (f : PowerSeries (RatFunc 𝔽)) : Prop :=
  ∀ n, PowerSeries.coeff n f ∈ R

theorem CoeffIn.mul {R : Subring (RatFunc 𝔽)} {f g : PowerSeries (RatFunc 𝔽)}
    (hf : CoeffIn R f) (hg : CoeffIn R g) : CoeffIn R (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact R.sum_mem fun p _ => R.mul_mem (hf p.1) (hg p.2)

theorem CoeffIn.one (R : Subring (RatFunc 𝔽)) : CoeffIn R 1 := by
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem CoeffIn.sub {R : Subring (RatFunc 𝔽)} {f g : PowerSeries (RatFunc 𝔽)}
    (hf : CoeffIn R f) (hg : CoeffIn R g) : CoeffIn R (f - g) := by
  intro n
  rw [map_sub]
  exact R.sub_mem (hf n) (hg n)

theorem CoeffIn.pow {R : Subring (RatFunc 𝔽)} {f : PowerSeries (RatFunc 𝔽)}
    (hf : CoeffIn R f) (k : ℕ) : CoeffIn R (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact CoeffIn.one R
  | succ k ih => rw [pow_succ]; exact ih.mul hf

theorem coeffIn_map_rat (a : 𝔽) (g : PowerSeries ℚ) :
    CoeffIn (regRing a) (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g) := by
  intro n
  rw [PowerSeries.coeff_map]
  exact ratCast_mem_regRing a _

theorem coeffIn_fpow {a : 𝔽} {f : PowerSeries (RatFunc 𝔽)} (hf : CoeffIn (regRing a) f)
    {e : RatFunc 𝔽} (he : e ∈ regRing a) : CoeffIn (regRing a) (fpow f e) := by
  intro n
  simp only [fpow, PowerSeries.coeff_mk]
  exact (regRing a).sum_mem fun k _ =>
    (regRing a).mul_mem (gbinom_mem_regRing he k) ((hf.sub (CoeffIn.one _)).pow k n)

theorem coeffIn_inv {R : Subring (RatFunc 𝔽)} {f : PowerSeries (RatFunc 𝔽)}
    (hf : CoeffIn R f) (h1 : PowerSeries.constantCoeff f = 1) : CoeffIn R f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv, h1, inv_one]
    split_ifs with hn
    · exact R.one_mem
    · refine R.mul_mem (R.neg_mem R.one_mem) (R.sum_mem fun p _ => ?_)
      split_ifs with hp
      · exact R.mul_mem (hf p.1) (ih p.2 hp)
      · exact R.zero_mem

theorem coeffIn_PhiTilde_inv (c a : 𝔽) (Δe : Fin 4 → 𝔽) :
    CoeffIn (regRing a) (PhiTilde c Δe)⁻¹ := by
  have h24 : (24 : RatFunc 𝔽) = ((24 : ℕ) : RatFunc 𝔽) := by norm_num
  have h2 : (2 : RatFunc 𝔽) = ((2 : ℕ) : RatFunc 𝔽) := by norm_num
  have hc : (RatFunc.C c - 1 : RatFunc 𝔽) ∈ regRing a :=
    (regRing a).sub_mem (C_mem_regRing a c) (regRing a).one_mem
  have a1 : (RatFunc.X - (RatFunc.C c - 1) / 24 : RatFunc 𝔽) ∈ regRing a := by
    rw [h24]
    exact (regRing a).sub_mem (X_mem_regRing a) (div_nat_mem_regRing hc 24)
  have a2 : ((RatFunc.C c - 1) / 24 - RatFunc.C (Δe 1) - RatFunc.C (Δe 2) : RatFunc 𝔽)
      ∈ regRing a := by
    rw [h24]
    exact (regRing a).sub_mem ((regRing a).sub_mem (div_nat_mem_regRing hc 24)
      (C_mem_regRing a _)) (C_mem_regRing a _)
  have a3 : ((RatFunc.C c - 1) / 2 - 4 * RatFunc.C (Δe 0 + Δe 1 + Δe 2 + Δe 3) : RatFunc 𝔽)
      ∈ regRing a := by
    rw [h2]
    have h4 : (4 : RatFunc 𝔽) = ((4 : ℕ) : RatFunc 𝔽) := by norm_num
    rw [h4]
    exact (regRing a).sub_mem (div_nat_mem_regRing hc 2) ((regRing a).mul_mem
      (natCast_mem (regRing a) 4) (C_mem_regRing a _))
  have e1 : nomeRatio (RatFunc 𝔽) =
      PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ) := (map_nomeRatio _).symm
  have e2 : (1 - zq (RatFunc 𝔽) : PowerSeries (RatFunc 𝔽)) =
      PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (1 - zq ℚ) := by
    rw [map_sub, map_one, map_zq]
  have e3 : th3 (RatFunc 𝔽) = PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (th3 ℚ) :=
    (map_th3 _).symm
  refine coeffIn_inv ?_ ?_
  · unfold PhiTilde
    rw [e1, e2, e3]
    exact ((coeffIn_fpow (coeffIn_map_rat a _) a1).mul
      (coeffIn_fpow (coeffIn_map_rat a _) a2)).mul (coeffIn_fpow (coeffIn_map_rat a _) a3)
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PhiTilde_coeff_zero c Δe

/-- If `ℬ_M`, `M ≤ N`, have expansions of order at least `-B` at `Δ = a`, so has `H_N`. -/
theorem ordGE_expandAt_Hsph (c a : 𝔽) (Δe : Fin 4 → 𝔽) (N B : ℕ)
    (hB : ∀ M ≤ N, OrdGE (expandAt (Bsph c Δe M) a) (-(B : ℤ))) :
    OrdGE (expandAt (Hsph c Δe N) a) (-(B : ℤ)) := by
  have hz : CoeffIn (regRing a) (zq (RatFunc 𝔽)) := by
    rw [← map_zq (algebraMap ℚ (RatFunc 𝔽))]
    exact coeffIn_map_rat a _
  have h16 : ((16 : RatFunc 𝔽) ^ N)⁻¹ ∈ regRing a := by
    have h : ((16 : RatFunc 𝔽) ^ N)⁻¹ = RatFunc.C (((16 : 𝔽) ^ N)⁻¹) := by
      rw [map_inv₀, map_pow, map_ofNat]
    rw [h]
    exact C_mem_regRing a _
  have hBz : ∀ j ≤ N, OrdGE (expandHom a (PowerSeries.coeff j (BzSeries c Δe))) (-(B : ℤ)) := by
    intro j hj
    simp only [BzSeries, PowerSeries.coeff_mk]
    rw [map_sum]
    refine OrdGE.sum fun m hm => ?_
    rw [map_mul]
    have hm' : m ≤ N := by
      have := Finset.mem_range.1 hm
      omega
    have h := (hB m hm').mul (hz.pow m j)
    rwa [add_zero] at h
  unfold Hsph Hseries
  rw [expandAt_eq, div_eq_mul_inv, map_mul, PowerSeries.coeff_mul, map_sum]
  have hsum : OrdGE (∑ p ∈ Finset.HasAntidiagonal.antidiagonal N,
      expandHom a (PowerSeries.coeff p.1 (PhiTilde c Δe)⁻¹ *
        PowerSeries.coeff p.2 (BzSeries c Δe))) (-(B : ℤ)) := by
    refine OrdGE.sum fun p hp => ?_
    rw [map_mul]
    have hp2 : p.2 ≤ N := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      omega
    have h := (coeffIn_PhiTilde_inv c a Δe p.1).mul (hBz p.2 hp2)
    rwa [zero_add] at h
  have h := hsum.mul h16
  rwa [add_zero] at h

/-- Theorem 5.1 of the sphere paper, from the torus Theorem 5.8.

Paper label: thm:jantzen-bound -/
theorem thm_jantzen_bound_of_cited (hJ : Cited_JantzenLayers) : Stmt_thm_jantzen_bound := by
  intro p p' r s b hset N
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  obtain ⟨wp, wm, -, -, -, hpole⟩ := thm_jantzen_smith hJ p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hBM : ∀ M ≤ N, OrdGE (expandAt (Bsph (cK (kacC b)) ΔK M) (cK (kacH r s b)))
      (-(jDepth p p' r s N : ℤ)) := by
    intro M hM
    refine (ordGE_expandAt_BsphK (kacC b) (kacH r s b) M).mono ?_
    rw [(hpole M).1]
    have := jDepth_mono p p' r s hM
    omega
  exact ⟨poleOrder_le_of_ordGE (hBM N le_rfl),
    poleOrder_le_of_ordGE (ordGE_expandAt_Hsph _ _ _ N _ hBM)⟩

example (hJ : Cited_JantzenLayers) : Stmt_thm_jantzen_bound := thm_jantzen_bound_of_cited hJ

end Virasoro.Sphere
