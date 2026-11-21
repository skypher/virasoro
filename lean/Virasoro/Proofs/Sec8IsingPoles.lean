import Virasoro.Proofs.Sec8NoDouble
import Virasoro.Proofs.Sec8Smith7
import Virasoro.Proofs.IsingAux
import Virasoro.Proofs.Sec4PF
import Virasoro.Proofs.Sec5Jantzen
import Virasoro.Statements.Sec8b
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Proposition 8.1 of `paper.tex` at 70bac53: the simple-pole clauses

* For `N < 7` every pole of `H_N(1/2,Δ,d)` over `ℂ(d)` is simple (paper.tex l.1737): at a
  complex point this is the Smith-exponent bound of the old Proposition 8.2
  (`prop_no_earlier_double_pole`); a point of `ℂ(d)` that is not complex is not a root of a
  Shapovalov determinant, so `H_N` is regular there.
* At the three interior weights, `j_N(λ) ≤ 1` below `N = min(ℓ⁺₂, ℓ⁻₂) = 7, 10, 11`
  (l.1767–1768, Theorem 5.8).
The remaining clauses of each row of the table (order exactly `2`, the coefficient of
`(Δ-λ)^{-2}`, the singular vector with its `τ` and `γ`) are collected in `IsingDoublePoleTop`.
-/

namespace Virasoro

open Polynomial

/-- An element of `ℂ(d)` that is a root of a nonzero complex polynomial is a complex number. -/
theorem const_of_root {a : Kd} {P : ℂ[X]} (hP : P ≠ 0)
    (h : (P.map (RatFunc.C : ℂ →+* Kd)).eval a = 0) : a ∈ Set.range (RatFunc.C : ℂ →+* Kd) := by
  have halg : IsAlgebraic ℂ a := by
    refine ⟨P, hP, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, RatFunc.algebraMap_eq_C]
    exact h
  have hint : IsIntegral ℂ a := halg.isIntegral
  have h1 := IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hint)
  obtain ⟨z, hz⟩ := minpoly.mem_range_of_degree_eq_one ℂ a h1
  exact ⟨z, by rw [← hz, RatFunc.algebraMap_eq_C]⟩

/-- `H_N(c,Δ,d)` over `ℂ(d)` is regular at every point that is not a complex number. -/
theorem poleOrder_HN_of_not_const (c : ℂ) (N : ℕ) {a : Kd}
    (ha : a ∉ Set.range (RatFunc.C : ℂ →+* Kd)) : poleOrder (HN c N) a = 0 := by
  have hdet : ∀ M ≤ N, (gram (RatFunc.C c : Kd) a M).det ≠ 0 := by
    intro M _ h0
    have hmap : gramPoly (RatFunc.C c : Kd) M =
        (gramPoly c M).map (mapRingHom (RatFunc.C : ℂ →+* Kd)) := by
      have := gram_map (mapRingHom (RatFunc.C : ℂ →+* Kd)) (C c) (X : ℂ[X]) M
      simp only [coe_mapRingHom, map_C, map_X] at this
      exact this
    have hd : ((gramPoly c M).map (mapRingHom (RatFunc.C : ℂ →+* Kd))).det =
        mapRingHom (RatFunc.C : ℂ →+* Kd) (gramPoly c M).det :=
      (RingHom.map_det (mapRingHom (RatFunc.C : ℂ →+* Kd)) (gramPoly c M)).symm
    rw [← gramPoly_det_eval, hmap, hd, coe_mapRingHom] at h0
    exact ha (const_of_root (gramPoly_det_ne_zero c M) h0)
  exact poleOrder_eq_zero_of _ _ fun k hk => ppCoeff_eq_zero_of_regAt (regAt_Hrat hdet) hk

/-- The clauses of `IsingDoublePole` at the level `N` itself. -/
def IsingDoublePoleTop (lam : ℂ) (N R₁ S₁ R₂ S₂ : ℕ) (γ : ℂ) : Prop :=
  poleOrder (HN (1 / 2) N) (pt lam) = 2 ∧
  ppCoeff (HN (1 / 2) N) (pt lam) 2 =
    genP R₁ S₁ (RatFunc.C b0 : Kd) dvar * genP R₂ S₂ (RatFunc.C b0 : Kd) dvar / RatFunc.C γ ∧
  ∃ x : Nat.Partition N → ℂ, x (onesPartition N) = 1 ∧
    Verma.IsSingular (Verma.pbwCoord (c := (1 / 2 : ℂ)) (h := lam) N x) N ∧
    (∀ d : ℂ, torusForm (1 / 2 : ℂ) lam d N x x = genP R₁ S₁ b0 d * genP R₂ S₂ b0 d) ∧
    jform (1 / 2 : ℂ) lam N 2 x x = γ

/-- Frozen sub-statement of Proposition 8.1 (paper.tex l.1738–1754, proof l.1768–1773): the three
rows of the table at the levels `7, 10, 11` themselves.
Demand sheet: the clauses of `Stmt_prop_ising_double_poles` other than the simple-pole clauses,
word for word. -/
def Stmt_sub_ising_rows : Prop :=
  IsingDoublePoleTop (1 / 2) 7 2 1 1 5 (-700700) ∧
  IsingDoublePoleTop (1 / 16) 10 1 2 4 2 (-1121229484375 / 192) ∧
  IsingDoublePoleTop 0 11 1 1 2 5 (-2477917160468750 / 6561)

theorem IsingDoublePole.of_top {lam : ℂ} {N R₁ S₁ R₂ S₂ : ℕ} {γ : ℂ}
    (h1 : ∀ M : ℕ, M < N → poleOrder (HN (1 / 2) M) (pt lam) ≤ 1)
    (h2 : IsingDoublePoleTop lam N R₁ S₁ R₂ S₂ γ) : IsingDoublePole lam N R₁ S₁ R₂ S₂ γ :=
  ⟨h1, h2⟩

theorem jDepth_21_lt7 : ∀ N : ℕ, N < 7 → jDepth 3 4 2 1 N ≤ 1 := by decide +kernel
theorem jDepth_12_lt10 : ∀ N : ℕ, N < 10 → jDepth 3 4 1 2 N ≤ 1 := by decide +kernel
theorem jDepth_11_lt11 : ∀ N : ℕ, N < 11 → jDepth 3 4 1 1 N ≤ 1 := by decide +kernel

/-- `j_M(λ) ≤ 1` gives at most a simple pole of `H_M(1/2,Δ,d)` at an interior Ising weight
(Theorem 5.8 with the cited Jantzen layers). -/
theorem ising_simple_below (hJ : Cited_JantzenLayers) {r s : ℕ} (hr : 0 < r) (hrp : r < 3)
    (hs : 0 < s) (hsp : s < 4) (hlt : 4 * r + 3 * s < 3 * 4) {lam : ℂ}
    (hlam : kacH r s b0 = lam) {M : ℕ} (hM : jDepth 3 4 r s M ≤ 1) :
    poleOrder (HN (1 / 2) M) (pt lam) ≤ 1 := by
  have hb : b0 ^ 2 = -((4 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) := by
    rw [b0_sq]
    norm_num
  obtain ⟨wp, wm, -, -, -, hpole⟩ :=
    thm_jantzen_smith hJ 3 4 r s (by norm_num) (by norm_num) (by decide) hr hrp hs hsp hlt b0 hb
  have h := (hpole M).2.2
  rw [kacC_b0', hlam] at h
  exact h.trans hM

/-- Proposition 8.1 from its rows at the levels `7, 10, 11`, the cited Kac determinant and the
cited Jantzen layers. -/
theorem prop_ising_double_poles_of_rows (hK : Cited_KacDeterminant) (hJ : Cited_JantzenLayers)
    (h : Stmt_sub_ising_rows) : Stmt_prop_ising_double_poles := by
  obtain ⟨h7, h10, h11⟩ := h
  have e21 : kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = (1 / 2 : ℂ) := by
    have := kacHL_b0_cast (2, 1)
    rw [kacHL] at this
    rw [this]
    norm_num [isingDelta]
  have e12 : kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0 = (1 / 16 : ℂ) := by
    have := kacHL_b0_cast (1, 2)
    rw [kacHL] at this
    rw [this]
    norm_num [isingDelta]
  have e11 : kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = (0 : ℂ) := by
    have := kacHL_b0_cast (1, 1)
    rw [kacHL] at this
    rw [this]
    norm_num [isingDelta]
  refine ⟨fun N hN a => ?_, IsingDoublePole.of_top (fun M hM => ?_) h7,
    IsingDoublePole.of_top (fun M hM => ?_) h10, IsingDoublePole.of_top (fun M hM => ?_) h11⟩
  · by_cases ha : a ∈ Set.range (RatFunc.C : ℂ →+* Kd)
    · obtain ⟨z, rfl⟩ := ha
      exact (prop_no_earlier_double_pole hK hJ N hN z).2.2.2
    · rw [poleOrder_HN_of_not_const _ _ ha]
      exact Nat.zero_le 1
  · exact ising_simple_below hJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) e21 (jDepth_21_lt7 M hM)
  · exact ising_simple_below hJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) e12 (jDepth_12_lt10 M hM)
  · exact ising_simple_below hJ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) e11 (jDepth_11_lt11 M hM)

end Virasoro
