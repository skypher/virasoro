import Virasoro.Proofs.P2Sec11VertexZero
import Virasoro.Proofs.TopLayerForm
import Virasoro.Proofs.DefMatrices
import Virasoro.Proofs.Naturality
import Virasoro.Proofs.PairingConstr

/-!
# Proposition 11.2(i): the case `i = 0` and the induction step (paper.tex l.2412–2459)

"For `i = 0`, `ρ⁽⁰⁾ = ρ_{c⋆,μ,d}`" (l.2412): the coefficient of `x⁰` of `ρ_x(a(x),b(x))` is
`ρ_{c⋆,μ,d}(a(0),b(0))`, so the four clauses of part (i) at `i = 0` are the Ward identity of
`ρ_{c⋆,μ,d}` and `J¹(c⋆,μ) ⊂ rad ρ⁽⁰⁾` (`sub_vertex_radical_zero`).  The induction step
(l.2423–2459) is the sub-statement `Stmt_sub_vertex_step`.
-/

namespace Virasoro

open Polynomial Verma

section Ring

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

/-- A primary pairing on vectors of two levels, in coordinates. -/
theorem primary_two_level {d : R} {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R}
    (hT : IsPrimaryPairing d T) (N₁ N₂ : ℕ) (u : Nat.Partition N₁ → R)
    (v : Nat.Partition N₂ → R) :
    T (pbwCoord N₁ u) (pbwCoord N₂ v) =
      ∑ Y, ∑ Y', u Y * v Y' * torusWord c h d Y.word Y'.word := by
  rw [pbwCoord_apply, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, LinearMap.smul_apply, pbwCoord_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [map_smul, smul_eq_mul, primary_torusWord hT _ (posWord_word Y) _ (posWord_word Y')]
  ring

end Ring

/-- The four clauses of Proposition 11.2(i) for one order `i`, one pairing `ρ_x = T` and one pair
of families (the body of the first conjunct of `Stmt_prop_jantzen_vertex`). -/
def VertexClausesAt (c μ d : ℂ) (i : ℕ)
    (T : Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] ℂ[X])
    (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
    (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]) : Prop :=
  (X : ℂ[X]) ^ i ∣ T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂ wb) ∧
  (∀ (wa' : Nat.Partition N₁ → ℂ[X]) (wb' : Nat.Partition N₂ → ℂ[X]),
    IsJFamily c μ N₁ i a wa' → IsJFamily c μ N₂ i a₂ wb' →
      (T (Verma.pbwCoord N₁ wa') (Verma.pbwCoord N₂ wb')).coeff i =
        (T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂ wb)).coeff i) ∧
  (∀ (n : ℤ) (N₁' N₂' : ℕ) (a' : Nat.Partition N₁' → ℂ) (b' : Nat.Partition N₂' → ℂ)
      (wa' : Nat.Partition N₁' → ℂ[X]) (wb' : Nat.Partition N₂' → ℂ[X]),
    IsJFamily c μ N₁' i a' wa' → IsJFamily c μ N₂' i b' wb' →
    Verma.pbwCoord (c := c) (h := μ) N₁' a' =
      Verma.L (-n) (Verma.pbwCoord (c := c) (h := μ) N₁ a) →
    Verma.pbwCoord (c := c) (h := μ) N₂' b' =
      Verma.L n (Verma.pbwCoord (c := c) (h := μ) N₂ a₂) →
      (T (Verma.pbwCoord N₁' wa') (Verma.pbwCoord N₂ wb)).coeff i -
          (T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂' wb')).coeff i =
        (((N₁ : ℂ) - (N₂ : ℂ)) + (n : ℂ) * d) *
          (T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂ wb)).coeff i) ∧
  (((∃ w, IsJFamily c μ N₁ (i + 1) a w) ∨ (∃ w, IsJFamily c μ N₂ (i + 1) a₂ w)) →
    (T (Verma.pbwCoord N₁ wa) (Verma.pbwCoord N₂ wb)).coeff i = 0)

/-- `ρ⁽⁰⁾ = ρ_{c⋆,μ,d}` (paper.tex l.2412): the coefficient of `x⁰` of `ρ_x(a(x),b(x))` is
`ρ_{c,μ,d}(a(0),b(0))`. -/
theorem primary_coeff_zero {c μ d : ℂ}
    {T : Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] ℂ[X]}
    (hT : IsPrimaryPairing (C d) T) {T₀ : Verma ℂ c μ →ₗ[ℂ] Verma ℂ c μ →ₗ[ℂ] ℂ}
    (hT₀ : IsPrimaryPairing d T₀) {N₁ N₂ : ℕ} {a : Nat.Partition N₁ → ℂ}
    {a₂ : Nat.Partition N₂ → ℂ} {wa : Nat.Partition N₁ → ℂ[X]} {wb : Nat.Partition N₂ → ℂ[X]}
    (ha : ∀ Y, (wa Y).eval 0 = a Y) (hb : ∀ Y, (wb Y).eval 0 = a₂ Y) :
    (T (pbwCoord N₁ wa) (pbwCoord N₂ wb)).coeff 0 = T₀ (pbwCoord N₁ a) (pbwCoord N₂ a₂) := by
  rw [primary_two_level hT, primary_two_level hT₀, coeff_zero_eq_eval_zero, eval_finsetSum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  rw [eval_mul, eval_mul, ha, hb]
  congr 1
  have := torusWord_map (Polynomial.evalRingHom (0 : ℂ)) (C c) (C μ + X) (C d) Y.word Y'.word
  simp only [coe_evalRingHom, eval_C, eval_add, eval_X, add_zero] at this
  exact this.symm

/-- Proposition 11.2(i) at `i = 0` (paper.tex l.2412–2421), given `J¹ ⊂ rad ρ_{c,μ,d}`. -/
theorem vertex_base {c μ d : ℂ}
    (hrad : ∀ T₀ : Verma ℂ c μ →ₗ[ℂ] Verma ℂ c μ →ₗ[ℂ] ℂ, IsPrimaryPairing d T₀ →
      ∀ u ∈ jantzen c μ 1, ∀ v, T₀ u v = 0 ∧ T₀ v u = 0)
    (T : Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] ℂ[X])
    (hT : IsPrimaryPairing (C d) T) (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ)
    (a₂ : Nat.Partition N₂ → ℂ) (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X])
    (ha : IsJFamily c μ N₁ 0 a wa) (hb : IsJFamily c μ N₂ 0 a₂ wb) :
    VertexClausesAt c μ d 0 T N₁ N₂ a a₂ wa wb := by
  have hT₀ := isPrimaryPairing_pairing (c := c) (h := μ) d
  refine ⟨by rw [pow_zero]; exact one_dvd _, fun wa' wb' ha' hb' => ?_,
    fun n N₁' N₂' a' b' wa' wb' ha' hb' e1 e2 => ?_, fun hex => ?_⟩
  · rw [primary_coeff_zero hT hT₀ ha'.1 hb'.1, primary_coeff_zero hT hT₀ ha.1 hb.1]
  · rw [primary_coeff_zero hT hT₀ ha'.1 hb.1, primary_coeff_zero hT hT₀ ha.1 hb'.1,
      primary_coeff_zero hT hT₀ ha.1 hb.1, e1, e2, sub_eq_iff_eq_add.2 ?_]
    have hw := hT₀.2 n (pbwCoord N₁ a) (pbwCoord N₂ a₂)
    rw [L_zero_of_mem_level ⟨a, rfl⟩, L_zero_of_mem_level ⟨a₂, rfl⟩, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at hw
    linear_combination hw
  · rw [primary_coeff_zero hT hT₀ ha.1 hb.1]
    rcases hex with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact (hrad _ hT₀ _ (pbwCoord_mem_jantzen ⟨w, hw.1, hw.2⟩) _).1
    · exact (hrad _ hT₀ _ (pbwCoord_mem_jantzen ⟨w, hw.1, hw.2⟩) _).2

/-- The induction step of Proposition 11.2(i), paper.tex l.2423–2459: if the four clauses of
part (i) hold at order `i` for all families, they hold at order `i + 1`.

Demand sheet: the hypotheses of `Stmt_prop_jantzen_vertex` (`MinimalSetting`, node `μ^ε_{k₀}`,
`(k,m)` in the fusion box, `ρ_x` any primary pairing over `ℂ[x]`); every `i ≥ 0`; the hypothesis
and the conclusion quantify over all levels `N₁, N₂` and all pairs of families of the order
concerned, as part (i) does. -/
def Stmt_sub_vertex_step : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k₀ k m : ℕ),
    k < min r (p - r) → m < min s (p' - s) →
      ∀ T : Verma ℂ[X] (C (kacC b)) (C (muOrb p p' r s ε k₀) + X) →ₗ[ℂ[X]]
          Verma ℂ[X] (C (kacC b)) (C (muOrb p p' r s ε k₀) + X) →ₗ[ℂ[X]] ℂ[X],
        Verma.IsPrimaryPairing (C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)) T → ∀ i : ℕ,
          (∀ (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
              (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]),
            IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₁ i a wa →
            IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₂ i a₂ wb →
              VertexClausesAt (kacC b) (muOrb p p' r s ε k₀)
                (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) i T N₁ N₂ a a₂ wa wb) →
          ∀ (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
              (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]),
            IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₁ (i + 1) a wa →
            IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₂ (i + 1) a₂ wb →
              VertexClausesAt (kacC b) (muOrb p p' r s ε k₀)
                (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (i + 1) T N₁ N₂ a a₂ wa wb

/-- Proposition 11.2(i) from its induction step: the case `i = 0` is `vertex_base` with
`sub_vertex_radical_zero`. -/
theorem vertex_part_i_of_step (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hstep : Stmt_sub_vertex_step)
    (p p' r s : ℕ) (b : ℂ) (hset : MinimalSetting p p' r s b) (ε : Bool) (k₀ k m : ℕ)
    (hk : k < min r (p - r)) (hm : m < min s (p' - s))
    (T : Verma ℂ[X] (C (kacC b)) (C (muOrb p p' r s ε k₀) + X) →ₗ[ℂ[X]]
      Verma ℂ[X] (C (kacC b)) (C (muOrb p p' r s ε k₀) + X) →ₗ[ℂ[X]] ℂ[X])
    (hT : Verma.IsPrimaryPairing (C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)) T) (i : ℕ) :
    ∀ (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
      (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]),
      IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₁ i a wa →
      IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₂ i a₂ wb →
        VertexClausesAt (kacC b) (muOrb p p' r s ε k₀)
          (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) i T N₁ N₂ a a₂ wa wb := by
  induction i with
  | zero =>
    intro N₁ N₂ a a₂ wa wb ha hb
    exact vertex_base (fun T₀ hT₀ =>
      sub_vertex_radical_zero hJ hH hU hF p p' r s b hset ε k₀ k m hk hm T₀ hT₀) T hT N₁ N₂ a a₂
      wa wb ha hb
  | succ i ih => exact hstep p p' r s b hset ε k₀ k m hk hm T hT i ih

set_option maxHeartbeats 800000 in
/-- `VertexClausesAt` is the body of part (i) of the frozen `Stmt_prop_jantzen_vertex`. -/
example (h : Stmt_prop_jantzen_vertex) (p p' r s : ℕ) (b : ℂ) (hset : MinimalSetting p p' r s b)
    (ε : Bool) (k₀ k m : ℕ) (hk : k < min r (p - r)) (hm : m < min s (p' - s))
    (T : Verma ℂ[X] (C (kacC b)) (C (muOrb p p' r s ε k₀) + X) →ₗ[ℂ[X]]
      Verma ℂ[X] (C (kacC b)) (C (muOrb p p' r s ε k₀) + X) →ₗ[ℂ[X]] ℂ[X])
    (hT : Verma.IsPrimaryPairing (C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)) T)
    (i N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
    (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X])
    (ha : IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₁ i a wa)
    (hb : IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₂ i a₂ wb) :
    VertexClausesAt (kacC b) (muOrb p p' r s ε k₀)
      (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) i T N₁ N₂ a a₂ wa wb := by
  unfold VertexClausesAt
  have h1 := (h p p' r s b hset ε k₀ k m hk hm).1
  exact h1 T hT i N₁ N₂ a a₂ wa wb ha hb

end Virasoro
