import Virasoro.Sphere.Statements.Sec4
import Virasoro.Proofs.LaurentLemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Lemma 4.6 of `sphere/paper.tex` (precision budget)

The proof of the torus Lemma 7.4 for the germs `S_{a,M}`, `W_{a,M}` built from arbitrary residue
germs `R_g`: `ord_t S_{a,M} ≥ -W_{a,M}` by induction on `M`, and a product of two Laurent
series through a given order depends only on the factors through the complementary orders.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

variable {K : Type*} [Field K] (bs : K) (Rg : Label → K⸨X⸩)

theorem SGg_zero (a : Label) : SGg bs Rg 0 a = 1 := by rw [SGg]

theorem SGg_succ (M : ℕ) (a : Label) :
    SGg bs Rg (M + 1) a =
      ∑ g ∈ (labels (M + 1)).attach,
        Rg g.1 / (zG bs a - hG bs g.1) * SGg bs Rg (M + 1 - g.1.lvl) g.1 := by
  rw [SGg]

theorem WGg_zero (a : Label) : WGg bs Rg 0 a = 0 := by rw [WGg]

theorem WGg_succ (M : ℕ) (a : Label) :
    WGg bs Rg (M + 1) a =
      (labels (M + 1)).attach.sup fun g =>
        piGg Rg g.1 + sigmaG bs a g.1 + WGg bs Rg (M + 1 - g.1.lvl) g.1 := by
  rw [WGg]

/-- `ord_t R_g ≥ -π_g`. -/
theorem ordGE_Rg (g : Label) : OrdGE (Rg g) (-(piGg Rg g : ℤ)) := by
  refine (ordGE_order _).mono ?_
  unfold piGg
  have := Int.self_le_toNat (-(Rg g).order)
  linarith

/-- `ord_t (R_g / (z_a - h_g)) ≥ -(π_g + σ_{a,g})`. -/
theorem ordGE_Rg_div (a g : Label) :
    OrdGE (Rg g / (zG bs a - hG bs g)) (-((piGg Rg g + sigmaG bs a g : ℕ) : ℤ)) := by
  refine ((ordGE_Rg Rg g).div (zG bs a - hG bs g)).mono ?_
  unfold sigmaG
  have := Int.self_le_toNat ((zG bs a - hG bs g).order)
  push_cast
  linarith

/-- The valuation bound over an arbitrary coefficient field: `ord_t S_{a,M} ≥ -W_{a,M}`. -/
theorem ordGE_SGg : ∀ (M : ℕ) (a : Label), OrdGE (SGg bs Rg M a) (-(WGg bs Rg M a : ℤ)) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro a
    cases M with
    | zero =>
      rw [SGg_zero, WGg_zero]
      simpa using ordGE_one (K := K)
    | succ M =>
      rw [SGg_succ, WGg_succ]
      refine OrdGE.sum fun g _ => ?_
      have hlt : M + 1 - g.1.lvl < M + 1 := by
        have := lvl_pos_of_mem_labels g.2
        omega
      have hS := ih (M + 1 - g.1.lvl) hlt g.1
      refine ((ordGE_Rg_div bs Rg a g.1).mul hS).mono ?_
      have hsup : piGg Rg g.1 + sigmaG bs a g.1 + WGg bs Rg (M + 1 - g.1.lvl) g.1 ≤
          (labels (M + 1)).attach.sup fun g =>
            piGg Rg g.1 + sigmaG bs a g.1 + WGg bs Rg (M + 1 - g.1.lvl) g.1 :=
        Finset.le_sup (f := fun g : {x // x ∈ labels (M + 1)} =>
          piGg Rg g.1 + sigmaG bs a g.1 + WGg bs Rg (M + 1 - g.1.lvl) g.1) (Finset.mem_attach _ g)
      have : ((piGg Rg g.1 + sigmaG bs a g.1 + WGg bs Rg (M + 1 - g.1.lvl) g.1 : ℕ) : ℤ) ≤
          (((labels (M + 1)).attach.sup fun g =>
            piGg Rg g.1 + sigmaG bs a g.1 + WGg bs Rg (M + 1 - g.1.lvl) g.1 : ℕ) : ℤ) := by
        exact_mod_cast hsup
      push_cast at this ⊢
      linarith

/-- The precision rule of Lemma 4.6 over an arbitrary coefficient field, first part. -/
theorem precision_step_g (a g : Label) (M : ℕ) (U : ℤ) (A' S' : K⸨X⸩)
    (hS' : OrdGE S' (-((WGg bs Rg (M - g.lvl) g : ℕ) : ℤ)))
    (hAA : ∀ n : ℤ, n ≤ U + (WGg bs Rg (M - g.lvl) g : ℕ) →
      A'.coeff n = (Rg g / (zG bs a - hG bs g)).coeff n)
    (hSS : ∀ n : ℤ, n ≤ U + (piGg Rg g + sigmaG bs a g : ℕ) →
      S'.coeff n = (SGg bs Rg (M - g.lvl) g).coeff n) :
    ∀ n : ℤ, n ≤ U →
      (A' * S').coeff n =
        (Rg g / (zG bs a - hG bs g) * SGg bs Rg (M - g.lvl) g).coeff n := by
  refine coeff_mul_congr (ordGE_Rg_div bs Rg a g) hS' ?_ ?_
  · intro n hn
    exact hAA n (by linarith)
  · intro n hn
    exact hSS n (by linarith)

/-- The precision rule of Lemma 4.6 over an arbitrary coefficient field, second part. -/
theorem precision_moment_g (N : ℕ) (lam : K) (a : Label) (k : ℕ)
    (R' S' D' : K⸨X⸩)
    (hS' : OrdGE S' (-((WGg bs Rg (N - a.lvl) a : ℕ) : ℤ)))
    (hRR : ∀ n : ℤ, n ≤ (WGg bs Rg (N - a.lvl) a : ℕ) → R'.coeff n = (Rg a).coeff n)
    (hSS : ∀ n : ℤ, n ≤ (piGg Rg a : ℕ) → S'.coeff n = (SGg bs Rg (N - a.lvl) a).coeff n)
    (hD' : OrdGE D' 0)
    (hDD : ∀ n : ℤ, n ≤ (vhatg bs Rg N a : ℕ) → D'.coeff n = (deltaG bs lam a ^ (k - 1)).coeff n) :
    (R' * S' * D').coeff 0 = (BGg bs Rg N a * deltaG bs lam a ^ (k - 1)).coeff 0 := by
  have h1 : ∀ n : ℤ, n ≤ 0 → (R' * S').coeff n = (BGg bs Rg N a).coeff n := by
    unfold BGg
    refine coeff_mul_congr (ordGE_Rg Rg a) hS' ?_ ?_
    · intro n hn
      exact hRR n (by linarith)
    · intro n hn
      exact hSS n (by linarith)
  have hB : OrdGE (BGg bs Rg N a) (-((vhatg bs Rg N a : ℕ) : ℤ)) := by
    unfold BGg vhatg
    refine ((ordGE_Rg Rg a).mul (ordGE_SGg bs Rg _ a)).mono ?_
    push_cast
    linarith
  refine coeff_mul_congr (U := 0) hB hD' ?_ ?_ 0 le_rfl
  · intro n hn
    exact h1 n (by linarith)
  · intro n hn
    exact hDD n (by linarith)

/-- Lemma 4.6.

Paper label: lem:precision-budget -/
theorem lem_precision_budget : Stmt_lem_precision_budget := by
  intro b _
  refine ⟨?_, ?_⟩
  · intro a g M U _ A' S' _ hS' hAA hSS
    exact precision_step_g (cK b) (RgSph b) a g M U A' S' hS' hAA hSS
  · intro N lam a k _ _ _ R' S' D' _ hS' hRR hSS hD' hDD
    exact precision_moment_g (cK b) (RgSph b) N (cK lam) a k R' S' D' hS' hRR hSS
      (by simpa [OrdGE] using hD') hDD

example : Stmt_lem_precision_budget := lem_precision_budget

end Virasoro.Sphere
