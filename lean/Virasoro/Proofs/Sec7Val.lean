import Virasoro.Statements.Sec7
import Virasoro.Proofs.LaurentLemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Proofs: Lemma 7.2 (valuation majorant) and Lemma 7.4 (precision budget)
-/

namespace Virasoro

open scoped LaurentSeries

variable {K : Type*} [Field K] (bs d : K)

theorem SG_zero (a : Label) : SG bs d 0 a = 1 := by rw [SG]

theorem SG_succ (M : ℕ) (a : Label) :
    SG bs d (M + 1) a =
      ∑ g ∈ (labels (M + 1)).attach,
        RG bs d g.1 / (zG bs a - hG bs g.1) * SG bs d (M + 1 - g.1.lvl) g.1 := by
  rw [SG]

theorem WG_zero (a : Label) : WG bs d 0 a = 0 := by rw [WG]

theorem WG_succ (M : ℕ) (a : Label) :
    WG bs d (M + 1) a =
      (labels (M + 1)).attach.sup fun g =>
        piG bs d g.1 + sigmaG bs a g.1 + WG bs d (M + 1 - g.1.lvl) g.1 := by
  rw [WG]

/-- `ord_t R_g ≥ -π_g`. -/
theorem ordGE_RG (g : Label) : OrdGE (RG bs d g) (-(piG bs d g : ℤ)) := by
  refine (ordGE_order _).mono ?_
  unfold piG
  have := Int.self_le_toNat (-(RG bs d g).order)
  linarith

/-- `ord_t (R_g / (z_a - h_g)) ≥ -(π_g + σ_{a,g})`. -/
theorem ordGE_RG_div (a g : Label) :
    OrdGE (RG bs d g / (zG bs a - hG bs g)) (-((piG bs d g + sigmaG bs a g : ℕ) : ℤ)) := by
  refine ((ordGE_RG bs d g).div (zG bs a - hG bs g)).mono ?_
  unfold sigmaG
  have := Int.self_le_toNat ((zG bs a - hG bs g).order)
  push_cast
  linarith

/-- Lemma 7.2 over an arbitrary coefficient field: `ord_t S_{a,M} ≥ -W_{a,M}`. -/
theorem ordGE_SG : ∀ (M : ℕ) (a : Label), OrdGE (SG bs d M a) (-(WG bs d M a : ℤ)) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro a
    cases M with
    | zero =>
      rw [SG_zero, WG_zero]
      simpa using ordGE_one (K := K)
    | succ M =>
      rw [SG_succ, WG_succ]
      refine OrdGE.sum fun g _ => ?_
      have hlt : M + 1 - g.1.lvl < M + 1 := by
        have := lvl_pos_of_mem_labels g.2
        omega
      have hS := ih (M + 1 - g.1.lvl) hlt g.1
      refine ((ordGE_RG_div bs d a g.1).mul hS).mono ?_
      have hsup : piG bs d g.1 + sigmaG bs a g.1 + WG bs d (M + 1 - g.1.lvl) g.1 ≤
          (labels (M + 1)).attach.sup fun g =>
            piG bs d g.1 + sigmaG bs a g.1 + WG bs d (M + 1 - g.1.lvl) g.1 :=
        Finset.le_sup (f := fun g : {x // x ∈ labels (M + 1)} =>
          piG bs d g.1 + sigmaG bs a g.1 + WG bs d (M + 1 - g.1.lvl) g.1) (Finset.mem_attach _ g)
      have : ((piG bs d g.1 + sigmaG bs a g.1 + WG bs d (M + 1 - g.1.lvl) g.1 : ℕ) : ℤ) ≤
          (((labels (M + 1)).attach.sup fun g =>
            piG bs d g.1 + sigmaG bs a g.1 + WG bs d (M + 1 - g.1.lvl) g.1 : ℕ) : ℤ) := by
        exact_mod_cast hsup
      push_cast at this ⊢
      linarith

/-- Paper label: lem:shifted-valuation-bound -/
theorem lem_shifted_valuation_bound : Stmt_lem_shifted_valuation_bound := by
  intro b _ a M _ _
  exact ordGE_SG (RatFunc.C b : Kd) dvar M a

example : Stmt_lem_shifted_valuation_bound := lem_shifted_valuation_bound

/-! ### Germs of the Kac weights are power series -/

theorem ordGE_single_one : OrdGE (HahnSeries.single 1 1 : K⸨X⸩) 0 :=
  ordGE_iff.2 fun m hm => HahnSeries.coeff_single_of_ne (by omega)

theorem ordGE_bGerm : OrdGE (bGerm bs) 0 := (ordGE_C bs).add ordGE_single_one

theorem bGerm_coeff_zero : (bGerm bs).coeff 0 = bs := by
  unfold bGerm
  rw [HahnSeries.coeff_add, HahnSeries.coeff_single_of_ne (by norm_num)]
  simp [HahnSeries.C]

theorem bGerm_order {bs : K} (hbs : bs ≠ 0) : (bGerm bs).order = 0 :=
  order_eq_zero_of (ordGE_bGerm bs) (by rw [bGerm_coeff_zero]; exact hbs)

theorem bGerm_ne_zero {bs : K} (hbs : bs ≠ 0) : bGerm bs ≠ 0 := by
  intro h
  have := bGerm_coeff_zero bs
  rw [h] at this
  exact hbs (by simpa using this.symm)

theorem ordGE_bGerm_inv {bs : K} (hbs : bs ≠ 0) : OrdGE (bGerm bs)⁻¹ 0 := by
  have := ordGE_inv (bGerm bs)
  rwa [bGerm_order hbs, neg_zero] at this

theorem ordGE_intCast (n : ℤ) : OrdGE ((n : K⸨X⸩)) 0 := by
  have : ((n : K⸨X⸩)) = HahnSeries.C (n : K) := (map_intCast (HahnSeries.C : K →+* K⸨X⸩) n).symm
  rw [this]
  exact ordGE_C _

theorem ordGE_natCast (n : ℕ) : OrdGE ((n : K⸨X⸩)) 0 := by
  have : ((n : K⸨X⸩)) = HahnSeries.C (n : K) := (map_natCast (HahnSeries.C : K →+* K⸨X⸩) n).symm
  rw [this]
  exact ordGE_C _

theorem OrdGE.div_four {x : K⸨X⸩} {a : ℤ} (hx : OrdGE x a) : OrdGE (x / 4) a := by
  have h4 : (4 : K⸨X⸩) = HahnSeries.C (4 : K) := (map_ofNat (HahnSeries.C : K →+* K⸨X⸩) 4).symm
  have : x / 4 = x * HahnSeries.C ((4 : K)⁻¹) := by
    rw [h4, div_eq_mul_inv, map_inv₀]
  rw [this]
  simpa using hx.mul (ordGE_C ((4 : K)⁻¹))

theorem ordGE_kacH {bs : K} (hbs : bs ≠ 0) (r s : ℤ) : OrdGE (kacH r s (bGerm bs)) 0 := by
  unfold kacH
  have hb := ordGE_bGerm bs
  have hbi := ordGE_bGerm_inv hbs
  have h1 : OrdGE ((bGerm bs + (bGerm bs)⁻¹) ^ 2) 0 := by
    simpa using (hb.add hbi).pow 2
  have h2 : OrdGE (((r : K⸨X⸩) * bGerm bs + (s : K⸨X⸩) * (bGerm bs)⁻¹) ^ 2) 0 := by
    have e1 : OrdGE ((r : K⸨X⸩) * bGerm bs) 0 := by simpa using (ordGE_intCast r).mul hb
    have e2 : OrdGE ((s : K⸨X⸩) * (bGerm bs)⁻¹) 0 := by simpa using (ordGE_intCast s).mul hbi
    simpa using (e1.add e2).pow 2
  exact (h1.sub h2).div_four

theorem ordGE_hG {bs : K} (hbs : bs ≠ 0) (a : Label) : OrdGE (hG bs a) 0 :=
  ordGE_kacH hbs _ _

theorem ordGE_deltaG {bs : K} (hbs : bs ≠ 0) (lam : K) (a : Label) :
    OrdGE (deltaG bs lam a) 0 :=
  (ordGE_hG hbs a).sub (ordGE_C lam)

/-- The precision rule of Lemma 7.4 over an arbitrary coefficient field, first part. -/
theorem precision_step (a g : Label) (M : ℕ) (U : ℤ) (A' S' : K⸨X⸩)
    (hS' : OrdGE S' (-((WG bs d (M - g.lvl) g : ℕ) : ℤ)))
    (hAA : ∀ n : ℤ, n ≤ U + (WG bs d (M - g.lvl) g : ℕ) →
      A'.coeff n = (RG bs d g / (zG bs a - hG bs g)).coeff n)
    (hSS : ∀ n : ℤ, n ≤ U + (piG bs d g + sigmaG bs a g : ℕ) →
      S'.coeff n = (SG bs d (M - g.lvl) g).coeff n) :
    ∀ n : ℤ, n ≤ U →
      (A' * S').coeff n =
        (RG bs d g / (zG bs a - hG bs g) * SG bs d (M - g.lvl) g).coeff n := by
  refine coeff_mul_congr (ordGE_RG_div bs d a g) hS' ?_ ?_
  · intro n hn
    exact hAA n (by linarith)
  · intro n hn
    exact hSS n (by linarith)

/-- The precision rule of Lemma 7.4 over an arbitrary coefficient field, second part. -/
theorem precision_moment {bs : K} (hbs : bs ≠ 0) (d : K) (N : ℕ) (lam : K) (a : Label) (k : ℕ)
    (R' S' D' : K⸨X⸩)
    (hS' : OrdGE S' (-((WG bs d (N - a.lvl) a : ℕ) : ℤ)))
    (hRR : ∀ n : ℤ, n ≤ (WG bs d (N - a.lvl) a : ℕ) → R'.coeff n = (RG bs d a).coeff n)
    (hSS : ∀ n : ℤ, n ≤ (piG bs d a : ℕ) → S'.coeff n = (SG bs d (N - a.lvl) a).coeff n)
    (hD' : OrdGE D' 0)
    (hDD : ∀ n : ℤ, n ≤ (vhat bs d N a : ℕ) → D'.coeff n = (deltaG bs lam a ^ (k - 1)).coeff n) :
    (R' * S' * D').coeff 0 = (BG bs d N a * deltaG bs lam a ^ (k - 1)).coeff 0 := by
  have h1 : ∀ n : ℤ, n ≤ 0 → (R' * S').coeff n = (BG bs d N a).coeff n := by
    unfold BG
    refine coeff_mul_congr (ordGE_RG bs d a) hS' ?_ ?_
    · intro n hn
      exact hRR n (by linarith)
    · intro n hn
      exact hSS n (by linarith)
  have hB : OrdGE (BG bs d N a) (-((vhat bs d N a : ℕ) : ℤ)) := by
    unfold BG vhat
    refine ((ordGE_RG bs d a).mul (ordGE_SG bs d _ a)).mono ?_
    push_cast
    linarith
  refine coeff_mul_congr (U := 0) hB hD' ?_ ?_ 0 le_rfl
  · intro n hn
    exact h1 n (by linarith)
  · intro n hn
    exact hDD n (by linarith)

/-- Paper label: lem:precision-budget -/
theorem lem_precision_budget : Stmt_lem_precision_budget := by
  intro b hb
  have hbs : (RatFunc.C b : Kd) ≠ 0 := by
    simpa using hb
  refine ⟨?_, ?_⟩
  · intro a g M U _ A' S' _ hS' hAA hSS
    exact precision_step (RatFunc.C b : Kd) dvar a g M U A' S' hS' hAA hSS
  · intro N lam a k _ _ _ R' S' D' _ hS' hRR hSS hD' hDD
    exact precision_moment hbs dvar N (pt lam) a k R' S' D' hS' hRR hSS
      (by simpa [OrdGE] using hD') hDD

example : Stmt_lem_precision_budget := lem_precision_budget

end Virasoro
