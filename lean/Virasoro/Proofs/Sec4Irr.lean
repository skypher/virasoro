import Virasoro.Proofs.Sec4Thm

/-!
# Theorem 4.3, irrational case: single-label classes and the generic recursion at `b⋆`
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

section General

variable {K : Type} [Field K] [CharZero K]

theorem toNat_neg_order_eq_zero {x : K⸨X⸩} (hx : OrdGE x 0) : (-x.order).toNat = 0 := by
  by_cases h0 : x = 0
  · rw [h0]; simp
  · unfold OrdGE at hx
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0] at hx
    have : (0 : ℤ) ≤ x.order := by exact_mod_cast hx
    omega

theorem labels_pos {N : ℕ} {a : Label} (ha : a ∈ labels N) : 0 < a.1 ∧ 0 < a.2 := by
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ha
  exact ⟨ha.1.1.1, ha.1.2.1⟩

variable {bs : K} (hbs : bs ≠ 0) (hirr : SqIrrational bs) (d : K)
include hbs hirr

theorem piG_eq_zero (a : Label) : piG bs d a = 0 :=
  toNat_neg_order_eq_zero (regVal_RG hbs hirr d a).1

theorem shift_value_ne {a g : Label} (ha : 0 < a.1 ∧ 0 < a.2) (hg : 0 < g.1 ∧ 0 < g.2) :
    kacHL a bs + (a.lvl : K) - kacHL g bs ≠ 0 := by
  have := kacH_shift_ne hbs hirr (a.1 : ℤ) (a.2 : ℤ) (g.1 : ℤ) (g.2 : ℤ)
    (by exact_mod_cast ha.1) (by exact_mod_cast ha.2) (by exact_mod_cast hg.1)
    (by exact_mod_cast hg.2)
  simpa [kacHL, Label.lvl] using this

theorem regVal_shift {a g : Label} :
    RegVal (zG bs a - hG bs g) (kacHL a bs + (a.lvl : K) - kacHL g bs) :=
  (regVal_zG hbs a).sub (regVal_hG hbs g)

theorem sigmaG_eq_zero {a g : Label} (ha : 0 < a.1 ∧ 0 < a.2) (hg : 0 < g.1 ∧ 0 < g.2) :
    sigmaG bs a g = 0 := by
  have h := regVal_shift hbs hirr (a := a) (g := g)
  have hord := order_eq_zero_of h.1 (by rw [h.2]; exact shift_value_ne hbs hirr ha hg)
  unfold sigmaG
  rw [hord]
  rfl

theorem WG_eq_zero : ∀ (M : ℕ) (a : Label), 0 < a.1 ∧ 0 < a.2 → WG bs d M a = 0 := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro a ha
    cases M with
    | zero => exact WG_zero bs d a
    | succ M =>
      rw [WG_succ]
      apply Nat.eq_zero_of_le_zero
      refine Finset.sup_le fun g _ => ?_
      have hg := labels_pos g.2
      have hl := lvl_pos_of_mem_labels g.2
      rw [piG_eq_zero hbs hirr d, sigmaG_eq_zero hbs hirr ha hg,
        ih (M + 1 - g.1.lvl) (by omega) g.1 hg]

theorem vhat_eq_zero (N : ℕ) {a : Label} (ha : 0 < a.1 ∧ 0 < a.2) : vhat bs d N a = 0 := by
  unfold vhat
  rw [piG_eq_zero hbs hirr d, WG_eq_zero hbs hirr d _ a ha]

open Classical in
theorem collClass_singleton {N : ℕ} {a : Label} (ha : a ∈ labels N) :
    collClass N bs (kacHL a bs) = {a} := by
  ext g
  rw [mem_collClass, Finset.mem_singleton]
  constructor
  · rintro ⟨hg, heq⟩
    by_contra hne
    have hgp := labels_pos hg
    have hap := labels_pos ha
    have := kacH_ne hbs hirr (g.1 : ℤ) (g.2 : ℤ) (a.1 : ℤ) (a.2 : ℤ)
      (by exact_mod_cast hgp.1) (by exact_mod_cast hgp.2) (by exact_mod_cast hap.1)
      (by exact_mod_cast hap.2) (by
        intro h
        apply hne
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2))
    exact this (sub_eq_zero.2 heq)
  · rintro rfl
    exact ⟨ha, rfl⟩

open Classical in
theorem Mhat_eq_one {N : ℕ} {a : Label} (ha : a ∈ labels N) :
    Mhat bs d N (kacHL a bs) = 1 := by
  unfold Mhat
  rw [collClass_singleton hbs hirr ha, Finset.sup_singleton, vhat_eq_zero hbs hirr d N (labels_pos ha)]
  split_ifs <;> simp

open Classical in
theorem Atilde_one {N : ℕ} {a : Label} (ha : a ∈ labels N) :
    Atilde bs d N (kacHL a bs) 1 = (BG bs d N a).coeff 0 := by
  unfold Atilde
  rw [collClass_singleton hbs hirr ha, Finset.sum_singleton]
  simp

open Classical in
/-- In the irrational case the confluence identity is the generic recursion at `b⋆`, and the
shifted coefficients are regular at `t = 0` with the block coefficients as values. -/
theorem irrational_recursion
    (hrec : ∀ M, 1 ≤ M →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M) :
    ∀ N : ℕ, (1 ≤ N → GenericRecursionAt K bs d N) ∧
      ∀ a : Label, 0 < a.1 ∧ 0 < a.2 →
        RegVal (SG bs d N a) (evalAt (kacHL a bs + (a.lvl : K)) (Hrat (kacC bs) d N)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hB : 1 ≤ N → GenericRecursionAt K bs d N := by
      intro hN
      have hid := confluence_identity hbs d hN (fun M h1 _ => hrec M h1)
      unfold GenericRecursionAt
      rw [hid]
      unfold Lam
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl fun a ha => ?_
        have hap := labels_pos ha
        have hl := lvl_pos_of_mem_labels ha
        rw [Mhat_eq_one hbs hirr d ha, Finset.Icc_self, Finset.sum_singleton, pow_one,
          Atilde_one hbs hirr d ha]
        have hS := (ih (N - a.lvl) (by omega)).2 a hap
        have hBG : (BG bs d N a).coeff 0 = genR a.1 a.2 bs d *
            evalAt (kacHL a bs + (a.lvl : K)) (Hrat (kacC bs) d (N - a.lvl)) :=
          ((regVal_RG hbs hirr d a).mul hS).2
        rw [hBG, map_mul]
        unfold evalAt
        ring
      · intro a ha g hg heq
        have h1 := collClass_singleton hbs hirr ha
        have : g ∈ collClass N bs (kacHL a bs) := mem_collClass.2 ⟨hg, heq.symm⟩
        rw [h1, Finset.mem_singleton] at this
        exact this.symm
    refine ⟨hB, fun a ha => ?_⟩
    cases N with
    | zero =>
      rw [SG_zero, Hrat_zero]
      simpa [evalAt] using regVal_C (1 : K)
    | succ M =>
      have hrecM := hB (by omega)
      have hne : ∀ g ∈ labels (M + 1), kacHL a bs + (a.lvl : K) ≠ kacHL g bs := fun g hg h =>
        shift_value_ne hbs hirr ha (labels_pos hg) (sub_eq_zero.2 h)
      rw [evalAt_recursion hrecM hne, SG_succ, ← Finset.sum_attach (labels (M + 1))]
      refine RegVal.sum fun g _ => ?_
      have hg := labels_pos g.2
      have hl := lvl_pos_of_mem_labels g.2
      have hS := (ih (M + 1 - g.1.lvl) (by omega)).2 g.1 hg
      exact ((regVal_RG hbs hirr d g.1).div (regVal_shift hbs hirr)
        (shift_value_ne hbs hirr ha hg)).mul hS

end General

/-- The irrational case of Theorem 4.3, from the generic recursion. -/
theorem confluence_irrational (hrec : GenericRecursionUniform) {b : ℂ} (hb : b ≠ 0)
    (hq : ∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) {N : ℕ} (hN : 1 ≤ N) :
    (∀ lam ∈ Lam N b, (collClass N b lam).card = 1 ∧ MhatC b N lam = 1) ∧
      GenericRecursionAt Kd (RatFunc.C b) dvar N := by
  classical
  have hbs : (RatFunc.C b : Kd) ≠ 0 := by simpa using hb
  have hirr : SqIrrational (RatFunc.C b : Kd) :=
    sqIrrational_map (RatFunc.C : ℂ →+* Kd) (x := b) hq
  refine ⟨fun lam hlam => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hlam
    have hpt : pt (kacHL a b) = kacHL a (RatFunc.C b : Kd) := (kacHL_ratC a b).symm
    constructor
    · rw [← collClass_ratC, hpt, collClass_singleton hbs hirr ha, Finset.card_singleton]
    · unfold MhatC
      rw [hpt]
      exact Mhat_eq_one hbs hirr dvar ha
  · exact (irrational_recursion hbs hirr dvar
      (fun M h1 => germ_recursion hrec (RatFunc.C b : Kd) dvar M h1) N).1 hN

end Virasoro
