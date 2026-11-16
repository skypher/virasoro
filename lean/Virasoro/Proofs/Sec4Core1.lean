import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.Expand
import Virasoro.Statements.Sec7
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Theorem 4.3, part I: from the generic recursion to the grouped identity at a point
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

section General

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

theorem partition_zero_word (Y : Nat.Partition 0) : Y.word = [] := by
  have hparts : Y.parts = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro i hi
    have h1 := Y.parts_pos hi
    have h2 := Multiset.le_sum_of_mem hi
    rw [Y.parts_sum] at h2
    omega
  simp [Nat.Partition.word, hparts]

theorem eta_zero : eta 0 = 1 := by simp [eta]

/-- `F_0 = 1`. -/
theorem Frat_zero (c d : 𝔽) : Frat c d 0 = 1 := by
  have hg : gramPoly c 0 = 1 := by
    ext Y Y'
    rw [Subsingleton.elim Y Y']
    simp [gramPoly, gram, partition_zero_word, gramWord, vac]
  have ht : ∀ Y Y' : Nat.Partition 0, torusPoly c d 0 Y Y' = 1 := by
    intro Y Y'
    simp [torusPoly, torus, partition_zero_word, torusWord, phi]
  unfold Frat Fnum
  rw [hg, Matrix.det_one, Matrix.adjugate_one]
  simp [ht, Matrix.one_apply]

/-- `H_0 = 1`. -/
theorem Hrat_zero (c d : 𝔽) : Hrat c d 0 = 1 := by
  simp [Hrat, eta_zero, Frat_zero]

/-- The generic recursion evaluated at a point `z` different from the Kac weights. -/
theorem evalAt_recursion {b d z : 𝔽} {M : ℕ} (hrec : GenericRecursionAt 𝔽 b d M)
    (hz : ∀ a ∈ labels M, z ≠ kacHL a b) :
    evalAt z (Hrat (kacC b) d M) =
      ∑ a ∈ labels M, genR a.1 a.2 b d / (z - kacHL a b) *
        evalAt (kacHL a b + (a.lvl : 𝔽)) (Hrat (kacC b) d (M - a.lvl)) := by
  unfold GenericRecursionAt at hrec
  rw [hrec]
  have hterm : ∀ a ∈ labels M,
      RatFunc.C (genR a.1 a.2 b d) / (RatFunc.X - RatFunc.C (kacHL a b)) *
          RatFunc.C (RatFunc.eval (RingHom.id 𝔽) (kacHL a b + (a.lvl : 𝔽))
            (Hrat (kacC b) d (M - a.lvl))) =
        algebraMap 𝔽[X] (RatFunc 𝔽) (C (genR a.1 a.2 b d)) /
            algebraMap 𝔽[X] (RatFunc 𝔽) (X - C (kacHL a b)) *
          algebraMap 𝔽[X] (RatFunc 𝔽) (C (evalAt (kacHL a b + (a.lvl : 𝔽))
            (Hrat (kacC b) d (M - a.lvl)))) := by
    intro a _
    simp [RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rw [Finset.sum_congr rfl hterm]
  have hq : ∀ a ∈ labels M, (X - C (kacHL a b) : 𝔽[X]).eval z ≠ 0 := by
    intro a ha
    simpa [sub_ne_zero] using hz a ha
  rw [evalAt_sum fun a ha => (regAt_div z _ (hq a ha)).mul (regAt_algebraMap z _)]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [evalAt_mul (regAt_div z _ (hq a ha)) (regAt_algebraMap z _), evalAt_div z _ (hq a ha),
    evalAt_algebraMap]
  simp

end General

section Germ

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] (ι : K →+* L)

theorem mapL_C (c : K) : mapL ι (HahnSeries.C c) = HahnSeries.C (ι c) := by
  ext n
  simp only [mapL_coeff, HahnSeries.C, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    HahnSeries.coeff_single]
  split_ifs <;> simp

theorem mapL_bGerm (bs : K) : mapL ι (bGerm bs) = bGerm (ι bs) := by
  ext n
  simp only [bGerm, mapL_coeff, HahnSeries.coeff_add, map_add, HahnSeries.C, RingHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, HahnSeries.coeff_single]
  congr 1 <;> split_ifs <;> simp

theorem mapL_injective : Function.Injective (mapL ι) := (mapL ι).injective

theorem sqIrrational_bGerm (bs : K) : SqIrrational (bGerm bs) := by
  intro q h
  have hP : (X ^ 2 - C q : ℚ[X]) ≠ 0 := by
    intro h0
    have := congrArg (fun p : ℚ[X] => p.coeff 2) h0
    simp [coeff_X_pow, coeff_C] at this
  apply aeval_bGerm_ne_zero bs hP
  simp [h]

theorem sqIrrational_map {F F' : Type*} [Field F] [Field F'] (φ : F →+* F') {x : F}
    (h : SqIrrational x) : SqIrrational (φ x) := by
  intro q hq
  apply h q
  apply φ.injective
  rw [map_pow, hq, map_ratCast]

theorem aeval_map_ne_zero {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
    (φ : F →+* F') {x : F} {P : ℚ[X]} (h : aeval x P ≠ 0) : aeval (φ x) P ≠ 0 := by
  have : aeval (φ x) P = φ (aeval x P) := by
    rw [aeval_def, aeval_def, hom_eval₂]
    congr 1
    exact RingHom.ext fun q => by simp
  rw [this]
  exact (map_ne_zero φ).2 h

variable {ι} (bs d : K) (N : ℕ)

/-- Under the generic recursion for the germ `b⋆ + t` (transported to `L⸨t⸩`), the shifted
coefficients are the values of the block coefficients:
`S_{a,M}(t) = H_M(c(b), z_a(t), d)`. -/
theorem SG_eq_eval (hbs : bs ≠ 0)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      GenericRecursionAt L⸨X⸩ (mapL ι (bGerm bs)) (mapL ι (HahnSeries.C d)) M) :
    ∀ M, M ≤ N → ∀ a : Label, 0 < a.1 → 0 < a.2 →
      mapL ι (SG bs d M a) =
        evalAt (mapL ι (zG bs a))
          (Hrat (kacC (mapL ι (bGerm bs))) (mapL ι (HahnSeries.C d)) M) := by
  have hb'ne : mapL ι (bGerm bs) ≠ 0 := (map_ne_zero (mapL ι)).2 (bGerm_ne_zero hbs)
  have hirr : SqIrrational (mapL ι (bGerm bs)) := sqIrrational_map _ (sqIrrational_bGerm bs)
  have hzG : ∀ a : Label, mapL ι (zG bs a) =
      kacHL a (mapL ι (bGerm bs)) + ((a.lvl : ℕ) : L⸨X⸩) := by
    intro a
    rw [zG, map_add, map_natCast, hG, map_kacHL]
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM a ha1 ha2
    cases M with
    | zero =>
      rw [SG_zero, Hrat_zero, map_one]
      simp [evalAt]
    | succ M =>
      have hne : ∀ g ∈ labels (M + 1), mapL ι (zG bs a) ≠ kacHL g (mapL ι (bGerm bs)) := by
        intro g hg
        have hg' := hg
        simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg'
        have := kacH_shift_ne hb'ne hirr (a.1 : ℤ) (a.2 : ℤ) (g.1 : ℤ) (g.2 : ℤ)
          (by exact_mod_cast ha1) (by exact_mod_cast ha2) (by exact_mod_cast hg'.1.1.1)
          (by exact_mod_cast hg'.1.2.1)
        rw [hzG]
        intro heq
        apply this
        rw [sub_eq_zero]
        simpa [kacHL, Label.lvl] using heq
      rw [evalAt_recursion (hrec (M + 1) (by omega) hM) hne, SG_succ, map_sum,
        ← Finset.sum_attach (labels (M + 1))]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hglvl := lvl_pos_of_mem_labels g.2
      have hg' := g.2
      simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg'
      rw [map_mul, map_div₀, map_sub, ih (M + 1 - g.1.lvl) (by omega) (by omega) g.1
        hg'.1.1.1 hg'.1.2.1, hzG g.1]
      congr 2
      · rw [RG, map_genR]
      · rw [hG, map_kacHL]

/-- The grouped identity (7.3) at a point `z` away from the Kac weights. -/
theorem grouped_at (hbs : bs ≠ 0) (hN : 1 ≤ N)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      GenericRecursionAt L⸨X⸩ (mapL ι (bGerm bs)) (mapL ι (HahnSeries.C d)) M)
    {z : L⸨X⸩} (hz : ∀ a ∈ labels N, z ≠ mapL ι (hG bs a)) :
    evalAt z (Hrat (kacC (mapL ι (bGerm bs))) (mapL ι (HahnSeries.C d)) N) =
      ∑ a ∈ labels N, mapL ι (BG bs d N a) / (z - mapL ι (hG bs a)) := by
  have hhG : ∀ a : Label, mapL ι (hG bs a) = kacHL a (mapL ι (bGerm bs)) := by
    intro a; rw [hG, map_kacHL]
  rw [evalAt_recursion (hrec N hN le_rfl) (fun a ha => by rw [← hhG]; exact hz a ha)]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha' := ha
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at ha'
  have hS := SG_eq_eval bs d N hbs hrec (N - a.lvl) (Nat.sub_le _ _) a ha'.1.1.1 ha'.1.2.1
  have hzG : mapL ι (zG bs a) = kacHL a (mapL ι (bGerm bs)) + ((a.lvl : ℕ) : L⸨X⸩) := by
    rw [zG, map_add, map_natCast, hG, map_kacHL]
  rw [← hzG, ← hS, BG, map_mul, RG, map_genR, hhG]
  ring

end Germ

end Virasoro
