import Virasoro.Proofs.Sec4Core2
import Virasoro.Statements.Sec4
import Virasoro.Statements.Sec6

/-!
# Theorem 4.3, part III: the confluence identity and the collision moments
-/

namespace Virasoro

open scoped LaurentSeries
open Polynomial

section General

variable {K : Type*} [Field K] [CharZero K] (bs d : K)

theorem ordGE_deltaG_one {bs : K} (hbs : bs ≠ 0) (a : Label) :
    OrdGE (deltaG bs (kacHL a bs) a) 1 := by
  have h := (regVal_hG hbs a).sub (regVal_C (kacHL a bs))
  rw [sub_self] at h
  refine ordGE_iff.2 fun m hm => ?_
  rcases lt_or_eq_of_le (show m ≤ 0 by omega) with h0 | h0
  · exact h.1.coeff_eq_zero h0
  · rw [h0]; exact h.2

theorem ordGE_BG (N : ℕ) (a : Label) : OrdGE (BG bs d N a) (-((vhat bs d N a : ℕ) : ℤ)) := by
  unfold BG vhat
  refine ((ordGE_RG bs d a).mul (ordGE_SG bs d _ a)).mono ?_
  push_cast
  linarith

theorem ratFunc_X_sub_C_ne_zero (c : K) : (RatFunc.X - RatFunc.C c : RatFunc K) ≠ 0 := by
  intro h
  have h1 : (RatFunc.X : RatFunc K) = RatFunc.C c := sub_eq_zero.1 h
  have h2 := congrArg RatFunc.intDegree h1
  rw [RatFunc.intDegree_X, RatFunc.intDegree_C] at h2
  exact one_ne_zero h2

/-- The constant term in `t` of the grouped identity: `H_N(c⋆,Δ,d)` as a sum over labels of
truncated geometric expansions. -/
theorem confluence_labels {bs : K} (hbs : bs ≠ 0) (d : K) {N : ℕ} (hN : 1 ≤ N)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M)
    (n : Label → ℕ) (hn : ∀ a ∈ labels N, vhat bs d N a < n a) :
    Hrat (kacC bs) d N =
      ∑ a ∈ labels N, ∑ j ∈ Finset.range (n a),
        RatFunc.C ((BG bs d N a * deltaG bs (kacHL a bs) a ^ j).coeff 0) /
          (RatFunc.X - RatFunc.C (kacHL a bs)) ^ (j + 1) := by
  set ι : K →+* RatFunc K := algebraMap K (RatFunc K) with hι
  have hsplit : ∀ a : Label, HahnSeries.C (RatFunc.X : RatFunc K) - mapL ι (hG bs a) =
      HahnSeries.C (RatFunc.X - RatFunc.C (kacHL a bs)) -
        mapL ι (deltaG bs (kacHL a bs) a) := by
    intro a
    have h1 : mapL ι (deltaG bs (kacHL a bs) a) =
        mapL ι (hG bs a) - HahnSeries.C (RatFunc.C (kacHL a bs)) := by
      rw [deltaG, map_sub, mapL_C, hι, RatFunc.algebraMap_eq_C]
    have h2 : (HahnSeries.C (RatFunc.X - RatFunc.C (kacHL a bs)) : (RatFunc K)⸨X⸩) =
        HahnSeries.C RatFunc.X - HahnSeries.C (RatFunc.C (kacHL a bs)) := map_sub _ _ _
    rw [h1, h2]
    ring
  have hz : ∀ a ∈ labels N, HahnSeries.C (RatFunc.X : RatFunc K) ≠ mapL ι (hG bs a) := by
    intro a _ heq
    have h0 := sub_eq_zero.2 heq
    rw [hsplit] at h0
    have hc := congrArg (fun x : (RatFunc K)⸨X⸩ => x.coeff 0) h0
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_zero] at hc
    rw [((ordGE_deltaG_one hbs a).mapL (ι := ι)).coeff_eq_zero (by norm_num), sub_zero] at hc
    have : (HahnSeries.C (RatFunc.X - RatFunc.C (kacHL a bs)) : (RatFunc K)⸨X⸩).coeff 0 =
        RatFunc.X - RatFunc.C (kacHL a bs) := (regVal_C _).2
    rw [this] at hc
    exact ratFunc_X_sub_C_ne_zero _ hc
  have hgr := grouped_at bs d N hbs hN hrec hz
  have hreg := regVal_Hrat_germ bs d hbs N
  rw [← hι] at hreg
  rw [← hreg.2, hgr, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hsplit]
  have hlt : (0 : ℤ) < -((vhat bs d N a : ℕ) : ℤ) + (n a : ℕ) := by
    have := hn a ha
    have : ((vhat bs d N a : ℕ) : ℤ) < (n a : ℕ) := by exact_mod_cast this
    linarith
  rw [pole_support ι _ (ratFunc_X_sub_C_ne_zero _) _ _ (ordGE_deltaG_one hbs a) (ordGE_BG bs d N a)
    0 (n a) hlt]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hι, RatFunc.algebraMap_eq_C]

theorem sum_range_succ_eq_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ j ∈ Finset.range n, f (j + 1) = ∑ k ∈ Finset.Icc 1 n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, ← Finset.sum_Icc_succ_top (by omega)]

open Classical in
theorem mem_collClass {N : ℕ} {b lam : K} {a : Label} :
    a ∈ collClass N b lam ↔ a ∈ labels N ∧ kacHL a b = lam := by
  simp [collClass]

/-- The collision moments vanish beyond the a priori pole bound. -/
theorem Atilde_eq_zero {bs : K} (hbs : bs ≠ 0) (d : K) (N : ℕ) (lam : K) {k : ℕ}
    (hk : Mhat bs d N lam < k) : Atilde bs d N lam k = 0 := by
  classical
  unfold Atilde
  rw [HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have hlam : kacHL a bs = lam := (mem_collClass.1 ha).2
  have hle : (if deltaG bs lam a = 0 then 1
      else 1 + vhat bs d N a / ((deltaG bs lam a).order).toNat) ≤ Mhat bs d N lam :=
    Finset.le_sup (f := fun a => if deltaG bs lam a = 0 then 1
      else 1 + vhat bs d N a / ((deltaG bs lam a).order).toNat) ha
  by_cases h0 : deltaG bs lam a = 0
  · rw [if_pos h0] at hle
    rw [h0, zero_pow (by omega), mul_zero, HahnSeries.coeff_zero]
  · rw [if_neg h0] at hle
    have hδ1 : OrdGE (deltaG bs lam a) 1 := by rw [← hlam]; exact ordGE_deltaG_one hbs a
    have hord1 : 1 ≤ (deltaG bs lam a).order := by
      have := hδ1
      unfold OrdGE at this
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0] at this
      exact_mod_cast this
    set ε := ((deltaG bs lam a).order).toNat with hε
    have hεpos : 0 < ε := by omega
    have hεeq : (ε : ℤ) = (deltaG bs lam a).order := Int.toNat_of_nonneg (by omega)
    have hpow : OrdGE (deltaG bs lam a ^ (k - 1)) (((k - 1 : ℕ) : ℤ) * (ε : ℤ)) := by
      rw [hεeq]
      exact (ordGE_order _).pow (k - 1)
    have hprod := (ordGE_BG bs d N a).mul hpow
    apply hprod.coeff_eq_zero
    have hdiv : vhat bs d N a / ε < k - 1 := by omega
    have hlt : vhat bs d N a < (k - 1) * ε := (Nat.div_lt_iff_lt_mul hεpos).1 hdiv
    have : ((vhat bs d N a : ℕ) : ℤ) < ((k - 1 : ℕ) : ℤ) * (ε : ℤ) := by exact_mod_cast hlt
    linarith

open Classical in
/-- The confluence identity (4.1) over an arbitrary coefficient field: under the generic
recursion for the germ `b⋆ + t`,
`H_N(c⋆,Δ,d) = ∑_{λ ∈ Λ_N} ∑_{k=1}^{M̂} Ã_{λ,k,N}/(Δ - λ)^k`. -/
theorem confluence_identity {bs : K} (hbs : bs ≠ 0) (d : K) {N : ℕ} (hN : 1 ≤ N)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M) :
    Hrat (kacC bs) d N =
      ∑ lam ∈ Lam N bs, ∑ k ∈ Finset.Icc 1 (Mhat bs d N lam),
        RatFunc.C (Atilde bs d N lam k) / (RatFunc.X - RatFunc.C lam) ^ k := by
  -- a uniform truncation order
  set n₀ : ℕ := (labels N).sup (fun a => vhat bs d N a) + (Lam N bs).sup (fun lam => Mhat bs d N lam) + 1
    with hn₀
  have hn : ∀ a ∈ labels N, vhat bs d N a < n₀ := by
    intro a ha
    have := Finset.le_sup (f := fun a => vhat bs d N a) ha
    omega
  rw [confluence_labels hbs d hN hrec (fun _ => n₀) hn]
  have hmaps : ∀ a ∈ labels N, kacHL a bs ∈ Lam N bs := fun a ha =>
    Finset.mem_image_of_mem _ ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  have hcl : ((labels N).filter fun a => kacHL a bs = lam) = collClass N bs lam := rfl
  rw [hcl]
  have hstep : ∑ a ∈ collClass N bs lam, ∑ j ∈ Finset.range n₀,
        RatFunc.C ((BG bs d N a * deltaG bs (kacHL a bs) a ^ j).coeff 0) /
          (RatFunc.X - RatFunc.C (kacHL a bs)) ^ (j + 1) =
      ∑ j ∈ Finset.range n₀, RatFunc.C (Atilde bs d N lam (j + 1)) /
        (RatFunc.X - RatFunc.C lam) ^ (j + 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Atilde
    rw [HahnSeries.coeff_sum, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(mem_collClass.1 ha).2, Nat.add_sub_cancel]
  rw [hstep, sum_range_succ_eq_Icc
    (fun k => RatFunc.C (Atilde bs d N lam k) / (RatFunc.X - RatFunc.C lam) ^ k) n₀]
  symm
  have hMle : Mhat bs d N lam ≤ n₀ := by
    have := Finset.le_sup (f := fun lam => Mhat bs d N lam) hlam
    omega
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hMle)
  intro k hk hk'
  have hgt : Mhat bs d N lam < k := by
    simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
    exact hk' hk.1
  rw [Atilde_eq_zero hbs d N lam hgt, map_zero, zero_div]

end General

end Virasoro
