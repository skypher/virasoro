import Virasoro.Proofs.SmithLayers
import Virasoro.Proofs.Naturality
import Virasoro.Statements.Sec5a
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Lemma 5.6, dimension part: Jantzen layers and Smith exponents

Polynomial families and power-series families define the same layers (truncation modulo
`x^i`), so `dim J^i_N = #{j : e_j ≥ i}` by the Smith normal form, and summing over `i ≥ 1` gives
`ord_x det G_N(c,h+x)`.
-/

namespace Virasoro

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

theorem gramLocal_eq_map_coe (c h : K) (N : ℕ) :
    gramLocal c h N = (gramShift c h N).map (Polynomial.coeToPowerSeries.ringHom) := by
  have := gram_map (Polynomial.coeToPowerSeries.ringHom (R := K)) (C c) (C h + X) N
  rw [gramShift, ← this, gramLocal]
  simp [Polynomial.coeToPowerSeries.ringHom]

theorem coe_mulVec (c h : K) (N : ℕ) (w : Nat.Partition N → K[X]) (Y : Nat.Partition N) :
    (((gramShift c h N).mulVec w Y : K[X]) : PowerSeries K)
      = (gramLocal c h N).mulVec (fun Z => ((w Z : K[X]) : PowerSeries K)) Y := by
  rw [gramLocal_eq_map_coe]
  exact RingHom.map_mulVec (Polynomial.coeToPowerSeries.ringHom (R := K)) (gramShift c h N) w Y

omit [CharZero K] in
theorem X_pow_dvd_coe_trunc_sub (φ : PowerSeries K) {i n : ℕ} (hin : i ≤ n) :
    (PowerSeries.X : PowerSeries K) ^ i ∣ ((PowerSeries.trunc n φ : K[X]) : PowerSeries K) - φ := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (by omega), sub_self]

/-- Polynomial families and power-series families define the same layers. -/
theorem jantzenLayer_eq_layer (c h : K) (N i : ℕ) :
    jantzenLayer c h N i = layer (gramLocal c h N) i := by
  ext v
  constructor
  · rintro ⟨w, hw0, hdvd⟩
    refine ⟨fun Y => ((w Y : K[X]) : PowerSeries K), fun Y => ?_, fun Y => ?_⟩
    · rw [← hw0 Y, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
        Polynomial.coeff_zero_eq_eval_zero]
    · rw [← coe_mulVec]
      have := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := K)) (hdvd Y)
      simpa [Polynomial.coeToPowerSeries.ringHom] using this
  · rintro ⟨V, hV0, hdvd⟩
    refine ⟨fun Y => PowerSeries.trunc (i + 1) (V Y), fun Y => ?_, fun Y => ?_⟩
    · rw [← hV0 Y, ← Polynomial.coeff_zero_eq_eval_zero, PowerSeries.coeff_trunc,
        if_pos (by omega), PowerSeries.coeff_zero_eq_constantCoeff_apply]
    · rw [Polynomial.X_pow_dvd_iff]
      intro m hm
      rw [← Polynomial.coeff_coe, coe_mulVec]
      have e : (fun Z => ((PowerSeries.trunc (i + 1) (V Z) : K[X]) : PowerSeries K))
          = V + fun Z => ((PowerSeries.trunc (i + 1) (V Z) : K[X]) : PowerSeries K) - V Z := by
        funext Z
        simp
      rw [e, Matrix.mulVec_add, Pi.add_apply]
      have h1 : (PowerSeries.X : PowerSeries K) ^ i ∣ (gramLocal c h N).mulVec V Y
          + (gramLocal c h N).mulVec
            (fun Z => ((PowerSeries.trunc (i + 1) (V Z) : K[X]) : PowerSeries K) - V Z) Y :=
        dvd_add (hdvd Y) (dvd_mulVec (fun Z => X_pow_dvd_coe_trunc_sub (V Z) (by omega)) Y)
      exact (PowerSeries.X_pow_dvd_iff.1 h1) m hm

theorem sum_filter_card (s : Multiset ℕ) (M : ℕ) (hM : ∀ e ∈ s, e ≤ M) :
    ∑ i ∈ Finset.Icc 1 M, (s.filter fun e => i ≤ e).card = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha : a ≤ M := hM a (Multiset.mem_cons_self a t)
    have ht := ih fun e he => hM e (Multiset.mem_cons_of_mem he)
    have e1 : ∀ i, ((a ::ₘ t).filter fun e => i ≤ e).card
        = (t.filter fun e => i ≤ e).card + (if i ≤ a then 1 else 0) := by
      intro i
      rw [Multiset.filter_cons]
      split_ifs with hia
      · simp
      · simp
    simp only [e1]
    rw [Finset.sum_add_distrib, ht, Multiset.sum_cons, add_comm]
    congr 1
    rw [Finset.sum_boole]
    have : (Finset.Icc 1 M).filter (fun i => i ≤ a) = Finset.Icc 1 a := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [this]
    simp

/-- The dimension statements of Lemma 5.6. -/
theorem jantzen_dim (c h : K) (N : ℕ) (s : Multiset ℕ) (hs : IsSmith (gramLocal c h N) s) :
    (∀ i : ℕ, Module.finrank K (jantzenLayer c h N i) = (s.filter fun e => i ≤ e).card) ∧
    (((∑ᶠ i : ℕ, if 1 ≤ i then Module.finrank K (jantzenLayer c h N i) else 0 : ℕ) : ℕ∞) =
      (gramLocal c h N).det.order) := by
  have h1 : ∀ i : ℕ, Module.finrank K (jantzenLayer c h N i)
      = (s.filter fun e => i ≤ e).card := by
    intro i
    rw [jantzenLayer_eq_layer]
    exact finrank_layer hs i
  refine ⟨h1, ?_⟩
  rw [(smith_main hs).1]
  congr 1
  have hsupp : (Function.support fun i : ℕ =>
      if 1 ≤ i then Module.finrank K (jantzenLayer c h N i) else 0)
      ⊆ ↑(Finset.Icc 1 s.sup) := by
    intro i hi
    rw [Function.mem_support] at hi
    rw [Finset.mem_coe, Finset.mem_Icc]
    by_contra hcon
    apply hi
    by_cases h1i : 1 ≤ i
    · rw [if_pos h1i, h1]
      have : s.filter (fun e => i ≤ e) = 0 := by
        rw [Multiset.filter_eq_nil]
        intro e he hie
        have := Multiset.le_sup he
        omega
      rw [this, Multiset.card_zero]
    · rw [if_neg h1i]
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  rw [← sum_filter_card s s.sup fun e he => Multiset.le_sup he]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [if_pos (Finset.mem_Icc.1 hi).1, h1]

end Virasoro
