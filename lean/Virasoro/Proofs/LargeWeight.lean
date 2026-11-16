import Virasoro.Proofs.LargeWeightCore
import Virasoro.Proofs.EtaPartition
import Virasoro.Proofs.EvalLemmas
import Virasoro.Statements.Sec4
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Polynomial

/-!
# Lemma 4.1: the limit of large internal weight
-/

namespace Virasoro

open Polynomial Filter Topology

/-- `p(z)/z^m → p_m` as `|z| → ∞`, for a complex polynomial `p` of degree at most `m`. -/
theorem tendsto_eval_div_pow (p : ℂ[X]) (m : ℕ) (hp : p.natDegree ≤ m) :
    Tendsto (fun z : ℂ => p.eval z / z ^ m) (Bornology.cobounded ℂ) (𝓝 (p.coeff m)) := by
  have hsum : ∀ z : ℂ, p.eval z / z ^ m
      = ∑ k ∈ Finset.range (m + 1), p.coeff k * (z ^ k / z ^ m) := by
    intro z
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_div_assoc]
  have hlim : ∀ k ∈ Finset.range (m + 1),
      Tendsto (fun z : ℂ => p.coeff k * (z ^ k / z ^ m)) (Bornology.cobounded ℂ)
        (𝓝 (p.coeff k * (if k = m then 1 else 0))) := by
    intro k hk
    refine Tendsto.const_mul _ ?_
    by_cases hkm : k = m
    · rw [if_pos hkm, hkm]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
      rw [div_self (pow_ne_zero m hz)]
    · rw [if_neg hkm]
      have hk' : k < m := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hkm
      have h0 : Tendsto (fun z : ℂ => z⁻¹ ^ (m - k)) (Bornology.cobounded ℂ) (𝓝 0) := by
        have := (tendsto_inv₀_cobounded (α := ℂ)).pow (m - k)
        rwa [zero_pow (by omega)] at this
      refine h0.congr' ?_
      filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
      rw [inv_pow, eq_div_iff (pow_ne_zero m hz)]
      have e : z ^ m = z ^ (m - k) * z ^ k := by
        rw [← pow_add]
        congr 1
        omega
      rw [e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hz), one_mul]
  have := tendsto_finsetSum (Finset.range (m + 1)) hlim
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_range,
    Nat.lt_succ_self, if_true] at this
  exact this.congr fun z => (hsum z).symm

/-- A quotient of complex polynomials with `deg P < deg Q` tends to zero at infinity, and the
denominator is eventually nonzero. -/
theorem tendsto_eval_div_of_degree_lt (P Q : ℂ[X]) (h : P.degree < Q.degree) :
    Tendsto (fun z : ℂ => P.eval z / Q.eval z) (Bornology.cobounded ℂ) (𝓝 0) ∧
      ∀ᶠ z in Bornology.cobounded ℂ, Q.eval z ≠ 0 := by
  have hQ : Q ≠ 0 := by
    rintro rfl
    rw [degree_zero] at h
    exact not_lt_bot h
  have hPm : P.natDegree ≤ Q.natDegree := by
    by_cases hP : P = 0
    · rw [hP, natDegree_zero]; exact Nat.zero_le _
    · exact (natDegree_lt_natDegree hP h).le
  have hPc : P.coeff Q.natDegree = 0 := by
    by_cases hP : P = 0
    · rw [hP, coeff_zero]
    · exact coeff_eq_zero_of_natDegree_lt (natDegree_lt_natDegree hP h)
  have h1 := tendsto_eval_div_pow P Q.natDegree hPm
  have h2 := tendsto_eval_div_pow Q Q.natDegree le_rfl
  rw [hPc] at h1
  have hlc : Q.coeff Q.natDegree ≠ 0 := by
    rw [coeff_natDegree]
    exact leadingCoeff_ne_zero.2 hQ
  have hev : ∀ᶠ z in Bornology.cobounded ℂ, Q.eval z ≠ 0 := by
    filter_upwards [h2.eventually_ne hlc] with z hz
    intro h0
    rw [h0, zero_div] at hz
    exact hz rfl
  refine ⟨?_, hev⟩
  have h3 := h1.div h2 hlc
  rw [zero_div] at h3
  refine h3.congr' ?_
  filter_upwards [Bornology.eventually_ne_cobounded (0 : ℂ)] with z hz
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ (pow_ne_zero _ hz)]

/-- `F_N(c,Δ,d) → p(N)` as `Δ → ∞`, for the pointwise values. -/
theorem tendsto_Fval (c d : ℂ) (M : ℕ) :
    Tendsto (fun z : ℂ => Fval c d z M) (Bornology.cobounded ℂ)
      (𝓝 (Fintype.card (Nat.Partition M) : ℂ)) := by
  obtain ⟨h1, h2⟩ := tendsto_eval_div_of_degree_lt _ _ (degree_Fnum_sub_lt c d M)
  have h3 : Tendsto (fun z : ℂ => (Fnum c d M
      - (Fintype.card (Nat.Partition M) : ℂ[X]) * (gramPoly c M).det).eval z
        / (gramPoly c M).det.eval z + (Fintype.card (Nat.Partition M) : ℂ))
      (Bornology.cobounded ℂ) (𝓝 (0 + (Fintype.card (Nat.Partition M) : ℂ))) :=
    h1.add tendsto_const_nhds
  rw [zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [h2] with z hz
  unfold Fval
  rw [← Fnum_eval, ← gramPoly_det_eval, eval_sub, eval_mul, eval_natCast]
  field_simp
  ring

theorem eventually_gram_det_ne_zero (c : ℂ) (M : ℕ) :
    ∀ᶠ z in Bornology.cobounded ℂ, (gram c z M).det ≠ 0 := by
  obtain ⟨-, h2⟩ := tendsto_eval_div_of_degree_lt _ _ (degree_Fnum_sub_lt c (0 : ℂ) M)
  filter_upwards [h2] with z hz
  rwa [← gramPoly_det_eval]

/-- For fixed `c, d, N`: `lim_{Δ→∞} F_N(c,Δ,d) = p(N)` and `lim_{Δ→∞} H_N(c,Δ,d) = δ_{N,0}`.

Paper label: lem:large-weight -/
theorem lem_large_weight : Stmt_lem_large_weight := by
  intro c d N
  have hall : ∀ᶠ z in Bornology.cobounded ℂ, ∀ M ∈ Finset.range (N + 1),
      (gram c z M).det ≠ 0 :=
    (Filter.eventually_all_finset _).2 fun M _ => eventually_gram_det_ne_zero c M
  constructor
  · refine (tendsto_Fval c d N).congr' ?_
    filter_upwards [eventually_gram_det_ne_zero c N] with z hz
    exact (evalAt_Frat hz).symm
  · have hH : Tendsto (fun z : ℂ => Hval c d z N) (Bornology.cobounded ℂ)
        (𝓝 (∑ j ∈ Finset.range (N + 1),
          (eta j : ℂ) * (Fintype.card (Nat.Partition (N - j)) : ℂ))) := by
      unfold Hval
      exact tendsto_finsetSum _ fun j _ => (tendsto_Fval c d (N - j)).const_mul _
    have hsum : (∑ j ∈ Finset.range (N + 1),
        (eta j : ℂ) * (Fintype.card (Nat.Partition (N - j)) : ℂ)) = if N = 0 then 1 else 0 := by
      have := congrArg (Int.cast : ℤ → ℂ) (eta_partition N)
      push_cast at this
      rw [this]
    rw [hsum] at hH
    refine hH.congr' ?_
    filter_upwards [hall] with z hz
    exact (evalAt_Hrat fun M hM => hz M (Finset.mem_range.2 (Nat.lt_succ_of_le hM))).symm

example : Stmt_lem_large_weight := lem_large_weight

end Virasoro
