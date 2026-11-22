import Virasoro.Proofs.RegEvalK
import Virasoro.Proofs.EvalLemmas
import Virasoro.Proofs.Sec4Core2
import Virasoro.Proofs.TwoBranchA

/-!
# Corollary 9.4: evaluation tools (paper.tex l.1975–1978, 3153–3157)

Functions of `b` regular at `b⋆`: finite sums, the point values `H_N(c(b),δ(b),d(b))` at a
point where the Shapovalov determinants do not vanish at `b⋆`, and the comparison of two
rational functions of `Δ` by their values.
-/

namespace Virasoro.P2

open Virasoro Polynomial

variable {b : ℂ}

theorem evToK_sum {ι : Type*} (s : Finset ι) {x : ι → RatFunc ℂ} {v : ι → ℂ}
    (h : ∀ i ∈ s, EvToK b (x i) (v i)) : EvToK b (∑ i ∈ s, x i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evToK_zero (K := ℂ) (b := b)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem evToK_uniq {x : RatFunc ℂ} {v w : ℂ} (hv : EvToK b x v) (hw : EvToK b x w) : v = w :=
  hv.2.symm.trans hw.2

theorem evToK_of_reg (y : regSubK ℂ b) : EvToK b (y : RatFunc ℂ) (evRegK ℂ b y) := ⟨y.2, rfl⟩

/-- `F_M(c(b),δ(b),d(b))` is regular at `b⋆` when `det G_M(c⋆,δ⋆) ≠ 0`, with the value
`F_M(c⋆,δ⋆,d⋆)`. -/
theorem evToK_Fval {c d z : RatFunc ℂ} {cv dv zv : ℂ} (hc : EvToK b c cv) (hd : EvToK b d dv)
    (hz : EvToK b z zv) (M : ℕ) (hdet : (gram cv zv M).det ≠ 0) :
    EvToK b (Fval c d z M) (Fval cv dv zv M) := by
  let cA : regSubK ℂ b := ⟨c, hc.1⟩
  let dA : regSubK ℂ b := ⟨d, hd.1⟩
  let zA : regSubK ℂ b := ⟨z, hz.1⟩
  have hcv : evRegK ℂ b cA = cv := evRegK_mk ℂ hc
  have hdv : evRegK ℂ b dA = dv := evRegK_mk ℂ hd
  have hzv : evRegK ℂ b zA = zv := evRegK_mk ℂ hz
  have n1 := evToK_of_reg (numR cA zA dA M)
  have d1 := evToK_of_reg (detR cA zA M)
  have e1 : ((numR cA zA dA M : regSubK ℂ b) : RatFunc ℂ) = numR c z d M :=
    map_numR (regSubK ℂ b).val.toRingHom cA zA dA M
  have e2 : ((detR cA zA M : regSubK ℂ b) : RatFunc ℂ) = detR c z M :=
    map_detR (regSubK ℂ b).val.toRingHom cA zA M
  rw [e1, map_numR, hcv, hdv, hzv] at n1
  rw [e2, map_detR, hcv, hzv] at d1
  rw [Fval_eq, Fval_eq]
  exact n1.div d1 hdet

theorem evToK_Hval {c d z : RatFunc ℂ} {cv dv zv : ℂ} (hc : EvToK b c cv) (hd : EvToK b d dv)
    (hz : EvToK b z zv) (N : ℕ) (hdet : ∀ M ≤ N, (gram cv zv M).det ≠ 0) :
    EvToK b (Hval c d z N) (Hval cv dv zv N) := by
  unfold Hval
  refine evToK_sum _ fun j _ => ?_
  exact (evToK_intCast (eta j)).mul (evToK_Fval hc hd hz _ (hdet _ (Nat.sub_le N j)))

/-- Two rational functions that are regular and take the same values outside a finite set are
equal. -/
theorem ratFunc_eq_of_evalAt {x y : RatFunc ℂ} (S : Finset ℂ)
    (h : ∀ z : ℂ, z ∉ S → RegAt z x ∧ RegAt z y ∧ evalAt z x = evalAt z y) : x = y := by
  have hpoly : x.num * y.denom - y.num * x.denom = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.Infinite.mono (s := (↑S : Set ℂ)ᶜ) ?_ S.finite_toSet.infinite_compl
    intro z hz
    obtain ⟨hx, hy, he⟩ := h z (by simpa using hz)
    simp only [evalAt, RatFunc.eval, Polynomial.eval₂_id] at he
    unfold RegAt at hx hy
    rw [div_eq_div_iff hx hy] at he
    show (x.num * y.denom - y.num * x.denom).IsRoot z
    rw [Polynomial.IsRoot, eval_sub, eval_mul, eval_mul, he]
    ring
  rw [← RatFunc.num_div_denom x, ← RatFunc.num_div_denom y,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x))
      (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero y)), ← map_mul, ← map_mul]
  congr 1
  linear_combination hpoly

end Virasoro.P2
