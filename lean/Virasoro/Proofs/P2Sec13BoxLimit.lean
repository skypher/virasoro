import Virasoro.Proofs.P2Sec13Limit

/-!
# Lemma 13.1: the limit of the box ratio (paper.tex l.3018–3023, 3031–3033)

`c_{R,S}(t;2k+1,2m+1)` is a rational function of `t` over `ℚ`.  By Proposition 12.1(i) its
reduced denominator does not vanish at `t₀ = -p'/p` and its value there is `Ω_{u,v}` of the
arrow.  As a function of `b` it is `n(b²)/d(b²)` for the reduced fraction `n/d`.
-/

namespace Virasoro.P2

open Virasoro Polynomial

theorem boxDenPoly_eval (R S : ℤ) (t : ℂ) :
    ((boxDenPoly R S).map (algebraMap ℚ ℂ)).eval t = boxDen R S t := by
  unfold boxDenPoly boxDen
  rw [Polynomial.map_prod, eval_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp

theorem boxNumPoly_eval (R S : ℤ) (k m : ℕ) (t : ℂ) :
    ((boxNumPoly R S k m).map (algebraMap ℚ ℂ)).eval t = boxNum R S k m t := by
  unfold boxNumPoly boxNum
  rw [Polynomial.map_prod, eval_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  simp

theorem boxDenPoly_ne_zero (R S : ℤ) : boxDenPoly R S ≠ 0 := by
  unfold boxDenPoly
  refine Finset.prod_ne_zero_iff.2 fun x hx => ?_
  have hx0 : x ≠ (0, 0) := Finset.ne_of_mem_erase hx
  intro h0
  have h1 := congrArg (fun q : ℚ[X] => q.coeff 1) h0
  have h2 := congrArg (fun q : ℚ[X] => q.coeff 0) h0
  simp only [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C_ne_zero one_ne_zero, add_zero,
    coeff_zero] at h1
  simp only [coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add, coeff_C_zero,
    coeff_zero] at h2
  exact hx0 (Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2))

theorem eval_map_ratCast (q : ℚ) (f : ℚ[X]) :
    (f.map (algebraMap ℚ ℂ)).eval (q : ℂ) = ((f.eval q : ℚ) : ℂ) := by
  rw [eval_map, ← eq_ratCast (algebraMap ℚ ℂ) q, eval₂_at_apply, eq_ratCast]

/-- `Stmt_sub_tau_box_limit` (l.3018–3023), from Proposition 12.1(i). -/
theorem sub_tau_box_limit : Stmt_sub_tau_box_limit := by
  classical
  intro p p' r s b hset k m hk hm ε j ε'
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  obtain ⟨-, hden, hval, -⟩ := (prop_bgg_cocycle p p' r s b hset k m hk hm).1 ε j ε'
  intro L
  set ρ : RatFunc ℚ := boxRatio L.1 L.2 k m with hρ
  set n : ℚ[X] := ρ.num with hn
  set dn : ℚ[X] := ρ.denom with hdn
  have hdn0 : dn ≠ 0 := RatFunc.denom_ne_zero ρ
  have hcross : n * boxDenPoly L.1 L.2 = boxNumPoly L.1 L.2 k m * dn := by
    apply IsFractionRing.injective ℚ[X] (RatFunc ℚ)
    have h1 : algebraMap ℚ[X] (RatFunc ℚ) n / algebraMap ℚ[X] (RatFunc ℚ) dn =
        algebraMap ℚ[X] (RatFunc ℚ) (boxNumPoly L.1 L.2 k m) /
          algebraMap ℚ[X] (RatFunc ℚ) (boxDenPoly L.1 L.2) := RatFunc.num_div_denom ρ
    rw [div_eq_div_iff (RatFunc.algebraMap_ne_zero hdn0)
      (RatFunc.algebraMap_ne_zero (boxDenPoly_ne_zero _ _))] at h1
    rw [map_mul, map_mul]
    exact h1
  set Nb : ℂ[X] := (n.map (algebraMap ℚ ℂ)).comp (X ^ 2) with hNb
  set Db : ℂ[X] := (dn.map (algebraMap ℚ ℂ)).comp (X ^ 2) with hDb
  have hNe : ∀ z : ℂ, Nb.eval z = (n.map (algebraMap ℚ ℂ)).eval (z ^ 2) := fun z => by
    rw [hNb, eval_comp, eval_pow, eval_X]
  have hDe : ∀ z : ℂ, Db.eval z = (dn.map (algebraMap ℚ ℂ)).eval (z ^ 2) := fun z => by
    rw [hDb, eval_comp, eval_pow, eval_X]
  have ht0 : b ^ 2 = ((-(p' : ℚ) / p : ℚ) : ℂ) := by
    rw [hb]
    push_cast
    rfl
  have hDb0 : Db.eval b ≠ 0 := by
    rw [hDe, ht0, eval_map_ratCast]
    exact_mod_cast hden
  have hDbne : Db ≠ 0 := fun h0 => hDb0 (by rw [h0, eval_zero])
  refine ⟨algebraMap ℂ[X] (RatFunc ℂ) Nb / algebraMap ℂ[X] (RatFunc ℂ) Db, Db.roots.toFinset,
    fun b' _ _ hS₀ => ?_, regAt_div b Nb hDb0, ?_⟩
  · have hD' : Db.eval b' ≠ 0 := fun h0 =>
      hS₀ (Multiset.mem_toFinset.2 ((mem_roots hDbne).2 h0))
    refine ⟨regAt_div b' Nb hD', ?_⟩
    rw [evalAt_div b' Nb hD', hNe, div_mul_eq_mul_div, div_eq_iff hD', hDe]
    have hc := congrArg (fun f : ℚ[X] => (f.map (algebraMap ℚ ℂ)).eval (b' ^ 2)) hcross
    simp only [Polynomial.map_mul, eval_mul, boxDenPoly_eval, boxNumPoly_eval] at hc
    exact hc
  · rw [evalAt_div b Nb hDb0, hNe, hDe, ht0, eval_map_ratCast, eval_map_ratCast]
    have h1 : RatFunc.eval (RingHom.id ℚ) (-(p' : ℚ) / p) ρ =
        n.eval (-(p' : ℚ) / p) / dn.eval (-(p' : ℚ) / p) := by
      simp only [RatFunc.eval, Polynomial.eval₂_id]
      rfl
    have h2 : (cArrow p p' r s k m ε j ε' : ℚ) = cMM p p' L.1 L.2 k m := rfl
    rw [h2, ← hval, h1]
    push_cast
    rfl

example : Stmt_sub_tau_box_limit := sub_tau_box_limit

end Virasoro.P2
