import Virasoro.Sphere.Statements.Sec3a
import Virasoro.Sphere.Proofs.Sec2HSeries
import Virasoro.Proofs.LargeWeight
import Virasoro.Proofs.GramDet
import Virasoro.Proofs.EvalLemmas
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The polynomial extension (sphere paper Lemma 3.2(iii), second half)

sphere/paper.tex l.499–503: with `H_N = P_N/det G_N`, `P_N ∈ ℚ[c,Δ,Δ_1,…,Δ_4]`, the vanishing of
`lim_{Δ→+∞} H_N` on the Zariski-dense real set `{c > 1, Δ_i ∈ ℝ}` forces every coefficient of
`Δ^d`, `d ≥ d_N`, in `P_N` to vanish identically.
-/

namespace Virasoro.Sphere

open Polynomial Filter Topology

/-- The parameter ring `ℚ[c,Δ₁,…,Δ₄]`. -/
abbrev PA : Type := MvPolynomial (Fin 5) ℚ

/-- The point `(c,Δ₁,…,Δ₄)`. -/
def pt5 (c : ℂ) (Δe : Fin 4 → ℂ) : Fin 5 → ℂ := ![c, Δe 0, Δe 1, Δe 2, Δe 3]

/-- Evaluation of the parameters at `(c,Δ₁,…,Δ₄)`. -/
noncomputable def ev5 (c : ℂ) (Δe : Fin 4 → ℂ) : PA →+* ℂ :=
  (MvPolynomial.aeval (pt5 c Δe)).toRingHom

/-- `ℚ[c,Δ,Δ₁,…,Δ₄] → ℚ[c,Δ₁,…,Δ₄][Δ]`. -/
noncomputable def tau : MvPolynomial (Fin 6) ℚ →+* PA[X] :=
  (MvPolynomial.aeval (![C (MvPolynomial.X 0), X, C (MvPolynomial.X 1), C (MvPolynomial.X 2),
    C (MvPolynomial.X 3), C (MvPolynomial.X 4)] : Fin 6 → PA[X])).toRingHom

theorem aeval_vec6 (c : ℂ) (Δe : Fin 4 → ℂ) (Q : MvPolynomial (Fin 6) ℚ) :
    MvPolynomial.aeval (vec6 c Δe) Q =
      algebraMap ℂ[X] (RatFunc ℂ) ((tau Q).map (ev5 c Δe)) := by
  have h : (MvPolynomial.aeval (vec6 c Δe) : MvPolynomial (Fin 6) ℚ →ₐ[ℚ] RatFunc ℂ).toRingHom =
      (algebraMap ℂ[X] (RatFunc ℂ)).comp ((mapRingHom (ev5 c Δe)).comp tau) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tau, ev5, eq_ratCast, map_ratCast]
    · intro i
      fin_cases i <;>
        simp [vec6, tau, ev5, pt5, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  exact DFunLike.congr_fun h Q

/-- `d_N = ∑_{|Y|=N} ℓ(Y)`, the degree of `det G_N` in `Δ`. -/
def dN (N : ℕ) : ℕ := ∑ Y : Nat.Partition N, Y.word.length

theorem det_natDegree_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ[X])
    (a : ι → ℕ) (h : ∀ i j, (M i j).natDegree ≤ a i) : M.det.natDegree ≤ ∑ i, a i := by
  rw [Matrix.det_apply']
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine natDegree_mul_le.trans ?_
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ[X]).natDegree = 0 := natDegree_intCast _
  rw [h1, zero_add]
  refine (natDegree_prod_le _ _).trans ?_
  rw [← Equiv.sum_comp σ a]
  exact Finset.sum_le_sum fun i _ => h (σ i) i

theorem gramPoly_det_natDegree (c : ℂ) (N : ℕ) : (gramPoly c N).det.natDegree = dN N := by
  refine le_antisymm (det_natDegree_le _ _ fun Y Y' => ?_)
    (le_natDegree_of_ne_zero (gramPoly_det_coeff_ne_zero c N))
  exact (natDegree_gramWord_le c Y.word Y'.word (word_pos Y)).trans (min_le_left _ _)

theorem gramPoly_det_degree (c : ℂ) (N : ℕ) : (gramPoly c N).det.degree = dN N := by
  rw [degree_eq_natDegree (gramPoly_det_ne_zero c N), gramPoly_det_natDegree]

theorem eventually_eval_ne_zero {D : ℂ[X]} (hD : D ≠ 0) :
    ∀ᶠ z in Bornology.cobounded ℂ, D.eval z ≠ 0 :=
  (tendsto_eval_div_of_degree_lt 0 D (by
    rw [degree_zero]; exact bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hD))).2

/-- If `P/D → 0` along a path going to infinity, then `deg P < deg D`. -/
theorem degree_lt_of_tendsto_zero (P D : ℂ[X]) (hD : D ≠ 0) (g : ℝ → ℂ)
    (hg : Tendsto g atTop (Bornology.cobounded ℂ))
    (h : Tendsto (fun t => P.eval (g t) / D.eval (g t)) atTop (𝓝 0)) : P.degree < D.degree := by
  by_contra hnot
  rw [not_lt] at hnot
  have hP : P ≠ 0 := by
    rintro rfl
    rw [degree_zero, le_bot_iff] at hnot
    exact degree_ne_bot.mpr hD hnot
  have hDp : D.natDegree ≤ P.natDegree := natDegree_le_natDegree hnot
  have h1 := (tendsto_eval_div_pow P P.natDegree le_rfl).comp hg
  have h2 := (tendsto_eval_div_pow D P.natDegree hDp).comp hg
  have h3 := h.mul h2
  rw [zero_mul] at h3
  have hev : ∀ᶠ t in atTop, D.eval (g t) ≠ 0 := hg.eventually (eventually_eval_ne_zero hD)
  have h4 : (fun t => P.eval (g t) / D.eval (g t) * (D.eval (g t) / g t ^ P.natDegree)) =ᶠ[atTop]
      ((fun z : ℂ => P.eval z / z ^ P.natDegree) ∘ g) := by
    filter_upwards [hev] with t ht
    simp only [Function.comp_apply]
    field_simp
  have h5 := tendsto_nhds_unique h1 (h3.congr' h4)
  exact leadingCoeff_ne_zero.mpr hP h5

theorem tendsto_sq_add (μ : ℝ) :
    Tendsto (fun lam : ℝ => (lam : ℂ) ^ 2 + (μ : ℂ) ^ 2) atTop (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have h1 : Tendsto (fun lam : ℝ => lam ^ 2 + μ ^ 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero)
  refine h1.congr fun lam => ?_
  have h2 : (lam : ℂ) ^ 2 + (μ : ℂ) ^ 2 = ((lam ^ 2 + μ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h2, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem evalAt_of_mul_eq {x : RatFunc ℂ} {P D : ℂ[X]}
    (h : x * algebraMap ℂ[X] (RatFunc ℂ) D = algebraMap ℂ[X] (RatFunc ℂ) P) {z : ℂ}
    (hz : D.eval z ≠ 0) : RatFunc.eval (RingHom.id ℂ) z x = P.eval z / D.eval z := by
  have hD : algebraMap ℂ[X] (RatFunc ℂ) D ≠ 0 := by
    intro h0
    have : D = 0 := (map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).mp h0
    rw [this, eval_zero] at hz
    exact hz rfl
  rw [eq_div_of_mul_eq hD h]
  exact evalAt_div z P hz

/-- Lemma 3.2(iii) from the polynomial form `H_N det G_N = P_N ∈ ℚ[c,Δ,Δ_i]`. -/
theorem largeDeltaAt_of_poly (N : ℕ) (Q : MvPolynomial (Fin 6) ℚ)
    (hQ : ∀ (c : ℂ) (Δe : Fin 4 → ℂ),
      Hsph c Δe N * algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det =
        MvPolynomial.aeval (vec6 c Δe) Q)
    (hyp : ∀ μ : ℝ, 0 < μ → ∀ Δe : Fin 4 → ℝ,
      Tendsto
        (fun lam : ℝ => RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
          (Hsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) N))
        atTop (𝓝 (if N = 0 then 1 else 0))) :
    LargeDeltaAt N := by
  have hmul : ∀ (c : ℂ) (Δe : Fin 4 → ℂ),
      Hsph c Δe N * algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det =
        algebraMap ℂ[X] (RatFunc ℂ) ((tau Q).map (ev5 c Δe)) := fun c Δe => by
    rw [hQ, aeval_vec6]
  -- the coefficients of `Δ^d`, `d ≥ d_N`, vanish identically
  have hclaim : 1 ≤ N → ∀ d, dN N ≤ d → (tau Q).coeff d = 0 := by
    intro hN d hd
    apply MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
    rw [map_zero]
    refine MvPolynomial.funext_set
      (fun i : Fin 5 => if i = 0 then Complex.ofReal '' Set.Ioi 1 else Set.range Complex.ofReal)
      (fun i => ?_) fun x hx => ?_
    · by_cases hi : i = 0
      · rw [if_pos hi]
        exact (Set.Ioi_infinite 1).image Complex.ofReal_injective.injOn
      · rw [if_neg hi]
        exact Set.infinite_range_of_injective Complex.ofReal_injective
    · rw [map_zero]
      obtain ⟨c0, hc0, hx0⟩ : ∃ c0 : ℝ, 1 < c0 ∧ (c0 : ℂ) = x 0 := by
        have h0 := hx 0 (Set.mem_univ _)
        dsimp only at h0
        rw [if_pos rfl] at h0
        obtain ⟨c0, hc0, h⟩ := h0
        exact ⟨c0, hc0, h⟩
      have hxi : ∀ i : Fin 4, ∃ r : ℝ, (r : ℂ) = x i.succ := by
        intro i
        have h0 := hx i.succ (Set.mem_univ _)
        dsimp only at h0
        rw [if_neg (Fin.succ_ne_zero i)] at h0
        exact h0
      choose Δr hΔr using hxi
      have hμ0 : 0 < (c0 - 1) / 24 := by linarith
      have hμ : 0 < Real.sqrt ((c0 - 1) / 24) := Real.sqrt_pos.mpr hμ0
      have hc : (1 + 24 * ((Real.sqrt ((c0 - 1) / 24) : ℝ) : ℂ) ^ 2) = x 0 := by
        rw [← hx0]
        have : (1 + 24 * Real.sqrt ((c0 - 1) / 24) ^ 2 : ℝ) = c0 := by
          rw [Real.sq_sqrt hμ0.le]; ring
        exact_mod_cast this
      have hpt : pt5 (x 0) (fun i => (Δr i : ℂ)) = x := by
        funext i
        fin_cases i
        · rfl
        · exact hΔr 0
        · exact hΔr 1
        · exact hΔr 2
        · exact hΔr 3
      have hcoef : MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) ((tau Q).coeff d)) =
          ((tau Q).map (ev5 (x 0) (fun i => (Δr i : ℂ)))).coeff d := by
        rw [coeff_map, ev5, hpt, MvPolynomial.eval_map]
        rfl
      rw [hcoef]
      have hD := gramPoly_det_ne_zero (x 0) N
      have hlim := hyp _ hμ Δr
      rw [if_neg (by omega), hc] at hlim
      have hdeg := degree_lt_of_tendsto_zero _ _ hD _ (tendsto_sq_add _) (hlim.congr' (by
        filter_upwards [(tendsto_sq_add (Real.sqrt ((c0 - 1) / 24))).eventually
          (eventually_eval_ne_zero hD)] with lam hlam
        exact evalAt_of_mul_eq (hmul (x 0) _) hlam))
      rw [gramPoly_det_degree] at hdeg
      exact (degree_lt_iff_coeff_zero _ _).mp hdeg d hd
  have hdegree : 1 ≤ N → ∀ (c : ℂ) (Δe : Fin 4 → ℂ),
      ((tau Q).map (ev5 c Δe)).degree < (gramPoly c N).det.degree := by
    intro hN c Δe
    rw [gramPoly_det_degree, degree_lt_iff_coeff_zero]
    intro d hd
    rw [coeff_map, hclaim hN d hd, map_zero]
  refine ⟨fun c Δe => ?_, Q, fun c Δe => ⟨_, (aeval_vec6 c Δe Q).symm, hmul c Δe, fun hN =>
    hdegree hN c Δe⟩⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [if_pos rfl]
    simp only [Hsph_zero]
    have : RatFunc.eval (RingHom.id ℂ) = fun (z : ℂ) (x : RatFunc ℂ) =>
        RatFunc.eval (RingHom.id ℂ) z x := rfl
    simp only [RatFunc.eval_one]
    exact tendsto_const_nhds
  · rw [if_neg (by omega)]
    have hD := gramPoly_det_ne_zero c N
    refine (tendsto_eval_div_of_degree_lt _ _ (hdegree hN c Δe)).1.congr' ?_
    filter_upwards [eventually_eval_ne_zero hD] with z hz
    exact (evalAt_of_mul_eq (hmul c Δe) hz).symm

end Virasoro.Sphere
