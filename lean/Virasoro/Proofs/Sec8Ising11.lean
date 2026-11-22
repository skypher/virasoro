import Virasoro.Proofs.Sec8IsingRows
import Virasoro.Proofs.Sec8Ising11PP
import Virasoro.Proofs.Sec5TopLayerFinal
import Virasoro.Proofs.Sec6Regular
import Virasoro.Proofs.SingularOnes
import Virasoro.Proofs.SingularPull
import Virasoro.Proofs.LevelComp

/-!
# Proposition 8.1 of `paper.tex` at 70bac53: the singular vector at level eleven

At `λ = 0` the singular vector that starts the second Jantzen layer has level `11 = 1 + 10`.
It is the image of the normalized singular vector of level `10` in `M(1/2,1)` under the
embedding defined by `L_{-1}|0⟩` (labels `(1,1)` and `(2,5)`), so its torus norm is
`𝒫_{1,1}(b₀,d) 𝒫_{2,5}(b₀,d)` by Lemma 5.5 and Lemma 6.6.  Equation (5.1) at a level with a
single summand gives the coefficient `τ/γ` (`top_two_single`).
-/

namespace Virasoro

open Verma Module Polynomial

theorem negSpan_smul {c h : ℂ} (χ : Verma ℂ c h) {e : ℂ} (he : e ≠ 0) :
    negSpan (e • χ) = negSpan χ := by
  have hc : ∀ w : List ℕ+, VirEnv.negOp c (w.map (↑)) • (e • χ) =
      e • (VirEnv.negOp c (w.map (↑)) • χ) :=
    fun w => (smul_comm e (VirEnv.negOp c (w.map (↑))) χ).symm
  unfold negSpan
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨w, rfl⟩
    have hm : e • (VirEnv.negOp c (w.map (↑)) • χ) ∈ Submodule.span ℂ
        (Set.range fun w : List ℕ+ => VirEnv.negOp c (w.map (↑)) • χ) :=
      Submodule.smul_mem _ e (Submodule.subset_span ⟨w, rfl⟩)
    rw [← hc w] at hm
    exact hm
  · rintro _ ⟨w, rfl⟩
    have hm : e⁻¹ • (VirEnv.negOp c (w.map (↑)) • (e • χ)) ∈ Submodule.span ℂ
        (Set.range fun w : List ℕ+ => VirEnv.negOp c (w.map (↑)) • (e • χ)) :=
      Submodule.smul_mem _ e⁻¹ (Submodule.subset_span ⟨w, rfl⟩)
    have h1 : e⁻¹ • (VirEnv.negOp c (w.map (↑)) • (e • χ)) =
        VirEnv.negOp c (w.map (↑)) • χ := by
      rw [hc w]
      exact inv_smul_smul₀ he (VirEnv.negOp c (w.map (↑)) • χ)
    rw [h1] at hm
    exact hm

/-- The image of a singular vector `ψ = ∑ q_Y L_{-Y}|h'⟩`, `h' = h + ℓ`, under the embedding
defined by a singular vector `χ` of level `ℓ` in `M(c,h)`: it is singular of level `ℓ + m`
and its torus norm is the product of the two torus norms (Lemma 5.5). -/
theorem composite_data (hI : Cited_VermaHomInjective) {c h : ℂ} {ℓ m : ℕ}
    (p : Nat.Partition ℓ → ℂ) (q : Nat.Partition m → ℂ) (h' : ℂ) (hh' : h' = h + (ℓ : ℂ))
    (hp : IsSingular (pbwCoord (c := c) (h := h) ℓ p) ℓ)
    (hq : IsSingular (pbwCoord (c := c) (h := h') m q) m) :
    ∃ x : Nat.Partition (ℓ + m) → ℂ,
      IsSingular (pbwCoord (c := c) (h := h) (ℓ + m) x) (ℓ + m) ∧
      ∀ d : ℂ, torusForm c h d (ℓ + m) x x = torusForm c h d ℓ p p * torusForm c h' d m q q := by
  subst hh'
  obtain ⟨j, hjhw, hjL, hjneg⟩ := exists_singularHom hp.2.1 hp.2.2
  have hj0 : j ≠ 0 := by
    intro h0
    apply hp.1
    rw [← hjhw, h0]
    rfl
  have hinj := hI c h (h + (ℓ : ℂ)) j hjL hj0
  have hs := isSingular_map rfl j hinj hjL hq
  obtain ⟨x, hx⟩ := mem_level_of_L_zero hs.2.1
  have hjψ : j (pbwCoord m q) = coordOp c q • pbwCoord (c := c) (h := h) ℓ p := by
    rw [pbwCoord_apply, map_sum]
    unfold coordOp
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [map_smul, hjneg, smul_assoc]
  refine ⟨x, by rw [hx]; exact hs, fun d => ?_⟩
  have hT := isPrimaryPairing_pairing (c := c) (h := h) d
  rw [← primary_pbwCoord hT (ℓ + m), hx, hjψ, pairing_coordOp c h d hp q, primary_pbwCoord hT ℓ]

/-- A singular vector whose torus norm is a monic polynomial can be normalized, without
changing the torus norm (Lemma 5.7: the leading coefficient is the square of the coefficient
of `L_{-1}^N`). -/
theorem normalize_singular {c h : ℂ} {N : ℕ} (hN : 1 ≤ N) (x : Nat.Partition N → ℂ)
    (hs : IsSingular (pbwCoord (c := c) (h := h) N x) N) {Q : ℂ[X]} (hQ : Q.Monic)
    (htor : ∀ d : ℂ, torusForm c h d N x x = Q.eval d) :
    ∃ x' : Nat.Partition N → ℂ, x' (onesPartition N) = 1 ∧
      IsSingular (pbwCoord (c := c) (h := h) N x') N ∧
      ∀ d : ℂ, torusForm c h d N x' x' = Q.eval d := by
  obtain ⟨ha, -, hlead⟩ := lem_singular_degree c h N hN x hs
  have hpoly : torusPolyForm c h x = Q := torusForm_poly_eq htor
  rw [hpoly, hQ.leadingCoeff] at hlead
  have hinv : (x (onesPartition N))⁻¹ * (x (onesPartition N))⁻¹ = 1 := by
    rw [← mul_inv, ← sq, ← hlead, inv_one]
  refine ⟨(x (onesPartition N))⁻¹ • x, ?_, ?_, fun d => ?_⟩
  · rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ ha]
  · rw [map_smul]
    exact isSingular_smul hs (inv_ne_zero ha)
  · have hT := isPrimaryPairing_pairing (c := c) (h := h) d
    rw [← primary_pbwCoord hT N]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [primary_pbwCoord hT N, htor d, ← mul_assoc, hinv, one_mul]

theorem genPpoly_monic (r s : ℕ) (b : ℂ) : (genPpoly r s b).Monic := by
  unfold genPpoly
  refine monic_prod_of_monic _ _ fun k _ => monic_prod_of_monic _ _ fun l _ => ?_
  have e : ∀ a a' : ℂ, (C a - X) * (C a' - X) = (X - C a) * (X - C a') := fun a a' => by ring
  rw [e]
  exact (monic_X_sub_C _).mul (monic_X_sub_C _)

set_option maxHeartbeats 1600000 in
/-- Equation (5.1) at the level `N = ℓ⁻₂ < ℓ⁺₂`, where it has the single term `τ/γ`, for an
arbitrary singular vector of level `N` (singular vectors of a given level are proportional). -/
theorem top_two_single (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique)
    {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    (wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)) (hsetting : TopLayerSetting p p' r s b wp wm)
    {N : ℕ} (hN : ellMinus p p' r s 2 = N) (hlt : N < ellPlus p p' r s 2)
    (hN3 : N < ellMin p p' r s 3) (x : Nat.Partition N → ℂ)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) N x) N) :
    ppCoeff (HN (kacC b) N) (pt (kacH r s b)) 2 =
      algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) x) *
        RatFunc.C (jform (kacC b) (kacH r s b) N 2 x x)⁻¹ := by
  subst hN
  obtain ⟨hsg, hjan⟩ := hsetting
  obtain ⟨e, he⟩ := hU _ _ _ _ _ (hsg 2 (by norm_num)).2 hx
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hx.1 (by rw [he]; exact zero_smul ℂ (wm 2))
  have hsetting' : TopLayerSetting p p' r s b wp
      (Function.update wm 2 (pbwCoord (ellMinus p p' r s 2) x)) := by
    refine ⟨fun k hk => ⟨(hsg k hk).1, ?_⟩, fun i hi => ?_⟩
    · by_cases hk2 : k = 2
      · subst hk2
        rw [Function.update_self]
        exact hx
      · rw [Function.update_of_ne hk2]
        exact (hsg k hk).2
    · by_cases hi2 : i = 2
      · subst hi2
        rw [Function.update_self, hjan 2 hi, he, negSpan_smul _ he0]
      · rw [Function.update_of_ne hi2]
        exact hjan i hi
  obtain ⟨-, -, -, hpp⟩ := thm_top_layer_of_cited hI p p' r s b hset wp _ hsetting' 2
    (ellMinus p p' r s 2) (by norm_num) (Nat.min_le_right _ _) hN3
  obtain ⟨xp, hxp⟩ := mem_level_of_L_zero (hsg 2 (by norm_num)).1.2.1
  have h := (hpp xp x hxp (by rw [Function.update_self])).2
  unfold topTerm at h
  rw [if_neg (not_le.2 hlt), if_pos le_rfl, zero_add, Nat.sub_self, HN_zero, RatFunc.eval_one,
    mul_one] at h
  exact h

set_option maxRecDepth 100000 in
/-- The normalized singular vector of level `11` in `M(1/2,0)` with torus norm
`𝒫_{1,1}(b₀,d) 𝒫_{2,5}(b₀,d)`. -/
theorem exists_vec_eleven (hI : Cited_VermaHomInjective) (hH : Cited_HJSNormalizations) :
    ∃ x : Nat.Partition 11 → ℂ, x (onesPartition 11) = 1 ∧
      IsSingular (pbwCoord (c := kacC b0) (h := kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0) 11 x) 11 ∧
      ∀ d : ℂ, torusForm (kacC b0) (kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0) d 11 x x =
        (genPpoly 1 1 b0 * genPpoly 2 5 b0).eval d := by
  have hreg := lem_regular_everywhere_of_cited hH
  obtain ⟨p11, ⟨h1a, h1b⟩, -⟩ := normalization_at hH 1 1 (by norm_num) (by norm_num)
  obtain ⟨p25, ⟨h2a, h2b⟩, -⟩ := normalization_at hH 2 5 (by norm_num) (by norm_num)
  have r11 := (hreg 1 1 (by norm_num) (by norm_num) p11 h1a h1b b0 b0_ne_zero).2
  have r25 := (hreg 2 5 (by norm_num) (by norm_num) p25 h2a h2b b0 b0_ne_zero).2
  dsimp only at r11 r25
  obtain ⟨-, hs11, ht11, -⟩ := r11
  obtain ⟨-, hs25, ht25, -⟩ := r25
  have hh : kacH ((2 : ℕ) : ℤ) ((5 : ℕ) : ℤ) b0 =
      kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 + ((1 * 1 : ℕ) : ℂ) := by
    have a := kacHL_b0_cast (2, 5)
    have a' := kacHL_b0_cast (1, 1)
    rw [kacHL] at a a'
    rw [a, a']
    norm_num [isingDelta]
  obtain ⟨x, hxs, hxt⟩ := composite_data hI _ _ _ hh hs11 hs25
  have hQ := (genPpoly_monic 1 1 b0).mul (genPpoly_monic 2 5 b0)
  obtain ⟨x', h1, hs', ht'⟩ := normalize_singular (by norm_num) x hxs hQ
    (fun d => by rw [hxt d, ht11 d, ht25 d, eval_mul, genPpoly_eval, genPpoly_eval])
  exact ⟨x', h1, hs', ht'⟩

end Virasoro
