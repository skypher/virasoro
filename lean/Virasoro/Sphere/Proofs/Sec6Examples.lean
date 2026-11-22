import Virasoro.Sphere.Proofs.Sec5TopLayerH
import Virasoro.Sphere.Proofs.Sec5PiFactorization
import Virasoro.Sphere.Proofs.Sec5PoleBound
import Virasoro.Sphere.Proofs.Sec4Imported
import Virasoro.Proofs.Sec8IsingTop
import Virasoro.Proofs.Sec6TTLabel
import Virasoro.Proofs.P2Sec11LayerIndep
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Propositions 6.1 and 6.2 of the sphere paper: the first double poles (sphere/paper.tex
l.1793–1851)

"At `N = ℓ₂`, Theorem 5.3 has the single term `M = 0` (`H₀ = ℬ₀ = 1`), with `π` given by
Lemma 5.2(ii) at `j = 1` and the same second Jantzen norm `γ = B²(w^small_2, w^small_2)` as on
the torus."  Here: the transfer of Lemma 5.2(ii) from complex weights to the indeterminate
external weights of `ℂ(Δ₁,…,Δ₄)` (both sides are polynomials in the weights), and the
normalization `w^small_2 = a·w̃`.
-/

namespace Virasoro.Sphere

open Finset

section Transfer

/-- `P_{r,s}(b;Δ_a,Δ_b)` with complex `b`, over a commutative `ℂ`-algebra. -/
noncomputable def fusPC (r s : ℕ) (b : ℂ) {A : Type*} [CommRing A] [Algebra ℂ A] (Δa Δb : A) : A :=
  (if (0 : ℤ) ∈ stepRange r ∧ (0 : ℤ) ∈ stepRange s then
      (algebraMap ℂ A ((b + b⁻¹) ^ 2) - 4 * Δa - (algebraMap ℂ A ((b + b⁻¹) ^ 2) - 4 * Δb)) *
        algebraMap ℂ A (1 / 4)
    else 1) *
    ∏ x ∈ (stepRange r ×ˢ stepRange s).filter fun x : ℤ × ℤ => 0 < x.1 ∨ (x.1 = 0 ∧ 0 < x.2),
      ((algebraMap ℂ A ((b + b⁻¹) ^ 2) - 4 * Δa - (algebraMap ℂ A ((b + b⁻¹) ^ 2) - 4 * Δb) +
          algebraMap ℂ A (((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) ^ 2)) ^ 2
        - 4 * (algebraMap ℂ A ((b + b⁻¹) ^ 2) - 4 * Δa) *
          algebraMap ℂ A (((x.1 : ℂ) * b + (x.2 : ℂ) * b⁻¹) ^ 2)) * algebraMap ℂ A (1 / 16)

theorem fusP_eq_fusPC {𝔽 : Type*} [Field 𝔽] [Algebra ℂ 𝔽] (r s : ℕ) (b : ℂ) (Δa Δb : 𝔽) :
    fusP r s (algebraMap ℂ 𝔽 b) Δa Δb = fusPC r s b Δa Δb := by
  unfold fusP fusPC
  simp only [map_mul, map_add, map_pow, map_inv₀, map_intCast, map_div₀, map_one, map_ofNat]
  congr 1
  · split_ifs <;> ring
  · refine prod_congr rfl fun x _ => ?_
    ring

theorem map_fusPC {A A' : Type*} [CommRing A] [Algebra ℂ A] [CommRing A'] [Algebra ℂ A']
    (f : A →ₐ[ℂ] A') (r s : ℕ) (b : ℂ) (Δa Δb : A) :
    f (fusPC r s b Δa Δb) = fusPC r s b (f Δa) (f Δb) := by
  unfold fusPC
  simp only [map_mul, map_sub, map_add, map_pow, map_prod, AlgHom.commutes, apply_ite f, map_one,
    map_ofNat]

/-- `π(Δ_i, Δ_j)` as a polynomial in the external weights. -/
noncomputable def piR (lam : ℂ) {ℓ : ℕ} (x : Nat.Partition ℓ → ℂ) (i j : Fin 4) :
    MvPolynomial (Fin 4) ℂ :=
  ∑ Y, MvPolynomial.C (x Y) *
    gammaY (MvPolynomial.C lam) (MvPolynomial.X i) (MvPolynomial.X j) Y.word

theorem piScalar_K4 (lam : ℂ) {ℓ : ℕ} (x : Nat.Partition ℓ → ℂ) (i j : Fin 4) :
    piScalar lam x (ΔK i) (ΔK j) = algebraMap (MvPolynomial (Fin 4) ℂ) K4 (piR lam x i j) := by
  unfold piScalar piR
  rw [map_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [map_mul, map_gammaY]
  simp only [ΔK, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rfl

theorem eval_piR (lam : ℂ) {ℓ : ℕ} (x : Nat.Partition ℓ → ℂ) (i j : Fin 4) (v : Fin 4 → ℂ) :
    MvPolynomial.eval v (piR lam x i j) = piScalar lam x (v i) (v j) := by
  unfold piR piScalar
  rw [map_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [map_mul, map_gammaY, MvPolynomial.eval_C, MvPolynomial.eval_C, MvPolynomial.eval_X,
    MvPolynomial.eval_X]
  rfl

theorem fusK4 (r s : ℕ) (b : ℂ) (i j : Fin 4) :
    fusP r s (cK b) (ΔK i) (ΔK j) = algebraMap (MvPolynomial (Fin 4) ℂ) K4
      (fusPC r s b (MvPolynomial.X i) (MvPolynomial.X j)) := by
  rw [fusP_eq_fusPC]
  have h := map_fusPC (IsScalarTower.toAlgHom ℂ (MvPolynomial (Fin 4) ℂ) K4) r s b
    (MvPolynomial.X i) (MvPolynomial.X j)
  simp only [IsScalarTower.coe_toAlgHom'] at h
  rw [h]
  rfl

theorem eval_fusPC (r s : ℕ) (b : ℂ) (i j : Fin 4) (v : Fin 4 → ℂ) :
    MvPolynomial.eval v (fusPC r s b (MvPolynomial.X i) (MvPolynomial.X j)) =
      fusP r s b (v i) (v j) := by
  calc MvPolynomial.eval v (fusPC r s b (MvPolynomial.X i) (MvPolynomial.X j))
      = MvPolynomial.aeval v (fusPC r s b (MvPolynomial.X i) (MvPolynomial.X j)) := rfl
    _ = fusPC r s b (v i) (v j) := by
      rw [map_fusPC, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    _ = fusP r s b (v i) (v j) := by
      rw [← fusP_eq_fusPC]
      rfl

/-- Lemma 5.2(ii) at indeterminate external weights. -/
theorem pi_K4_of {lam b : ℂ} {ℓ : ℕ} {x : Nat.Partition ℓ → ℂ} {R₁ S₁ R₂ S₂ : ℕ}
    (h : ∀ Δa Δb : ℂ, piScalar lam x Δa Δb = fusP R₁ S₁ b Δa Δb * fusP R₂ S₂ b Δa Δb)
    (i j : Fin 4) :
    piScalar lam x (ΔK i) (ΔK j) =
      fusP R₁ S₁ (cK b) (ΔK i) (ΔK j) * fusP R₂ S₂ (cK b) (ΔK i) (ΔK j) := by
  rw [piScalar_K4, fusK4, fusK4, ← map_mul]
  congr 1
  apply MvPolynomial.funext
  intro v
  rw [eval_piR, map_mul, eval_fusPC, eval_fusPC, h]

theorem piScalar_K4_ne {lam : ℂ} {ℓ : ℕ} {x : Nat.Partition ℓ → ℂ} {i j : Fin 4} (hij : i ≠ j)
    {α β : ℂ} (h : piScalar lam x α β ≠ 0) : piScalar lam x (ΔK i) (ΔK j) ≠ 0 := by
  rw [piScalar_K4]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Fin 4) ℂ) K4)).2 ?_
  intro h0
  apply h
  have := congrArg (MvPolynomial.eval fun k => if k = i then α else if k = j then β else 0) h0
  rw [eval_piR, map_zero] at this
  simpa [if_neg hij.symm] using this

end Transfer

section Normalize

variable {c lam : ℂ} {ℓ k : ℕ}

theorem piScalar_smul {𝔽 : Type*} [Field 𝔽] [Algebra ℂ 𝔽] (a : ℂ) (x : Nat.Partition ℓ → ℂ)
    (Δa Δb : 𝔽) : piScalar lam (a • x) Δa Δb = algebraMap ℂ 𝔽 a * piScalar lam x Δa Δb := by
  unfold piScalar
  rw [mul_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem mem_layer_of_jform_ne {x : Nat.Partition ℓ → ℂ} (h : jform c lam ℓ k x x ≠ 0) :
    x ∈ jantzenLayer c lam ℓ k := by
  unfold jform at h
  split_ifs at h with hu
  · obtain ⟨w, hw⟩ := hu
    exact ⟨w, hw.1, hw.2⟩
  · exact absurd rfl h

theorem jform_smul_smul (a : ℂ) {x : Nat.Partition ℓ → ℂ} (hx : x ∈ jantzenLayer c lam ℓ k) :
    jform c lam ℓ k (a • x) (a • x) = a ^ 2 * jform c lam ℓ k x x := by
  have hax : a • x ∈ jantzenLayer c lam ℓ k := Submodule.smul_mem _ a hx
  rw [jform_smul_left' a hx hax, jform_symm c lam hx hax, jform_smul_left' a hx hx]
  ring

end Normalize

section FirstDouble

variable {p p' r s : ℕ}

theorem topTermSph_self (f : ℕ → RatFunc K4) (hf0 : f 0 = 1) (c lam : ℂ) (ℓ k : ℕ)
    (x : Nat.Partition ℓ → ℂ) :
    topTermSph f c lam ℓ ℓ k x =
      piScalar lam x (ΔK 3) (ΔK 2) * piScalar lam x (ΔK 0) (ΔK 1) * cK (jform c lam ℓ k x x)⁻¹ := by
  unfold topTermSph
  rw [if_pos le_rfl, Nat.sub_self, hf0, RatFunc.eval_one, mul_one]

theorem topTermSph_big (f : ℕ → RatFunc K4) (c lam : ℂ) {N ℓ : ℕ} (k : ℕ) (hℓ : N < ℓ)
    (x : Nat.Partition ℓ → ℂ) : topTermSph f c lam N ℓ k x = 0 := by
  unfold topTermSph
  rw [if_neg (by omega)]

theorem jDepth_le_one (hp : 2 ≤ p) (hp' : 2 ≤ p') (hr : 0 < r) (hrp : r < p) (hs : 0 < s)
    (hsp : s < p') {M : ℕ} (hM : M < ellMin p p' r s 2) : jDepth p p' r s M ≤ 1 := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, -⟩ := jDepth_range hp hp' hr hrp hs hsp (by omega : 1 ≤ jDepth p p' r s M)
  have h2 : ellMin p p' r s 2 ≤ ellMin p p' r s (jDepth p p' r s M) := by
    rcases Nat.lt_or_ge 2 (jDepth p p' r s M) with h3 | h3
    · obtain ⟨j, hj⟩ : ∃ j, jDepth p p' r s M = 2 + j := ⟨jDepth p p' r s M - 2, by omega⟩
      rw [hj]
      have hjp := ellOrb_lt_add (show 0 < p by omega) (show 0 < p' by omega) hr hrp hs hsp true 2 j
        (by omega)
      have e1 := hjp true
      have e2 := hjp false
      rw [TT.ellOrb_true (by norm_num), TT.ellOrb_true (by omega)] at e1
      rw [TT.ellOrb_true (by norm_num), TT.ellOrb_false (by omega)] at e2
      unfold ellMin
      omega
    · have : jDepth p p' r s M = 2 := by omega
      rw [this]
  omega

/-- The value of the leading coefficient for the singular vector of the small sign at level
`ℓ^ε_2` (sphere/paper.tex l.1836–1840): Lemma 5.2(ii) at `j = 1` and the second Jantzen norm. -/
theorem small_value (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool) {n : ℕ}
    (hn : ellOrb p p' r s ε 2 = n) {x : Nat.Partition n → ℂ}
    (hxs : Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b) n x) n)
    (hj : jform (kacC b) (kacH r s b) n 2 x x ≠ 0) {γ : ℂ}
    (hγ : ∀ xt : Nat.Partition n → ℂ, xt (onesPartition n) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b) n xt) n →
        jform (kacC b) (kacH r s b) n 2 xt xt = γ) :
    piScalar (kacH r s b) x (ΔK 3) (ΔK 2) * piScalar (kacH r s b) x (ΔK 0) (ΔK 1) *
        cK (jform (kacC b) (kacH r s b) n 2 x x)⁻¹ =
      exampleCoeff b r s (if ε then r + p else p - r) (if ε then p' - s else p' + s) γ ∧
    exampleCoeff b r s (if ε then r + p else p - r) (if ε then p' - s else p' + s) γ ≠ 0 := by
  subst hn
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  have hlev := TT.ellOrb_pos hp hp' hr hrp hs hsp ε (show 1 ≤ 2 by norm_num)
  have ha := sub_singular_ones_coeff _ _ _ hlev x hxs
  set a := x (onesPartition _) with ha_def
  set xt := a⁻¹ • x with hxt_def
  clear_value xt
  have hx : x = a • xt := by rw [hxt_def, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have hxt1 : xt (onesPartition _) = 1 := by
    rw [hxt_def, Pi.smul_apply, smul_eq_mul, ← ha_def, inv_mul_cancel₀ ha]
  have hxts : Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b)
      (ellOrb p p' r s ε 2) xt) (ellOrb p p' r s ε 2) := by
    rw [hxt_def, map_smul]
    exact isSingular_smul hxs (inv_ne_zero ha)
  have hmem : xt ∈ jantzenLayer (kacC b) (kacH r s b) (ellOrb p p' r s ε 2) 2 := by
    rw [hxt_def]; exact Submodule.smul_mem _ a⁻¹ (mem_layer_of_jform_ne hj)
  have hγ' := hγ xt hxt1 hxts
  have hj' : jform (kacC b) (kacH r s b) (ellOrb p p' r s ε 2) 2 x x = a ^ 2 * γ := by
    rw [hx, jform_smul_smul a hmem, hγ']
  have hγ0 : γ ≠ 0 := by
    intro h0; apply hj; rw [hj', h0, mul_zero]
  -- Lemma 5.2(ii) at `j = 1`
  obtain ⟨-, hpi2, hpi3⟩ := lem_pi_factorization_of_cited hH hF hU p p' r s b hset 2 ε
    (by norm_num) xt hxt1 hxts
  have hfac : ∀ Δa Δb : ℂ, piScalar (kacH r s b) xt Δa Δb =
      fusP r s b Δa Δb * fusP (if ε then r + p else p - r) (if ε then p' - s else p' + s) b Δa Δb := by
    intro Δa Δb
    rw [hpi2 (by norm_num) Δa Δb]
    cases ε <;> simp
  have hK32 := pi_K4_of hfac 3 2
  have hK01 := pi_K4_of hfac 0 1
  -- nonvanishing (Lemma 5.2(iii) at `(a, b) = (1/2, 0)`)
  have hne : ∀ {i j : Fin 4}, i ≠ j → piScalar (kacH r s b) xt (ΔK i) (ΔK j) ≠ 0 := by
    intro i j hij
    refine piScalar_K4_ne hij (α := (((1 / 2 : ℂ)) ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p'))
      (β := (((0 : ℂ)) ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')) ?_
    intro h0
    obtain ⟨c₀, -, hc⟩ := (hpi3 (1 / 2) 0).1 h0
    have hc' : (c₀ : ℂ) = 1 / 2 := by rcases hc with hc | hc <;> rw [← hc] <;> ring
    have hq : ((c₀ : ℚ) : ℂ) = ((1 / 2 : ℚ) : ℂ) := by push_cast; exact hc'
    have hq' : (c₀ : ℚ) = 1 / 2 := by exact_mod_cast hq
    have h2 : (2 * c₀ : ℚ) = 1 := by rw [hq']; norm_num
    have h3 : (2 * c₀ : ℤ) = 1 := by exact_mod_cast h2
    omega
  refine ⟨?_, ?_⟩
  · rw [hj', hx, piScalar_smul, piScalar_smul, hK32, hK01, exampleCoeff]
    have hcK : cK a ≠ 0 := (map_ne_zero _).2 ha
    have hcγ : cK γ ≠ 0 := (map_ne_zero _).2 hγ0
    simp only [map_inv₀, map_mul, map_pow]
    field_simp
  · have e : exampleCoeff b r s (if ε then r + p else p - r) (if ε then p' - s else p' + s) γ =
        piScalar (kacH r s b) xt (ΔK 3) (ΔK 2) * piScalar (kacH r s b) xt (ΔK 0) (ΔK 1) /
          cK γ := by
      rw [exampleCoeff, hK32, hK01]; ring
    rw [e]
    exact div_ne_zero (mul_ne_zero (hne (by decide)) (hne (by decide)))
      ((map_ne_zero _).2 hγ0)

/-- `FirstDoublePole` from the top-layer data at `N = ℓ` (sphere/paper.tex l.1834–1840). -/
theorem fdp_of {c lam : ℂ} {N : ℕ} {coef : K4}
    (hlow : ∀ M : ℕ, M < N → poleOrder (Bsph (cK c) ΔK M) (cK lam) ≤ 1 ∧
      poleOrder (Hsph (cK c) ΔK M) (cK lam) ≤ 1)
    (hBle : poleOrder (Bsph (cK c) ΔK N) (cK lam) ≤ 2)
    (hBc : ppCoeff (Bsph (cK c) ΔK N) (cK lam) 2 = coef)
    (hHle : poleOrder (Hsph (cK c) ΔK N) (cK lam) ≤ 2)
    (hHc : ppCoeff (Hsph (cK c) ΔK N) (cK lam) 2 = coef) (hne : coef ≠ 0) :
    FirstDoublePole c lam N coef :=
  ⟨hlow, poleOrder_eq_of_ppCoeff_ne hBle (by rw [hBc]; exact hne),
    poleOrder_eq_of_ppCoeff_ne hHle (by rw [hHc]; exact hne), hBc, hHc⟩

/-- The common top-layer data at level two. -/
theorem top_two (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective) {b : ℂ}
    (hset : MinimalSetting p p' r s b) {N : ℕ} (hmin2 : ellMin p p' r s 2 = N)
    (hN3 : N < ellMin p p' r s 3) :
    ∃ (xp : Nat.Partition (ellPlus p p' r s 2) → ℂ) (xm : Nat.Partition (ellMinus p p' r s 2) → ℂ),
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b) _ xp) (ellPlus p p' r s 2) ∧
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b) _ xm) (ellMinus p p' r s 2) ∧
      (ellPlus p p' r s 2 ≤ N → jform (kacC b) (kacH r s b) (ellPlus p p' r s 2) 2 xp xp ≠ 0) ∧
      (ellMinus p p' r s 2 ≤ N → jform (kacC b) (kacH r s b) (ellMinus p p' r s 2) 2 xm xm ≠ 0) ∧
      (poleOrder (Bsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) ≤ 2 ∧
        ppCoeff (Bsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) 2 =
          topTermSph (Bsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N (ellPlus p p' r s 2) 2 xp +
            topTermSph (Bsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N (ellMinus p p' r s 2) 2 xm) ∧
      (poleOrder (Hsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) ≤ 2 ∧
        ppCoeff (Hsph (cK (kacC b)) ΔK N) (cK (kacH r s b)) 2 =
          topTermSph (Hsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N (ellPlus p p' r s 2) 2 xp +
            topTermSph (Hsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N (ellMinus p p' r s 2) 2 xm) ∧
      (∀ M : ℕ, M < N → poleOrder (Bsph (cK (kacC b)) ΔK M) (cK (kacH r s b)) ≤ 1 ∧
        poleOrder (Hsph (cK (kacC b)) ΔK M) (cK (kacH r s b)) ≤ 1) := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  obtain ⟨wp, wm, hsing, hjan, -, -⟩ :=
    thm_jantzen_smith hJ p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hT : TopLayerSetting p p' r s b wp wm := ⟨hsing, hjan⟩
  have top := thm_top_layer_of_cited hI p p' r s b hset wp wm hT 2 N (by norm_num) hmin2.le hN3
  have hcp : Verma.pbwCoord (ellPlus p p' r s 2) (Verma.comp (ellPlus p p' r s 2) (wp 2)) = wp 2 :=
    Verma.pbwCoord_comp_of_mem_level (Verma.mem_level_of_L_zero (hsing 2 (by norm_num)).1.2.1)
  have hcm : Verma.pbwCoord (ellMinus p p' r s 2) (Verma.comp (ellMinus p p' r s 2) (wm 2)) =
      wm 2 :=
    Verma.pbwCoord_comp_of_mem_level (Verma.mem_level_of_L_zero (hsing 2 (by norm_num)).2.2.1)
  obtain ⟨hB, hHH⟩ := top.2.2.2 _ _ hcp hcm
  refine ⟨_, _, by rw [hcp]; exact (hsing 2 (by norm_num)).1, by rw [hcm]; exact
    (hsing 2 (by norm_num)).2, fun h => (top.2.1 _ hcp h).1, fun h => (top.2.2.1 _ hcm h).1, hB, hHH,
    fun M hM => ?_⟩
  have hj := jDepth_le_one hp hp' hr hrp hs hsp (hmin2 ▸ hM)
  obtain ⟨h1, h2⟩ := thm_jantzen_bound_of_cited hJ p p' r s b hset M
  exact ⟨h1.trans hj, h2.trans hj⟩

theorem ellMin3 {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool) :
    ellOrb p p' r s ε 2 < ellMin p p' r s 3 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  have h := ellOrb_lt_succ (show 0 < p by omega) (show 0 < p' by omega) hr hrp hs hsp ε 2
  have h1 : ellOrb p p' r s ε 2 < ellPlus p p' r s 3 := by
    have := h true
    rwa [TT.ellOrb_true (by norm_num)] at this
  have h2 : ellOrb p p' r s ε 2 < ellMinus p p' r s 3 := by
    have := h false
    rwa [TT.ellOrb_false (by norm_num)] at this
  unfold ellMin
  omega

/-- The first double pole at `N = ℓ⁻_2 = ℓ₂` (sphere/paper.tex l.1834–1840). -/
theorem fdp_minus (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial) (hU : Cited_SingularUnique)
    {b : ℂ} (hset : MinimalSetting p p' r s b)
    (hsmall : ellMinus p p' r s 2 < ellPlus p p' r s 2) {γ : ℂ}
    (hγ : ∀ xt : Nat.Partition (ellMinus p p' r s 2) → ℂ, xt (onesPartition _) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b) (ellMinus p p' r s 2) xt)
        (ellMinus p p' r s 2) →
        jform (kacC b) (kacH r s b) (ellMinus p p' r s 2) 2 xt xt = γ) :
    FirstDoublePole (kacC b) (kacH r s b) (ellMinus p p' r s 2)
      (exampleCoeff b r s (p - r) (p' + s) γ) := by
  have hmin2 : ellMin p p' r s 2 = ellMinus p p' r s 2 := by unfold ellMin; omega
  have hN3 := ellMin3 hset false
  rw [TT.ellOrb_false (by norm_num)] at hN3
  obtain ⟨xp, xm, -, hxm, -, hjm, ⟨hBle, hBc⟩, ⟨hHle, hHc⟩, hlow⟩ :=
    top_two hJ hI hset hmin2 hN3
  have hj := hjm le_rfl
  obtain ⟨hval, hne⟩ := small_value hH hF hU hset false (TT.ellOrb_false (by norm_num)) hxm hj hγ
  simp only [Bool.false_eq_true, if_false] at hval hne
  rw [topTermSph_big _ _ _ 2 hsmall, zero_add, topTermSph_self _ (Bsph_zero _ _), hval] at hBc
  rw [topTermSph_big _ _ _ 2 hsmall, zero_add, topTermSph_self _ (Hsph_zero _ _), hval] at hHc
  exact fdp_of hlow hBle hBc hHle hHc hne

/-- The first double pole at `N = ℓ⁺_2 = ℓ₂` (sphere/paper.tex l.1834–1840). -/
theorem fdp_plus (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial) (hU : Cited_SingularUnique)
    {b : ℂ} (hset : MinimalSetting p p' r s b)
    (hsmall : ellPlus p p' r s 2 < ellMinus p p' r s 2) {γ : ℂ}
    (hγ : ∀ xt : Nat.Partition (ellPlus p p' r s 2) → ℂ, xt (onesPartition _) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s 2) xt)
        (ellPlus p p' r s 2) →
        jform (kacC b) (kacH r s b) (ellPlus p p' r s 2) 2 xt xt = γ) :
    FirstDoublePole (kacC b) (kacH r s b) (ellPlus p p' r s 2)
      (exampleCoeff b r s (r + p) (p' - s) γ) := by
  have hmin2 : ellMin p p' r s 2 = ellPlus p p' r s 2 := by unfold ellMin; omega
  have hN3 := ellMin3 hset true
  rw [TT.ellOrb_true (by norm_num)] at hN3
  obtain ⟨xp, xm, hxp, -, hjp, -, ⟨hBle, hBc⟩, ⟨hHle, hHc⟩, hlow⟩ :=
    top_two hJ hI hset hmin2 hN3
  have hj := hjp le_rfl
  obtain ⟨hval, hne⟩ := small_value hH hF hU hset true (TT.ellOrb_true (by norm_num)) hxp hj hγ
  simp only [if_true] at hval hne
  rw [topTermSph_big _ _ _ 2 hsmall, add_zero, topTermSph_self _ (Bsph_zero _ _), hval] at hBc
  rw [topTermSph_big _ _ _ 2 hsmall, add_zero, topTermSph_self _ (Hsph_zero _ _), hval] at hHc
  exact fdp_of hlow hBle hBc hHle hHc hne

end FirstDouble

end Virasoro.Sphere
