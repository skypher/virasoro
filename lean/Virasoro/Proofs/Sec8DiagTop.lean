import Virasoro.Proofs.Sec8DiagLeading
import Mathlib.LinearAlgebra.Lagrange

/-!
# Proposition 8.6 (`prop:top-ratios`)

A chain with `x₁ = θ ≠ μ` is the label from `a` to `θ` followed by a chain from `θ` to `μ`;
grouping by `x₂`, Lemma 8.5(ii) from the base `θ` and partial fractions give
`F(θ) = ρ_{aθ} Top(θ→μ) / ∏_{θ' ∈ FS(θ→μ)} (h_{aθ} - h_{θθ'})`.  Lemma 8.5(ii) for the end `θ`
gives `ρ_{aθ}`, and Lemma 8.5(ii) for the end `μ` gives the identity.  Differences of momenta of
the same class are `2pp'` times differences of positions.
-/

namespace Virasoro

open scoped LaurentSeries

/-- Partial fractions: `∑_i T/∏_{j ≠ i}(y_i - y_j)/(z - y_i) = T/∏_i (z - y_i)`. -/
theorem partial_frac {ι K : Type*} [DecidableEq ι] [Field K] (S : Finset ι) (y : ι → K)
    (z T : K) (hinj : Set.InjOn y S) (hS : S.Nonempty) (hz : ∀ i ∈ S, z ≠ y i) :
    ∑ i ∈ S, T / (∏ j ∈ S.erase i, (y i - y j)) / (z - y i) = T / ∏ i ∈ S, (z - y i) := by
  have hP : ∏ i ∈ S, (z - y i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (hz i hi)
  have hE : ∀ i ∈ S, ∏ j ∈ S.erase i, (y i - y j) ≠ 0 := by
    intro i hi
    refine Finset.prod_ne_zero_iff.2 fun j hj e => ?_
    have hj' := Finset.mem_erase.1 hj
    exact hj'.1 (hinj hj'.2 hi (sub_eq_zero.1 e).symm)
  have h1 := congrArg (Polynomial.eval z) (Lagrange.sum_basis hinj hS)
  rw [Polynomial.eval_finset_sum, Polynomial.eval_one] at h1
  have hb : ∀ i ∈ S, (Lagrange.basis S y i).eval z =
      (∏ j ∈ S, (z - y j)) / ((z - y i) * ∏ j ∈ S.erase i, (y i - y j)) := by
    intro i hi
    rw [Lagrange.basis, Polynomial.eval_prod]
    simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X]
    rw [← Finset.mul_prod_erase S (fun j => z - y j) hi, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, mul_div_mul_left _ _ (sub_ne_zero.2 (hz i hi)), div_eq_inv_mul]
  rw [Finset.sum_congr rfl hb] at h1
  calc ∑ i ∈ S, T / (∏ j ∈ S.erase i, (y i - y j)) / (z - y i)
      = T / (∏ i ∈ S, (z - y i)) *
          ∑ i ∈ S, (∏ j ∈ S, (z - y j)) / ((z - y i) * ∏ j ∈ S.erase i, (y i - y j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hzi : z - y i ≠ 0 := sub_ne_zero.2 (hz i hi)
        have := hE i hi
        first | (field_simp; ring) | field_simp
    _ = T / ∏ i ∈ S, (z - y i) := by rw [h1, mul_one]

/-- `A B = (P₂/P₃) C` from `C/(P₃P₁) = (A/P₁)(B/P₂)`. -/
theorem top_alg {K : Type*} [Field K] {A B C P1 P2 P3 : K} (h1 : P1 ≠ 0) (h2 : P2 ≠ 0)
    (h3 : P3 ≠ 0) (key : C / (P3 * P1) = A / P1 * (B / P2)) : A * B = P2 / P3 * C := by
  rw [div_mul_div_comm, div_eq_div_iff (mul_ne_zero h3 h1) (mul_ne_zero h1 h2)] at key
  rw [div_mul_eq_mul_div, eq_div_iff h3]
  apply mul_left_cancel₀ h1
  linear_combination (-1 : K) * key

variable {p p' r s : ℕ} {b : ℂ}

/-- `S_x = c + 2pp' π_x` with `c` depending only on the parity of the layer. -/
theorem nodeS_pos (a : Node) :
    ((nodeS p p' r s a : ℤ) : ℚ) =
      (if a.2 % 2 = 0 then ((p' : ℚ) * r - p * s) else ((p' : ℚ) * r + p * s - p * p')) +
        2 * p * p' * nodePos a := by
  obtain ⟨ε, k⟩ := a
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k <;> cases ε
  · have h : (2 * j) % 2 = 0 := by omega
    simp only [nodeS, nodePos, Bool.false_eq_true, ↓reduceIte, nOrb_even_false, h]
    push_cast; ring
  · have h : (2 * j) % 2 = 0 := by omega
    simp only [nodeS, nodePos, ↓reduceIte, nOrb_even_true, h]
    push_cast; ring
  · have h : (2 * j + 1) % 2 ≠ 0 := by omega
    simp only [nodeS, nodePos, Bool.false_eq_true, ↓reduceIte, nOrb_odd_false, h]
    push_cast; ring
  · have h : (2 * j + 1) % 2 ≠ 0 := by omega
    simp only [nodeS, nodePos, ↓reduceIte, nOrb_odd_true, h]
    push_cast; ring

/-- Momenta of the same class differ by `2pp'` times the difference of the positions. -/
theorem nodeS_sub {x y : Node} (h : x.2 % 2 = y.2 % 2) :
    ((nodeS p p' r s x : ℂ) - nodeS p p' r s y) =
      2 * (p : ℂ) * p' * (((nodePos x : ℚ) : ℂ) - ((nodePos y : ℚ) : ℂ)) := by
  have hx := nodeS_pos (p := p) (p' := p') (r := r) (s := s) x
  have hy := nodeS_pos (p := p) (p' := p') (r := r) (s := s) y
  rw [h] at hx
  have hq : ((nodeS p p' r s x : ℤ) : ℚ) - nodeS p p' r s y =
      2 * p * p' * (nodePos x - nodePos y) := by
    rw [hx, hy]; ring
  have := congrArg (fun q : ℚ => (q : ℂ)) hq
  push_cast at this
  exact this

/-- `F_{a→μ}(θ) = ∑_{x₁ = θ} w_γ`. -/
noncomputable def Fsum (p p' r s : ℕ) (b : ℂ) (a μ θ : Node) : Kd :=
  ∑ γ ∈ (nodeChains a μ).filter (fun γ => γ.tail.head? = some θ), chainW p p' r s b γ

/-- The coefficient `(S_θ/S_a)^{D(θ,μ)} κ̂(a,θ,μ)`. -/
def topFac (p p' r s : ℕ) (a θ μ : Node) : ℚ :=
  ((nodeS p p' r s θ : ℚ) / nodeS p p' r s a) ^ (μ.2 - θ.2) * kappaHat a θ μ

theorem sum_group_first {a μ : Node} (φ : Node → Kd) :
    ∑ γ ∈ nodeChains a μ, chainW p p' r s b γ * φ (γ.tail.headD a) =
      ∑ θ ∈ firstSteps a μ, Fsum p p' r s b a μ θ * φ θ := by
  have hmaps : ∀ γ ∈ nodeChains a μ, (fun γ : List Node => γ.tail.headD a) γ ∈ firstSteps a μ := by
    intro γ hγ
    obtain ⟨x, l, rfl, hx⟩ := chain_first hγ
    simpa using hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [Fsum, Finset.sum_mul]
  have hf : (nodeChains a μ).filter (fun γ => γ.tail.headD a = θ) =
      (nodeChains a μ).filter (fun γ => γ.tail.head? = some θ) :=
    Finset.filter_congr fun γ hγ => by
      obtain ⟨x, l, rfl, -⟩ := chain_first hγ
      simp
  rw [hf]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨hγ1, hγ2⟩ := Finset.mem_filter.1 hγ
  obtain ⟨x, l, rfl, -⟩ := chain_first hγ1
  simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at hγ2
  subst hγ2
  rfl

theorem chains_filter_step {a μ θ : Node} (haμ : a.2 < μ.2) (hθ : θ ∈ firstSteps a μ)
    (hθμ : θ ≠ μ) :
    (nodeChains a μ).filter (fun γ => γ.tail.head? = some θ) = (nodeChains θ μ).image (a :: ·) := by
  ext γ
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    rw [nodeChains_of_lt haμ] at h1
    rcases Finset.mem_union.1 h1 with h | h
    · split_ifs at h with ho
      · rw [Finset.mem_singleton.1 h] at h2
        simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h2
        exact absurd h2.symm hθμ
      · simp at h
    · obtain ⟨θ', -, h3⟩ := Finset.mem_biUnion.1 h
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h3
      obtain ⟨x, l, rfl, -⟩ := chain_first hγ'
      simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h2
      subst h2
      exact ⟨_, hγ', rfl⟩
  · rintro ⟨γ', hγ', rfl⟩
    refine ⟨?_, ?_⟩
    · rw [nodeChains_of_lt haμ]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨⟨θ, Finset.mem_filter.2 ⟨hθ, hθμ⟩⟩,
        Finset.mem_attach _ _, Finset.mem_image.2 ⟨γ', hγ', rfl⟩⟩)
    · obtain ⟨x, l, rfl, -⟩ := chain_first hγ'
      simp

/-- The chains from `a` to `θ` entering `θ` directly: only the one-label chain. -/
theorem Fsum_self {a θ : Node} (haθ : a.2 < θ.2) (hodd : (θ.2 - a.2) % 2 = 1) :
    Fsum p p' r s b a θ θ = nodeRho p p' r s b a θ := by
  have hf : (nodeChains a θ).filter (fun γ => γ.tail.head? = some θ) = {[a, θ]} := by
    ext γ
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rw [nodeChains_of_lt haθ] at h1
      rcases Finset.mem_union.1 h1 with h | h
      · rw [if_pos hodd, Finset.mem_singleton] at h; exact h
      · obtain ⟨θ', -, h3⟩ := Finset.mem_biUnion.1 h
        obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h3
        obtain ⟨x, l, rfl, -⟩ := chain_first hγ'
        simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h2
        exact absurd h2 (Finset.mem_filter.1 θ'.2).2
    · rintro rfl
      refine ⟨?_, by simp⟩
      rw [nodeChains_of_lt haθ]
      exact Finset.mem_union_left _ (by rw [if_pos hodd]; exact Finset.mem_singleton_self _)
  rw [Fsum, hf, Finset.sum_singleton]
  simp [chainW, chainRho, chainLinks]

/-- `F_{a→μ}(θ) = ρ_{aθ} ∑_{θ' ∈ FS(θ→μ)} F_{θ→μ}(θ')/(h_{aθ} - h_{θθ'})` for `θ ≠ μ`. -/
theorem Fsum_rec {a μ θ : Node} (haμ : a.2 < μ.2) (hθ : θ ∈ firstSteps a μ) (hθμ : θ ≠ μ) :
    Fsum p p' r s b a μ θ = nodeRho p p' r s b a θ *
      ∑ θ' ∈ firstSteps θ μ, Fsum p p' r s b θ μ θ' /
        (nodeH p p' r s b a θ - nodeH p p' r s b θ θ') := by
  rw [Fsum, chains_filter_step haμ hθ hθμ,
    Finset.sum_image (fun x _ y _ h => List.cons_injective h)]
  simp_rw [div_eq_mul_inv]
  rw [← sum_group_first (a := θ) (μ := μ)
    (fun θ' => (nodeH p p' r s b a θ - nodeH p p' r s b θ θ')⁻¹), Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ' hγ' => ?_
  obtain ⟨x, l, rfl, -⟩ := chain_first hγ'
  simp only [List.tail_cons, List.headD_cons]
  rw [show chainW p p' r s b (a :: θ :: x :: l) =
      nodeRho p p' r s b a θ * chainRho p p' r s b (θ :: x :: l) /
        ((nodeH p p' r s b a θ - nodeH p p' r s b θ x) * chainLinks p p' r s b (θ :: x :: l)) from rfl,
    chainW, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

section Top

variable (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
  (hset : MinimalSetting p p' r s b)
include hK hH hset

theorem Fsum_eq {a μ θ : Node} (haμ : a.2 < μ.2) (hθ : θ ∈ firstSteps a μ) :
    Fsum p p' r s b a μ θ = nodeTop p p' r s b a μ /
      ∏ θ' ∈ (firstSteps a μ).erase θ, (nodeH p p' r s b a θ - nodeH p p' r s b a θ') :=
  (lem_node_leading_of_cited hK hH p p' r s b hset a μ haμ).2.2.2.2.2 θ hθ

/-- `ρ_{aθ} = Top(a→θ)/∏_{θ̃ ∈ FS(a→θ), θ̃ ≠ θ} (h_{aθ} - h_{aθ̃})`. -/
theorem rho_eq {a θ : Node} (haθ : a.2 < θ.2) (hodd : (θ.2 - a.2) % 2 = 1) :
    nodeRho p p' r s b a θ = nodeTop p p' r s b a θ /
      ∏ θ' ∈ (firstSteps a θ).erase θ, (nodeH p p' r s b a θ - nodeH p p' r s b a θ') := by
  rw [← Fsum_self haθ hodd]
  exact Fsum_eq hK hH hset haθ (mem_firstSteps.2 (Or.inr ⟨hodd, rfl⟩))

/-- The identity of Proposition 8.6 for a first step `θ ≠ μ`. -/
theorem top_identity {a θ μ : Node} (hθ : θ ∈ firstSteps a μ) (hθμ : θ ≠ μ) :
    nodeTop p p' r s b a θ * nodeTop p p' r s b θ μ =
      ((topFac p p' r s a θ μ : ℚ) : Kd) * nodeTop p p' r s b a μ := by
  obtain ⟨haθ, hodd⟩ := firstSteps_props hθ
  have hθμ2 : θ.2 < μ.2 := by
    rcases mem_firstSteps.1 hθ with ⟨-, h, -⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h hθμ
  have haμ : a.2 < μ.2 := haθ.trans hθμ2
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb0 := b_ne_zero_of hset
  have hσ : varsig p' b ≠ 0 := by
    unfold varsig
    exact div_ne_zero hb0 (mul_ne_zero two_ne_zero (pow_ne_zero 2 (by exact_mod_cast hp'.ne')))
  have hN : (2 * (p : ℂ) * p') ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne')) (by exact_mod_cast hp'.ne')
  have hSa : (nodeS p p' r s a : ℂ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset a
  have hSθ : (nodeS p p' r s θ : ℂ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset θ
  have hθself : θ ∈ firstSteps a θ := mem_firstSteps.2 (Or.inr ⟨hodd, rfl⟩)
  have hsub : firstSteps a θ ⊆ firstSteps a μ := by
    intro x hx
    rw [mem_firstSteps] at hx ⊢
    rcases hx with ⟨h1, h2, h3⟩ | ⟨h1, rfl⟩
    · exact Or.inl ⟨h1, by omega, h3⟩
    · exact Or.inl ⟨haθ, hθμ2, h1⟩
  -- the product over `FS(a→μ) ∖ {θ}` splits
  have hsplit : ∏ x ∈ (firstSteps a μ).erase θ,
        (nodeH p p' r s b a θ - nodeH p p' r s b a x) =
      (∏ x ∈ firstSteps a μ \ firstSteps a θ, (nodeH p p' r s b a θ - nodeH p p' r s b a x)) *
        ∏ x ∈ (firstSteps a θ).erase θ, (nodeH p p' r s b a θ - nodeH p p' r s b a x) := by
    rw [← Finset.prod_sdiff (Finset.erase_subset_erase θ hsub)]
    congr 2
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h2, fun h4 => h3 ⟨h1, h4⟩⟩
    · rintro ⟨h2, h3⟩
      refine ⟨⟨fun e => h3 (by rw [e]; exact hθself), h2⟩, fun h4 => h3 h4.2⟩
  -- nonvanishing of the three products
  have hP1 : ∏ x ∈ (firstSteps a θ).erase θ,
      (nodeH p p' r s b a θ - nodeH p p' r s b a x) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun x hx e => ?_
    have hx' := Finset.mem_erase.1 hx
    exact hx'.1 (nodeH_injOn hset haθ hx'.2 hθself (sub_eq_zero.1 e).symm)
  have hP3 : ∏ x ∈ firstSteps a μ \ firstSteps a θ,
      (nodeH p p' r s b a θ - nodeH p p' r s b a x) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun x hx e => ?_
    have hx' := Finset.mem_sdiff.1 hx
    have hxθ := nodeH_injOn hset haμ hx'.1 hθ (sub_eq_zero.1 e).symm
    exact hx'.2 (by rw [hxθ]; exact hθself)
  have hz : ∀ θ' ∈ firstSteps θ μ, nodeH p p' r s b a θ ≠ nodeH p p' r s b θ θ' := by
    intro θ' hθ' e
    obtain ⟨h1, h1o⟩ := firstSteps_props hθ'
    have a1 := node_abs_lt hset haθ hodd
    have a2 := node_abs_lt hset h1 h1o
    have hne : nodeS p p' r s θ' ≠ nodeS p p' r s a := by
      intro e'; rw [e'] at a2; linarith
    apply hne
    unfold nodeH at e
    have e1 := mul_left_cancel₀ hσ (RatFunc.C_injective e)
    have e2 : (nodeS p p' r s θ : ℂ) * ((nodeS p p' r s θ' : ℂ) - nodeS p p' r s a) = 0 := by
      linear_combination e1
    rcases mul_eq_zero.1 e2 with h | h
    · exact absurd h hSθ
    · exact_mod_cast sub_eq_zero.1 h
  have hP2 : ∏ θ' ∈ firstSteps θ μ, (nodeH p p' r s b a θ - nodeH p p' r s b θ θ') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun θ' h => sub_ne_zero.2 (hz θ' h)
  have hne_fs : (firstSteps θ μ).Nonempty :=
    Finset.card_pos.1 (by rw [firstSteps_card hθμ2]; omega)
  -- the three instances of Lemma 8.5(ii) and partial fractions
  have hF2 := Fsum_rec (p := p) (p' := p') (r := r) (s := s) (b := b) haμ hθ hθμ
  have hF3 : ∀ θ' ∈ firstSteps θ μ, Fsum p p' r s b θ μ θ' /
        (nodeH p p' r s b a θ - nodeH p p' r s b θ θ') =
      nodeTop p p' r s b θ μ /
        (∏ θ'' ∈ (firstSteps θ μ).erase θ', (nodeH p p' r s b θ θ' - nodeH p p' r s b θ θ'')) /
        (nodeH p p' r s b a θ - nodeH p p' r s b θ θ') := by
    intro θ' hθ'
    rw [Fsum_eq hK hH hset hθμ2 hθ']
  have hpf : ∑ θ' ∈ firstSteps θ μ, nodeTop p p' r s b θ μ /
        (∏ θ'' ∈ (firstSteps θ μ).erase θ', (nodeH p p' r s b θ θ' - nodeH p p' r s b θ θ'')) /
        (nodeH p p' r s b a θ - nodeH p p' r s b θ θ') =
      nodeTop p p' r s b θ μ /
        ∏ θ' ∈ firstSteps θ μ, (nodeH p p' r s b a θ - nodeH p p' r s b θ θ') :=
    partial_frac (firstSteps θ μ) (fun θ' => nodeH p p' r s b θ θ') (nodeH p p' r s b a θ)
      (nodeTop p p' r s b θ μ) (nodeH_injOn hset hθμ2) hne_fs hz
  rw [Finset.sum_congr rfl hF3, hpf, rho_eq hK hH hset haθ hodd] at hF2
  have key := hF2
  rw [Fsum_eq hK hH hset haμ hθ, hsplit] at key
  have hmain := top_alg hP1 hP2 hP3 key
  -- the ratio of the two products is `(S_θ/S_a)^{D(θ,μ)} κ̂(a,θ,μ)`
  have hd1 : ∀ θ' ∈ firstSteps θ μ, nodeH p p' r s b a θ - nodeH p p' r s b θ θ' =
      pt (varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p') *
        (((nodePos θ' : ℚ) : ℂ) - ((nodePos a : ℚ) : ℂ))) := by
    intro θ' hθ'
    obtain ⟨h1, h1o⟩ := firstSteps_props hθ'
    have hs := nodeS_sub (p := p) (p' := p') (r := r) (s := s) (x := θ') (y := a) (by omega)
    unfold nodeH
    rw [← map_sub]
    congr 1
    linear_combination (varsig p' b * (nodeS p p' r s θ : ℂ)) * hs
  have hd2 : ∀ x ∈ firstSteps a μ \ firstSteps a θ, nodeH p p' r s b a θ - nodeH p p' r s b a x =
      pt (varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p') *
        (((nodePos x : ℚ) : ℂ) - ((nodePos θ : ℚ) : ℂ))) := by
    intro x hx
    obtain ⟨h1, h1o⟩ := firstSteps_props (Finset.mem_sdiff.1 hx).1
    have hs := nodeS_sub (p := p) (p' := p') (r := r) (s := s) (x := x) (y := θ) (by omega)
    unfold nodeH
    rw [← map_sub]
    congr 1
    linear_combination (varsig p' b * (nodeS p p' r s a : ℂ)) * hs
  have hcard2 : (firstSteps a μ \ firstSteps a θ).card = μ.2 - θ.2 := by
    rw [Finset.card_sdiff_of_subset hsub, firstSteps_card haμ, firstSteps_card haθ]; omega
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = ∏ θ' ∈ firstSteps θ μ,
      (((nodePos θ' : ℚ) : ℂ) - ((nodePos a : ℚ) : ℂ)) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = ∏ x ∈ firstSteps a μ \ firstSteps a θ,
      (((nodePos x : ℚ) : ℂ) - ((nodePos θ : ℚ) : ℂ)) := ⟨_, rfl⟩
  have hP2e : ∏ θ' ∈ firstSteps θ μ, (nodeH p p' r s b a θ - nodeH p p' r s b θ θ') =
      pt ((varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p')) ^ (μ.2 - θ.2) * A) := by
    rw [Finset.prod_congr rfl hd1, ← map_prod, Finset.prod_mul_distrib, Finset.prod_const,
      firstSteps_card hθμ2, hA]
  have hP3e : ∏ x ∈ firstSteps a μ \ firstSteps a θ,
        (nodeH p p' r s b a θ - nodeH p p' r s b a x) =
      pt ((varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (μ.2 - θ.2) * B) := by
    rw [Finset.prod_congr rfl hd2, ← map_prod, Finset.prod_mul_distrib, Finset.prod_const,
      hcard2, hB]
  have hB0 : B ≠ 0 := by
    intro h0; apply hP3; rw [hP3e, h0, mul_zero]; exact map_zero _
  have hq : (∏ θ' ∈ firstSteps θ μ, (nodeH p p' r s b a θ - nodeH p p' r s b θ θ')) /
        (∏ x ∈ firstSteps a μ \ firstSteps a θ, (nodeH p p' r s b a θ - nodeH p p' r s b a x)) =
      ((topFac p p' r s a θ μ : ℚ) : Kd) := by
    rw [hP2e, hP3e, ← map_div₀, ← map_ratCast (RatFunc.C : ℂ →+* Kd)]
    congr 1
    unfold topFac kappaHat
    push_cast
    rw [← hA, ← hB]
    have hX : varsig p' b * (nodeS p p' r s a : ℂ) * (2 * (p : ℂ) * p') ≠ 0 :=
      mul_ne_zero (mul_ne_zero hσ hSa) hN
    rw [div_eq_iff (mul_ne_zero (pow_ne_zero _ hX) hB0), div_pow, div_mul_div_comm,
      div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (pow_ne_zero _ hSa) hB0)]
    ring
  rw [← hq]
  exact hmain

theorem top_ne_of_odd {x y : Node} (hxy : x.2 < y.2) (hodd : (y.2 - x.2) % 2 = 1) :
    nodeTop p p' r s b x y ≠ 0 := by
  intro h0
  have hρ := (lem_node_poles p p' r s b hset x y hxy hodd).2
  rw [rho_eq hK hH hset hxy hodd, h0, zero_div] at hρ
  exact hρ rfl

theorem top_ne {x y : Node} (hxy : x.2 < y.2) : nodeTop p p' r s b x y ≠ 0 := by
  rcases Nat.even_or_odd (y.2 - x.2) with he | ho
  · have he' : (y.2 - x.2) % 2 = 0 := Nat.even_iff.1 he
    have hθ : ((true, x.2 + 1) : Node) ∈ firstSteps x y :=
      mem_firstSteps.2 (Or.inl ⟨by show x.2 < x.2 + 1; omega, by show x.2 + 1 < y.2; omega,
        by show (x.2 + 1 - x.2) % 2 = 1; omega⟩)
    have hθy : ((true, x.2 + 1) : Node) ≠ y := by
      intro e
      have := congrArg Prod.snd e
      simp only at this
      omega
    have hid := top_identity hK hH hset hθ hθy
    have h1 := top_ne_of_odd hK hH hset (x := x) (y := (true, x.2 + 1))
      (by show x.2 < x.2 + 1; omega) (by show (x.2 + 1 - x.2) % 2 = 1; omega)
    have h2 := top_ne_of_odd hK hH hset (x := (true, x.2 + 1)) (y := y)
      (by show x.2 + 1 < y.2; omega) (by show (y.2 - (x.2 + 1)) % 2 = 1; omega)
    intro h0
    rw [h0, mul_zero] at hid
    exact mul_ne_zero h1 h2 hid
  · exact top_ne_of_odd hK hH hset hxy (Nat.odd_iff.1 ho)

end Top

/-- `κ̂(a,ν,μ)` for `ν` at even distance from `a`, through the node `θ = (+, L_a + 1)`:
`κ̂(a,θ,μ) κ̂(θ,ν,μ)/κ̂(a,θ,ν)`. -/
def kappaEven (a ν μ : Node) : ℚ :=
  kappaHat a (true, a.2 + 1) μ * kappaHat (true, a.2 + 1) ν μ / kappaHat a (true, a.2 + 1) ν

theorem top_even (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hset : MinimalSetting p p' r s b) {a ν μ : Node} (haν : a.2 < ν.2) (hνμ : ν.2 < μ.2)
    (hev : (ν.2 - a.2) % 2 = 0) :
    nodeTop p p' r s b a ν * nodeTop p p' r s b ν μ =
      ((((nodeS p p' r s ν : ℚ) / nodeS p p' r s a) ^ (μ.2 - ν.2) * kappaEven a ν μ : ℚ) : Kd) *
        nodeTop p p' r s b a μ := by
  have hθμ : ((true, a.2 + 1) : Node) ∈ firstSteps a μ :=
    mem_firstSteps.2 (Or.inl ⟨by show a.2 < a.2 + 1; omega, by show a.2 + 1 < μ.2; omega,
      by show (a.2 + 1 - a.2) % 2 = 1; omega⟩)
  have hθν : ((true, a.2 + 1) : Node) ∈ firstSteps a ν :=
    mem_firstSteps.2 (Or.inl ⟨by show a.2 < a.2 + 1; omega, by show a.2 + 1 < ν.2; omega,
      by show (a.2 + 1 - a.2) % 2 = 1; omega⟩)
  have hνθμ : ν ∈ firstSteps (true, a.2 + 1) μ :=
    mem_firstSteps.2 (Or.inl ⟨by show a.2 + 1 < ν.2; omega, hνμ,
      by show (ν.2 - (a.2 + 1)) % 2 = 1; omega⟩)
  have hne1 : ((true, a.2 + 1) : Node) ≠ μ := by
    intro e; have := congrArg Prod.snd e; simp only at this; omega
  have hne2 : ((true, a.2 + 1) : Node) ≠ ν := by
    intro e; have := congrArg Prod.snd e; simp only at this; omega
  have hne3 : ν ≠ μ := by intro e; rw [e] at hνμ; exact lt_irrefl _ hνμ
  have h1 := top_identity hK hH hset hθμ hne1
  have h2 := top_identity hK hH hset hνθμ hne3
  have h3 := top_identity hK hH hset hθν hne2
  have hT1 := top_ne hK hH hset (x := a) (y := (true, a.2 + 1)) (by show a.2 < a.2 + 1; omega)
  have hT2 := top_ne hK hH hset (x := (true, a.2 + 1)) (y := ν) (by show a.2 + 1 < ν.2; omega)
  have hc3 : ((topFac p p' r s a (true, a.2 + 1) ν : ℚ) : Kd) ≠ 0 := by
    intro h; rw [h, zero_mul] at h3; exact mul_ne_zero hT1 hT2 h3
  have hc3q : topFac p p' r s a (true, a.2 + 1) ν ≠ 0 := fun h => hc3 (by rw [h, Rat.cast_zero])
  have hk3 : kappaHat a (true, a.2 + 1) ν ≠ 0 := by
    intro h; apply hc3q; unfold topFac; rw [h, mul_zero]
  have hSa : (nodeS p p' r s a : ℚ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset a
  have hSθ : (nodeS p p' r s (true, a.2 + 1) : ℚ) ≠ 0 := by
    exact_mod_cast nodeS_ne_zero hset (true, a.2 + 1)
  have hQ : topFac p p' r s a (true, a.2 + 1) ν *
        (((nodeS p p' r s ν : ℚ) / nodeS p p' r s a) ^ (μ.2 - ν.2) * kappaEven a ν μ) =
      topFac p p' r s a (true, a.2 + 1) μ * topFac p p' r s (true, a.2 + 1) ν μ := by
    unfold topFac kappaEven
    simp only
    rw [show μ.2 - (a.2 + 1) = (ν.2 - (a.2 + 1)) + (μ.2 - ν.2) by omega, pow_add]
    rw [div_pow, div_pow, div_pow, div_pow]
    first | (field_simp; ring) | field_simp
  have hq : ((topFac p p' r s a (true, a.2 + 1) ν : ℚ) : Kd) *
        (((((nodeS p p' r s ν : ℚ) / nodeS p p' r s a) ^ (μ.2 - ν.2) * kappaEven a ν μ : ℚ)) : Kd) =
      ((topFac p p' r s a (true, a.2 + 1) μ : ℚ) : Kd) *
        ((topFac p p' r s (true, a.2 + 1) ν μ : ℚ) : Kd) := by
    rw [← Rat.cast_mul, ← Rat.cast_mul, hQ]
  apply mul_left_cancel₀ hc3
  linear_combination (-nodeTop p p' r s b ν μ) * h3 + nodeTop p p' r s b a (true, a.2 + 1) * h2 +
    ((topFac p p' r s (true, a.2 + 1) ν μ : ℚ) : Kd) * h1 - nodeTop p p' r s b a μ * hq

/-- Proposition 8.6 (`prop:top-ratios`), from the two cited results (through Lemma 8.5).

Paper label: prop:top-ratios -/
theorem prop_top_ratios_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_prop_top_ratios :=
  ⟨fun _ _ _ _ _ hset => ⟨fun _ _ hxy => top_ne hK hH hset hxy,
      fun _ _ _ hθ hθμ => top_identity hK hH hset hθ hθμ⟩,
    ⟨kappaEven, fun _ _ _ _ _ hset _ _ _ h1 h2 h3 => top_even hK hH hset h1 h2 h3⟩⟩

end Virasoro
