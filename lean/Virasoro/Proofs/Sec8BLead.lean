import Virasoro.Proofs.Sec8BBridge
import Virasoro.Proofs.Sec8DiagLeading
import Virasoro.Proofs.Sec8DiagJets

/-!
# Section 8.2: leading terms of the boundary chains, and Theorem 8.11(i)

As for Lemma 8.5, with Lemma 8.10 in place of Lemmas 8.3(ii),(iii) and 8.4, `T` in place of `S`
and `h_{aθ} = ς(K + ε T_a T_θ)`; now every node strictly between `a` and `μ`, and `μ` itself, is a
first step, one per layer.  Lemma 8.5(ii) for the one-label chain gives Theorem 8.11(i).
-/

namespace Virasoro

open scoped LaurentSeries

section Defs

variable (p p' x₀ : ℕ) (b : ℂ)

/-- `∏ ρ_{g_i}` along a chain. -/
noncomputable def bChRho : List ℕ → Kd
  | y₀ :: y₁ :: l => bRho p p' x₀ b y₀ y₁ * bChRho (y₁ :: l)
  | _ => 1

/-- `∏ (h_{i-1} - h_i)` along a chain. -/
noncomputable def bChLinks : List ℕ → Kd
  | y₀ :: y₁ :: y₂ :: l =>
      (bH p p' x₀ b y₀ y₁ - bH p p' x₀ b y₁ y₂) * bChLinks (y₁ :: y₂ :: l)
  | _ => 1

/-- `w_γ`. -/
noncomputable def bChW (γ : List ℕ) : Kd := bChRho p p' x₀ b γ / bChLinks p p' x₀ b γ

/-- `h_0` of a chain. -/
noncomputable def bChH0 : List ℕ → Kd
  | y₀ :: y₁ :: _ => bH p p' x₀ b y₀ y₁
  | _ => 0

/-- `h_n` of a chain. -/
noncomputable def bChHn : List ℕ → Kd
  | [y₀, y₁] => bH p p' x₀ b y₀ y₁
  | _ :: l => bChHn l
  | [] => 0

/-- `F(θ) = ∑_{x₁ = θ} w_γ`. -/
noncomputable def bFsum (i k θ : ℕ) : Kd :=
  ∑ γ ∈ (bChains i k).filter (fun γ => γ.tail.head? = some θ), bChW p p' x₀ b γ

end Defs

/-- The steps of a list of layers increase and it ends at `k`. -/
def bSteps (k : ℕ) : List ℕ → Prop
  | [] => False
  | [x] => x = k
  | x :: y :: l => x < y ∧ bSteps k (y :: l)

theorem b_steps_of_mem {i k : ℕ} {γ : List ℕ} (hγ : γ ∈ bChains i k) :
    ∃ x l, γ = i :: x :: l ∧ i < x ∧ bSteps k (x :: l) := by
  rcases Nat.lt_or_ge i k with h | h
  · rw [bChains_of_lt h] at hγ
    rcases Finset.mem_union.1 hγ with h1 | h1
    · rw [Finset.mem_singleton.1 h1]; exact ⟨k, [], rfl, h, rfl⟩
    · obtain ⟨θ, -, h2⟩ := Finset.mem_biUnion.1 h1
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h2
      obtain ⟨x, l, rfl, h3, h4⟩ := b_steps_of_mem hγ'
      exact ⟨θ.1, x :: l, rfl, (Finset.mem_Ioo.1 θ.2).1, ⟨h3, h4⟩⟩
  · rw [bChains_of_le h] at hγ; simp at hγ
termination_by k - i
decreasing_by have := Finset.mem_Ioo.1 θ.2; omega

theorem b_steps_last {k x : ℕ} {l : List ℕ} (h : bSteps k (x :: l)) : x ≤ k := by
  induction l generalizing x with
  | nil => simp only [bSteps] at h; rw [h]
  | cons y l ih => obtain ⟨h1, h3⟩ := h; exact h1.le.trans (ih h3)

theorem b_chain_first {i k : ℕ} {γ : List ℕ} (hγ : γ ∈ bChains i k) :
    ∃ x l, γ = i :: x :: l ∧ x ∈ Finset.Ioc i k := by
  obtain ⟨x, l, rfl, hlt, hok⟩ := b_steps_of_mem hγ
  exact ⟨x, l, rfl, Finset.mem_Ioc.2 ⟨hlt, b_steps_last hok⟩⟩

theorem bPi_injective : Function.Injective bPi := by
  intro m m' h
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m <;> obtain ⟨j', rfl | rfl⟩ := Nat.even_or_odd' m'
  · rw [bPi_even, bPi_even] at h; omega
  · rw [bPi_even, bPi_odd] at h; omega
  · rw [bPi_odd, bPi_even] at h; omega
  · rw [bPi_odd, bPi_odd] at h; omega

variable {p p' x₀ : ℕ} {b : ℂ}

theorem bT_sub (m m' : ℕ) :
    (bT p p' x₀ m : ℂ) - bT p p' x₀ m' = 2 * (p : ℂ) * p' * ((bPi m : ℂ) - bPi m') := by
  unfold bT; push_cast; ring

section Lead

variable (hB : BoundarySetting p p' x₀ b)
include hB

theorem varsig_ne : varsig p' b ≠ 0 := by
  have hmin := bSetting_minimal hB
  have hb0 := b_ne_zero_of hmin
  have hp' : 0 < p' := by have := hB.2.1; omega
  unfold varsig
  exact div_ne_zero hb0 (mul_ne_zero two_ne_zero (pow_ne_zero 2 (by exact_mod_cast hp'.ne')))

theorem bEps_ne : (bEps p x₀ : ℂ) ≠ 0 := by
  unfold bEps; split_ifs <;> norm_num

/-- `δ_g = h_g t + O(t²)` with `h_g = ς(K + ε T_i T_m)`. -/
theorem lv_bDel {i m : ℕ} (him : i < m) : LV (bDel p p' x₀ b i m) 1 (bH p p' x₀ b i m) := by
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  have hmin := bSetting_minimal hB
  have hb0 := b_ne_zero_of hmin
  have hbs : (bsC b : Kd) ≠ 0 := by simpa [bsC] using hb0
  have hxy := ((lem_boundary_labels p p' x₀ b hB).1 i m him).2.2.2.2.2.1
  have hv := regVal_hG hbs (bLabel p p' x₀ i m)
  have h0 : (bDel p p' x₀ b i m).coeff 0 = 0 := by
    unfold bDel delG deltaG
    rw [HahnSeries.coeff_sub, hv.2, (j2_C (kacHL (bLabel p p' x₀ i m) (bsC b))).2.1, sub_self]
  have hreg : OrdGE (bDel p p' x₀ b i m) 0 := by
    unfold bDel delG deltaG
    exact hv.1.sub (j2_C _).1
  refine ⟨?_, ?_⟩
  · rw [ordGE_iff] at hreg ⊢
    intro n hn
    rcases lt_or_eq_of_le (show n ≤ 0 by omega) with h | h
    · exact hreg n h
    · rw [h]; exact h0
  · unfold bDel bH
    rw [node_slope hp hp' hB.2.2.2.2.2.2]
    congr 2
    have : ((((p' : ℤ) * (bLabel p p' x₀ i m).1 - p * (bLabel p p' x₀ i m).2 : ℤ) : ℂ) *
        (((p' : ℤ) * (bLabel p p' x₀ i m).1 + p * (bLabel p p' x₀ i m).2 : ℤ) : ℂ)) =
        (((-bEps p x₀ * bT p p' x₀ i * bT p p' x₀ m : ℤ)) : ℂ) := by
      rw [← Int.cast_mul, hxy]
    rw [this]
    push_cast
    ring

/-- Consecutive slopes differ. -/
theorem bH_link_ne {π ν ν' : ℕ} (h1 : π < ν) (h2 : ν < ν') :
    bH p p' x₀ b π ν - bH p p' x₀ b ν ν' ≠ 0 := by
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  unfold bH
  rw [← map_sub]
  refine (map_ne_zero _).2 ?_
  have e : varsig p' b * (((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) + (bEps p x₀ : ℂ) * (bT p p' x₀ π : ℂ) *
      (bT p p' x₀ ν : ℂ)) - varsig p' b * (((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) +
      (bEps p x₀ : ℂ) * (bT p p' x₀ ν : ℂ) * (bT p p' x₀ ν' : ℂ)) =
      varsig p' b * (bEps p x₀ : ℂ) * (bT p p' x₀ ν : ℂ) *
        (2 * (p : ℂ) * p' * ((bPi π : ℂ) - bPi ν')) := by
    rw [← bT_sub]; ring
  rw [e]
  have hπ : (bPi π : ℂ) - bPi ν' ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have := bPi_injective (by exact_mod_cast h : bPi π = bPi ν'); omega
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (varsig_ne hB) (bEps_ne hB))
    (by exact_mod_cast bT_ne hB ν)) (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (by exact_mod_cast hp.ne')) (by exact_mod_cast hp'.ne')) hπ)

theorem bH_injOn (i : ℕ) : Set.InjOn (fun θ => bH p p' x₀ b i θ) (Set.Ioi i) := by
  intro θ _ θ' _ h
  simp only [bH] at h
  have h1 := mul_left_cancel₀ (varsig_ne hB) (RatFunc.C_injective h)
  have h2 : (bEps p x₀ : ℂ) * (bT p p' x₀ i : ℂ) * ((bT p p' x₀ θ : ℂ) - bT p p' x₀ θ') = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact absurd h' (bEps_ne hB)
    · exact absurd (by exact_mod_cast h') (bT_ne hB i)
  · rw [bT_sub] at h
    have hp : 0 < p := by have := hB.1; omega
    have hp' : 0 < p' := by have := hB.2.1; omega
    rcases mul_eq_zero.1 h with h' | h'
    · exfalso
      exact mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne'))
        (by exact_mod_cast hp'.ne') h'
    · exact bPi_injective (by exact_mod_cast sub_eq_zero.1 h')

/-- The tail of a chain entered from `π`. -/
theorem b_tail_lead (j k : ℕ) :
    ∀ (l : List ℕ) (π ν : ℕ), bSteps k (ν :: l) → π < ν →
      LV (bTailProd p p' x₀ b j (bDel p p' x₀ b π ν) ν l) ((j : ℤ) - (k - ν))
        (bChRho p p' x₀ b (ν :: l) / bChLinks p p' x₀ b (π :: ν :: l) *
          bChHn p p' x₀ b (π :: ν :: l) ^ j / (j.factorial : Kd)) := by
  intro l
  induction l with
  | nil =>
    intro π ν hok hlt
    simp only [bSteps] at hok
    subst hok
    have h := ((lv_bDel hB hlt).pow j).div (lv_natCast (K := Kd) j.factorial)
      (by exact_mod_cast (Nat.factorial_pos j).ne')
    simp only [bTailProd, bChRho, bChLinks, bChHn]
    refine h.congr (by push_cast; ring) (by ring)
  | cons ν' l ih =>
    intro π ν hok hlt
    obtain ⟨h2, hok'⟩ := hok
    have hR := bR_order hB h2
    have hRv : LV (bR p p' x₀ b ν ν') (1 - ((ν' : ℤ) - ν)) (bRho p p' x₀ b ν ν') :=
      ⟨by unfold OrdGE; rw [hR.1], rfl⟩
    have hlink := (lv_bDel hB hlt).sub (lv_bDel hB h2)
    have hq := hRv.div hlink (bH_link_ne hB hlt h2)
    have hIH := ih ν ν' hok' h2
    have hprod := hq.mul hIH
    simp only [bTailProd]
    refine hprod.congr (by push_cast; ring) ?_
    simp only [bChRho, bChLinks, bChHn]
    field_simp

/-- The leading term of `P^{(k')}_γ δ_{g_n}^j/j!`. -/
theorem b_prod_lead {i k : ℕ} {γ : List ℕ} (hγ : γ ∈ bChains i k) (k' j : ℕ) (hk : 1 ≤ k') :
    LV (bProd p p' x₀ b k' j γ) ((k' : ℤ) + j - (k - i))
      (bChW p p' x₀ b γ * bChH0 p p' x₀ b γ ^ (k' - 1) * bChHn p p' x₀ b γ ^ j /
        (j.factorial : Kd)) := by
  obtain ⟨x, l, rfl, hlt, hok⟩ := b_steps_of_mem hγ
  have hR := bR_order hB hlt
  have hRv : LV (bR p p' x₀ b i x) (1 - ((x : ℤ) - i)) (bRho p p' x₀ b i x) :=
    ⟨by unfold OrdGE; rw [hR.1], rfl⟩
  have hd := (lv_bDel hB hlt).pow (k' - 1)
  have ht := b_tail_lead hB j k l i x hok hlt
  have h := (hRv.mul hd).mul ht
  simp only [bProd]
  refine h.congr ?_ ?_
  · have : ((k' - 1 : ℕ) : ℤ) = (k' : ℤ) - 1 := by omega
    rw [this]; ring
  · simp only [bChW, bChRho, bChH0]
    ring

theorem b_chain_coeff {i k : ℕ} (hik : i < k) (k' j : ℕ) (hk : 1 ≤ k') :
    (bChain p p' x₀ b i k k' j).coeff ((k' : ℤ) + j - (k - i)) =
      ∑ γ ∈ bChains i k, bChW p p' x₀ b γ * bChH0 p p' x₀ b γ ^ (k' - 1) *
        bChHn p p' x₀ b γ ^ j / (j.factorial : Kd) := by
  rw [b_head_bridge hB hik k' j, HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun γ hγ => (b_prod_lead hB hγ k' j hk).2

theorem b_chain_coeff_zero {i k : ℕ} (hik : i < k) (k' j : ℕ) (hk : 1 ≤ k')
    (h : k - i < k' + j) : (bChain p p' x₀ b i k k' j).coeff 0 = 0 := by
  rw [b_head_bridge hB hik k' j, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun γ hγ => ?_
  exact (b_prod_lead hB hγ k' j hk).1.coeff_eq_zero (by omega)

/-- Lemma 8.5(i) at the boundary: the vanishing and the value. -/
theorem b_leading_sums (hreg : Stmt_lem_chain_regular) {i k : ℕ} (hik : i < k) :
    (∀ k' j : ℕ, 1 ≤ k' → k' + j < k - i →
      ∑ γ ∈ bChains i k,
        bChW p p' x₀ b γ * bChH0 p p' x₀ b γ ^ (k' - 1) * bChHn p p' x₀ b γ ^ j = 0) ∧
    (∀ k' j : ℕ, 1 ≤ k' → k' + j = k - i →
      (bChain p p' x₀ b i k k' j).coeff 0 =
        (∑ γ ∈ bChains i k,
          bChW p p' x₀ b γ * bChH0 p p' x₀ b γ ^ (k' - 1) * bChHn p p' x₀ b γ ^ j) /
          (j.factorial : Kd)) := by
  have hb0 := b_ne_zero_of (bSetting_minimal hB)
  have hlev := bLev_strictMono hB hik
  have hfact : ∀ j : ℕ, (j.factorial : Kd) ≠ 0 := fun j => by
    exact_mod_cast (Nat.factorial_pos j).ne'
  refine ⟨fun k' j hk hkj => ?_, fun k' j hk hkj => ?_⟩
  · have hr := hreg b hb0 (bWt p p' x₀ i) (bLev p p' x₀ k - bLev p p' x₀ i) k' j (by omega) hk
    have hz : (bChain p p' x₀ b i k k' j).coeff ((k' : ℤ) + j - (k - i)) = 0 := by
      have hneg : (k' : ℤ) + j - (k - i) < 0 := by omega
      exact (show OrdGE (bChain p p' x₀ b i k k' j) 0 by unfold bChain; simpa [OrdGE] using hr).coeff_eq_zero
        hneg
    rw [b_chain_coeff hB hik k' j hk] at hz
    have : (∑ γ ∈ bChains i k, bChW p p' x₀ b γ * bChH0 p p' x₀ b γ ^ (k' - 1) *
        bChHn p p' x₀ b γ ^ j) / (j.factorial : Kd) = 0 := by
      rw [Finset.sum_div]; exact hz
    rcases div_eq_zero_iff.1 this with h | h
    · exact h
    · exact absurd h (hfact j)
  · have h0 : (k' : ℤ) + j - (k - i) = 0 := by omega
    have := b_chain_coeff hB hik k' j hk
    rw [h0] at this
    rw [this, Finset.sum_div]

theorem b_group_first {i k : ℕ} (φ : ℕ → Kd) :
    ∑ γ ∈ bChains i k, bChW p p' x₀ b γ * φ (γ.tail.headD i) =
      ∑ θ ∈ Finset.Ioc i k, bFsum p p' x₀ b i k θ * φ θ := by
  have hmaps : ∀ γ ∈ bChains i k, (fun γ : List ℕ => γ.tail.headD i) γ ∈ Finset.Ioc i k := by
    intro γ hγ
    obtain ⟨x, l, rfl, hx⟩ := b_chain_first hγ
    simpa using hx
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [bFsum, Finset.sum_mul]
  have hf : (bChains i k).filter (fun γ => γ.tail.headD i = θ) =
      (bChains i k).filter (fun γ => γ.tail.head? = some θ) :=
    Finset.filter_congr fun γ hγ => by
      obtain ⟨x, l, rfl, -⟩ := b_chain_first hγ
      simp
  rw [hf]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨hγ1, hγ2⟩ := Finset.mem_filter.1 hγ
  obtain ⟨x, l, rfl, -⟩ := b_chain_first hγ1
  simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at hγ2
  subst hγ2
  rfl

/-- Lemma 8.5(ii) at the boundary: `F(θ) = Top(a→μ)/∏_{θ' ≠ θ}(h_{aθ} - h_{aθ'})`. -/
theorem b_Fsum_eq (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {i k θ : ℕ}
    (hik : i < k) (hθ : θ ∈ Finset.Ioc i k) :
    bFsum p p' x₀ b i k θ = bTop p p' x₀ b i k /
      ∏ θ' ∈ (Finset.Ioc i k).erase θ, (bH p p' x₀ b i θ - bH p p' x₀ b i θ') := by
  have hreg := lem_chain_regular_of_cited hK hH
  obtain ⟨hs1, hs2⟩ := b_leading_sums hB hreg hik
  have hcard : (Finset.Ioc i k).card = k - i := Nat.card_Ioc i k
  refine moment_lagrange (Finset.Ioc i k) (fun θ => bH p p' x₀ b i θ)
    (fun θ => bFsum p p' x₀ b i k θ) (bTop p p' x₀ b i k)
    (fun x hx y hy h => bH_injOn hB i (Set.mem_Ioi.2 (Finset.mem_Ioc.1 hx).1)
      (Set.mem_Ioi.2 (Finset.mem_Ioc.1 hy).1) h) ?_ θ hθ
  rw [hcard]
  intro m hm
  have hgroup := b_group_first hB (i := i) (k := k) (fun θ => bH p p' x₀ b i θ ^ m)
  have hh0 : ∀ γ ∈ bChains i k, bChH0 p p' x₀ b γ = bH p p' x₀ b i (γ.tail.headD i) := by
    intro γ hγ
    obtain ⟨x, l, rfl, -⟩ := b_chain_first hγ
    rfl
  rw [← Finset.sum_congr rfl (fun γ hγ => by rw [← hh0 γ hγ])] at hgroup
  beta_reduce at hgroup
  rw [← hgroup]
  split_ifs with hmD
  · have h2 := hs2 (m + 1) 0 (by omega) (by omega)
    simp only [Nat.add_sub_cancel, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
      div_one] at h2
    unfold bTop
    rw [show k - i = m + 1 by omega, h2]
  · have h1 := hs1 (m + 1) 0 (by omega) (by omega)
    simpa using h1

theorem b_Fsum_self {i k : ℕ} (hik : i < k) : bFsum p p' x₀ b i k k = bRho p p' x₀ b i k := by
  have hf : (bChains i k).filter (fun γ => γ.tail.head? = some k) = {[i, k]} := by
    ext γ
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      rw [bChains_of_lt hik] at h1
      rcases Finset.mem_union.1 h1 with h | h
      · exact Finset.mem_singleton.1 h
      · obtain ⟨θ', -, h3⟩ := Finset.mem_biUnion.1 h
        obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h3
        obtain ⟨x, l, rfl⟩ := bChains_head hγ'
        simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h2
        exact absurd h2 (by have := (Finset.mem_Ioo.1 θ'.2).2; omega)
    · rintro rfl
      refine ⟨?_, by simp⟩
      rw [bChains_of_lt hik]
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  rw [bFsum, hf, Finset.sum_singleton]
  simp [bChW, bChRho, bChLinks]

/-- Theorem 8.11(i), first form. -/
theorem b_top_eq (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {i k : ℕ}
    (hik : i < k) :
    bTop p p' x₀ b i k =
      bRho p p' x₀ b i k * ∏ m ∈ Finset.Ioo i k, (bH p p' x₀ b i k - bH p p' x₀ b i m) := by
  have h := b_Fsum_eq hB hK hH hik (Finset.mem_Ioc.2 ⟨hik, le_rfl⟩)
  rw [b_Fsum_self hB hik] at h
  have he : (Finset.Ioc i k).erase k = Finset.Ioo i k := by
    rw [← Finset.Ioo_insert_right hik, Finset.erase_insert (by simp)]
  rw [he] at h
  have hne : ∏ m ∈ Finset.Ioo i k, (bH p p' x₀ b i k - bH p p' x₀ b i m) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun m hm e => ?_
    have hm' := Finset.mem_Ioo.1 hm
    have := bH_injOn hB i (Set.mem_Ioi.2 hik) (Set.mem_Ioi.2 hm'.1) (sub_eq_zero.1 e)
    omega
  rw [h, div_mul_cancel₀ _ hne]

/-- The slope differences: `h_{aμ} - h_{aμ_m} = ε ς N₀ T_i (π_k - π_m)`. -/
theorem bH_sub (i k m : ℕ) :
    bH p p' x₀ b i k - bH p p' x₀ b i m =
      pt ((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ) *
        ((bPi k : ℂ) - bPi m)) := by
  unfold bH
  rw [← map_sub]
  congr 1
  have := bT_sub (p := p) (p' := p') (x₀ := x₀) k m
  linear_combination ((bEps p x₀ : ℂ) * varsig p' b * (bT p p' x₀ i : ℂ)) * this

/-- Theorem 8.11(i). -/
theorem b_thm_i (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {i k : ℕ}
    (hik : i < k) :
    bTop p p' x₀ b i k =
        bRho p p' x₀ b i k * ∏ m ∈ Finset.Ioo i k, (bH p p' x₀ b i k - bH p p' x₀ b i m) ∧
      bTop p p' x₀ b i k =
        bRho p p' x₀ b i k *
          pt (((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ)) ^ (k - i - 1) *
            ∏ m ∈ Finset.Ioo i k, ((bPi k : ℂ) - bPi m)) ∧
      bTop p p' x₀ b i k ≠ 0 := by
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  have h1 := b_top_eq hB hK hH hik
  have h2 : bTop p p' x₀ b i k = bRho p p' x₀ b i k *
      pt (((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ)) ^ (k - i - 1) *
        ∏ m ∈ Finset.Ioo i k, ((bPi k : ℂ) - bPi m)) := by
    rw [h1, Finset.prod_congr rfl (fun m _ => bH_sub hB i k m), ← map_prod, Finset.prod_mul_distrib,
      Finset.prod_const, Nat.card_Ioo]
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  refine mul_ne_zero (bR_order hB hik).2 ((map_ne_zero _).2 (mul_ne_zero (pow_ne_zero _ ?_) ?_))
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (bEps_ne hB) (varsig_ne hB))
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne')) (by exact_mod_cast hp'.ne')))
      (by exact_mod_cast bT_ne hB i)
  · refine Finset.prod_ne_zero_iff.2 fun m hm e => ?_
    have hm' := Finset.mem_Ioo.1 hm
    have := bPi_injective (by exact_mod_cast sub_eq_zero.1 e : bPi k = bPi m)
    omega

end Lead

end Virasoro
