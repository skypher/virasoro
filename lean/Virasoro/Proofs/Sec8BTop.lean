import Virasoro.Proofs.Sec8BLead
import Virasoro.Proofs.Sec8DiagTop

/-!
# Section 8.2: Proposition 8.6 at the boundary

`Top(μ_i→μ_θ) Top(μ_θ→μ_k) = (T_θ/T_i)^{k-θ} κ̂(i,θ,k) Top(μ_i→μ_k)` for `i < θ < k`, with
`κ̂(i,θ,k) = ∏_{θ<x≤k} (π_x - π_i)/(π_x - π_θ)`: the proof of Proposition 8.6 with `FS(θ→μ) = (θ,k]`
and `FS(a→μ) ∖ FS(a→θ) = (θ,k]`.
-/

namespace Virasoro

open scoped LaurentSeries

/-- `κ̂(i,θ,k) = ∏_{θ<x≤k} (π_x - π_i) / ∏_{θ<x≤k} (π_x - π_θ)`. -/
def bKappa (i θ k : ℕ) : ℚ :=
  (∏ x ∈ Finset.Ioc θ k, ((bPi x : ℚ) - bPi i)) / ∏ x ∈ Finset.Ioc θ k, ((bPi x : ℚ) - bPi θ)

/-- `κ(i,θ,k) = (T_θ/T_i)^{k-θ} κ̂(i,θ,k)`. -/
def bKfac (p p' x₀ : ℕ) (i θ k : ℕ) : ℚ :=
  ((bT p p' x₀ θ : ℚ) / bT p p' x₀ i) ^ (k - θ) * bKappa i θ k

theorem ratio_alg {c Tθ Ti A B : ℂ} (n : ℕ) (hc : c ≠ 0) (hTi : Ti ≠ 0)
    (hB : B ≠ 0) : (-(c * Tθ)) ^ n * A / ((-(c * Ti)) ^ n * B) = (Tθ / Ti) ^ n * (A / B) := by
  have hY : (-(c * Ti)) ^ n * B ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (mul_ne_zero hc hTi))) hB
  have hcn : c ^ n ≠ 0 := pow_ne_zero _ hc
  have htn : Ti ^ n ≠ 0 := pow_ne_zero _ hTi
  have h1 : ((-1 : ℂ)) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_eq_iff hY, neg_pow (c * Tθ), neg_pow (c * Ti), mul_pow c Tθ, mul_pow c Ti, div_pow,
    div_mul_div_comm, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero htn hB)]
  ring

variable {p p' x₀ : ℕ} {b : ℂ}

theorem bChW_cons (a θ x : ℕ) (l : List ℕ) :
    bChW p p' x₀ b (a :: θ :: x :: l) = bRho p p' x₀ b a θ * bChW p p' x₀ b (θ :: x :: l) *
      (bH p p' x₀ b a θ - bH p p' x₀ b θ x)⁻¹ := by
  rw [show bChW p p' x₀ b (a :: θ :: x :: l) =
      bRho p p' x₀ b a θ * bChRho p p' x₀ b (θ :: x :: l) /
        ((bH p p' x₀ b a θ - bH p p' x₀ b θ x) * bChLinks p p' x₀ b (θ :: x :: l)) from rfl,
    bChW, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

theorem b_chains_filter_step {i k θ : ℕ} (hik : i < k) (hθ : θ ∈ Finset.Ioo i k) :
    (bChains i k).filter (fun γ => γ.tail.head? = some θ) = (bChains θ k).image (i :: ·) := by
  have hθk := (Finset.mem_Ioo.1 hθ).2
  ext γ
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    rw [bChains_of_lt hik] at h1
    rcases Finset.mem_union.1 h1 with h | h
    · rw [Finset.mem_singleton.1 h] at h2
      simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h2
      omega
    · obtain ⟨θ', -, h3⟩ := Finset.mem_biUnion.1 h
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h3
      obtain ⟨x, l, rfl⟩ := bChains_head hγ'
      simp only [List.tail_cons, List.head?_cons, Option.some.injEq] at h2
      subst h2
      exact ⟨_, hγ', rfl⟩
  · rintro ⟨γ', hγ', rfl⟩
    refine ⟨?_, ?_⟩
    · rw [bChains_of_lt hik]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨⟨θ, hθ⟩, Finset.mem_attach _ _,
        Finset.mem_image.2 ⟨γ', hγ', rfl⟩⟩)
    · obtain ⟨x, l, rfl⟩ := bChains_head hγ'
      simp

section Top

variable (hB : BoundarySetting p p' x₀ b)
include hB

theorem b_Fsum_rec {i k θ : ℕ} (hik : i < k) (hθ : θ ∈ Finset.Ioo i k) :
    bFsum p p' x₀ b i k θ = bRho p p' x₀ b i θ *
      ∑ θ' ∈ Finset.Ioc θ k, bFsum p p' x₀ b θ k θ' /
        (bH p p' x₀ b i θ - bH p p' x₀ b θ θ') := by
  rw [bFsum, b_chains_filter_step hik hθ,
    Finset.sum_image (fun x _ y _ h => List.cons_injective h)]
  simp_rw [div_eq_mul_inv]
  rw [← b_group_first hB (i := θ) (k := k)
    (fun θ' => (bH p p' x₀ b i θ - bH p p' x₀ b θ θ')⁻¹), Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ' hγ' => ?_
  obtain ⟨x, l, rfl, -⟩ := b_chain_first hγ'
  simp only [List.tail_cons, List.headD_cons]
  rw [bChW_cons]
  ring

theorem bH_sub_link (i θ x : ℕ) :
    bH p p' x₀ b i θ - bH p p' x₀ b θ x =
      pt (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ)) *
        ((bPi x : ℂ) - bPi i)) := by
  unfold bH
  rw [← map_sub]
  congr 1
  have := bT_sub (p := p) (p' := p') (x₀ := x₀) x i
  linear_combination (-(bEps p x₀ : ℂ) * varsig p' b * (bT p p' x₀ θ : ℂ)) * this

theorem bH_sub_same (i θ x : ℕ) :
    bH p p' x₀ b i θ - bH p p' x₀ b i x =
      pt (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ)) *
        ((bPi x : ℂ) - bPi θ)) := by
  rw [bH_sub hB i θ x]
  congr 1
  ring

/-- Proposition 8.6 at the boundary. -/
theorem b_top_identity (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {i θ k : ℕ}
    (h1 : i < θ) (h2 : θ < k) :
    bTop p p' x₀ b i θ * bTop p p' x₀ b θ k =
      ((bKfac p p' x₀ i θ k : ℚ) : Kd) * bTop p p' x₀ b i k := by
  have hik : i < k := h1.trans h2
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  have hθ : θ ∈ Finset.Ioo i k := Finset.mem_Ioo.2 ⟨h1, h2⟩
  have hθ' : θ ∈ Finset.Ioc i k := Finset.mem_Ioc.2 ⟨h1, h2.le⟩
  -- the product over `(i,k] ∖ {θ}` splits into `(i,θ)` and `(θ,k]`
  have hsplit : ∏ x ∈ (Finset.Ioc i k).erase θ, (bH p p' x₀ b i θ - bH p p' x₀ b i x) =
      (∏ x ∈ Finset.Ioc θ k, (bH p p' x₀ b i θ - bH p p' x₀ b i x)) *
        ∏ x ∈ (Finset.Ioc i θ).erase θ, (bH p p' x₀ b i θ - bH p p' x₀ b i x) := by
    rw [← Finset.prod_union]
    · congr 1
      ext x
      simp only [Finset.mem_erase, Finset.mem_Ioc, Finset.mem_union]
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_erase, Finset.mem_Ioc] at hx hx'
      omega
  have hinj := bH_injOn hB (p := p) (p' := p') (x₀ := x₀) (b := b)
  have hP1 : ∏ x ∈ (Finset.Ioc i θ).erase θ, (bH p p' x₀ b i θ - bH p p' x₀ b i x) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun x hx e => ?_
    simp only [Finset.mem_erase, Finset.mem_Ioc] at hx
    exact hx.1 (hinj i (Set.mem_Ioi.2 hx.2.1) (Set.mem_Ioi.2 h1) (sub_eq_zero.1 e).symm)
  have hP3 : ∏ x ∈ Finset.Ioc θ k, (bH p p' x₀ b i θ - bH p p' x₀ b i x) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun x hx e => ?_
    simp only [Finset.mem_Ioc] at hx
    have := hinj i (Set.mem_Ioi.2 (h1.trans hx.1)) (Set.mem_Ioi.2 h1) (sub_eq_zero.1 e).symm
    omega
  have hz : ∀ θ' ∈ Finset.Ioc θ k, bH p p' x₀ b i θ ≠ bH p p' x₀ b θ θ' := by
    intro θ' hθ'' e
    simp only [Finset.mem_Ioc] at hθ''
    have := sub_eq_zero.2 e
    rw [bH_sub_link hB] at this
    have h0 := RatFunc.C_injective (this.trans (map_zero _).symm)
    rcases mul_eq_zero.1 h0 with h | h
    · apply neg_ne_zero.2 _ h
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (bEps_ne hB) (varsig_ne hB))
        (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne'))
          (by exact_mod_cast hp'.ne'))) (by exact_mod_cast bT_ne hB θ)
    · have := bPi_injective (by exact_mod_cast sub_eq_zero.1 h : bPi θ' = bPi i)
      omega
  have hP2 : ∏ θ' ∈ Finset.Ioc θ k, (bH p p' x₀ b i θ - bH p p' x₀ b θ θ') ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun θ' h => sub_ne_zero.2 (hz θ' h)
  have hne : (Finset.Ioc θ k).Nonempty := ⟨k, Finset.mem_Ioc.2 ⟨h2, le_rfl⟩⟩
  have hF2 := b_Fsum_rec hB hik hθ
  have hF3 : ∀ θ' ∈ Finset.Ioc θ k, bFsum p p' x₀ b θ k θ' /
        (bH p p' x₀ b i θ - bH p p' x₀ b θ θ') =
      bTop p p' x₀ b θ k /
        (∏ θ'' ∈ (Finset.Ioc θ k).erase θ', (bH p p' x₀ b θ θ' - bH p p' x₀ b θ θ'')) /
        (bH p p' x₀ b i θ - bH p p' x₀ b θ θ') := by
    intro θ' hθ''
    rw [b_Fsum_eq hB hK hH h2 hθ'']
  have hpf : ∑ θ' ∈ Finset.Ioc θ k, bTop p p' x₀ b θ k /
        (∏ θ'' ∈ (Finset.Ioc θ k).erase θ', (bH p p' x₀ b θ θ' - bH p p' x₀ b θ θ'')) /
        (bH p p' x₀ b i θ - bH p p' x₀ b θ θ') =
      bTop p p' x₀ b θ k / ∏ θ' ∈ Finset.Ioc θ k, (bH p p' x₀ b i θ - bH p p' x₀ b θ θ') :=
    partial_frac (Finset.Ioc θ k) (fun θ' => bH p p' x₀ b θ θ') (bH p p' x₀ b i θ)
      (bTop p p' x₀ b θ k)
      (fun x hx y hy h => hinj θ (Set.mem_Ioi.2 (Finset.mem_Ioc.1 hx).1)
        (Set.mem_Ioi.2 (Finset.mem_Ioc.1 hy).1) h) hne hz
  have hrho : bRho p p' x₀ b i θ = bTop p p' x₀ b i θ /
      ∏ x ∈ (Finset.Ioc i θ).erase θ, (bH p p' x₀ b i θ - bH p p' x₀ b i x) := by
    rw [← b_Fsum_self hB h1]
    exact b_Fsum_eq hB hK hH h1 (Finset.mem_Ioc.2 ⟨h1, le_rfl⟩)
  rw [Finset.sum_congr rfl hF3, hpf, hrho] at hF2
  have key := hF2
  rw [b_Fsum_eq hB hK hH hik hθ', hsplit] at key
  have hmain := top_alg hP1 hP2 hP3 key
  -- the ratio of the two products
  obtain ⟨n, hn⟩ : ∃ n, n = k - θ := ⟨_, rfl⟩
  have hcard : (Finset.Ioc θ k).card = n := by rw [Nat.card_Ioc, hn]
  have hP2e : ∏ θ' ∈ Finset.Ioc θ k, (bH p p' x₀ b i θ - bH p p' x₀ b θ θ') =
      pt ((-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ))) ^ n *
        ∏ x ∈ Finset.Ioc θ k, ((bPi x : ℂ) - bPi i)) := by
    rw [Finset.prod_congr rfl (fun x _ => bH_sub_link hB i θ x), ← map_prod,
      Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have hP3e : ∏ x ∈ Finset.Ioc θ k, (bH p p' x₀ b i θ - bH p p' x₀ b i x) =
      pt ((-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ))) ^ n *
        ∏ x ∈ Finset.Ioc θ k, ((bPi x : ℂ) - bPi θ)) := by
    rw [Finset.prod_congr rfl (fun x _ => bH_sub_same hB i θ x), ← map_prod,
      Finset.prod_mul_distrib, Finset.prod_const, hcard]
  have hBne : ∏ x ∈ Finset.Ioc θ k, ((bPi x : ℂ) - bPi θ) ≠ 0 := by
    intro h0; apply hP3; rw [hP3e, h0, mul_zero]; exact map_zero _
  have hq : (∏ θ' ∈ Finset.Ioc θ k, (bH p p' x₀ b i θ - bH p p' x₀ b θ θ')) /
        (∏ x ∈ Finset.Ioc θ k, (bH p p' x₀ b i θ - bH p p' x₀ b i x)) =
      ((bKfac p p' x₀ i θ k : ℚ) : Kd) := by
    rw [hP2e, hP3e, ← map_div₀, ← map_ratCast (RatFunc.C : ℂ →+* Kd)]
    congr 1
    unfold bKfac bKappa
    rw [← hn]
    push_cast
    have hc : (bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') ≠ 0 :=
      mul_ne_zero (mul_ne_zero (bEps_ne hB) (varsig_ne hB))
        (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne')) (by exact_mod_cast hp'.ne'))
    have hTi : (bT p p' x₀ i : ℂ) ≠ 0 := by exact_mod_cast bT_ne hB i
    exact ratio_alg n hc hTi hBne
  rw [← hq]
  exact hmain

end Top

end Virasoro
