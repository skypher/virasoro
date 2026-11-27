import Virasoro.Proofs.Sec8BVals
import Virasoro.Proofs.Sec8DiagMoments

/-!
# Section 8.2: Lemma 8.7(ii) at the boundary

`w_γ = Top(μ_i→μ_k) ℓ(γ)/(-ε ς N₀ T_i)^{D-1}` with `ℓ(γ)` rational from the positions (the signs
`ε` collect in the prefactor), and the moment argument: `f_j(i,k) = (-1)^{D-1} ∑_γ ℓ(γ) π_{x₁}^{D-1-j}
π_{x_n}^j`, `f_0 = 1`, with `j! (T_i/T_k)^j c^{(D-j)}_{μ_i→μ_k,j}(b⋆) = f_j(i,k) Top(μ_i→μ_k)`.
-/

namespace Virasoro

open scoped LaurentSeries

/-- `Π₁(a,θ) = ∏_{a<x<θ} (π_x - π_θ)`. -/
def bPi1 (a θ : ℕ) : ℚ := ∏ x ∈ Finset.Ioo a θ, ((bPi x : ℚ) - bPi θ)

/-- `ℓ(γ)` for a boundary chain ending at `k`. -/
def bEll (k : ℕ) : List ℕ → ℚ
  | [a, x] => 1 / bPi1 a x
  | a :: θ :: y₂ :: rest => bKappa a θ k / (bPi1 a θ * ((bPi y₂ : ℚ) - bPi a)) * bEll k (θ :: y₂ :: rest)
  | _ => 0

/-- The last layer before the end of a chain. -/
def bPenult : List ℕ → ℕ
  | [y₀, _] => y₀
  | _ :: l => bPenult l
  | [] => 0

/-- `f_j(i,k)` at the boundary. -/
def fValB (i k j : ℕ) : ℚ :=
  if j = 0 then 1 else
    (-1) ^ (k - i - 1) * ∑ γ ∈ bChains i k,
      bEll k γ * (bPi (γ.tail.headD i) : ℚ) ^ (k - i - 1 - j) * (bPi (bPenult γ) : ℚ) ^ j

variable {p p' x₀ : ℕ} {b : ℂ}

theorem bChW_one (a k : ℕ) : bChW p p' x₀ b [a, k] = bRho p p' x₀ b a k := by
  simp [bChW, bChRho, bChLinks]

theorem b_chains_cases {i k : ℕ} {γ : List ℕ} (hγ : γ ∈ bChains i k) :
    i < k ∧ (γ = [i, k] ∨ ∃ θ ∈ Finset.Ioo i k, ∃ γ' ∈ bChains θ k, γ = i :: γ') := by
  rcases Nat.lt_or_ge i k with h | h
  · refine ⟨h, ?_⟩
    rw [bChains_of_lt h] at hγ
    rcases Finset.mem_union.1 hγ with h1 | h1
    · exact Or.inl (Finset.mem_singleton.1 h1)
    · obtain ⟨θ, -, h2⟩ := Finset.mem_biUnion.1 h1
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h2
      exact Or.inr ⟨θ.1, θ.2, γ', hγ', rfl⟩
  · rw [bChains_of_le h] at hγ; simp at hγ

theorem bPi1_ne {a θ : ℕ} : ((bPi1 a θ : ℚ) : ℂ) ≠ 0 := by
  unfold bPi1
  push_cast
  refine Finset.prod_ne_zero_iff.2 fun x hx e => ?_
  have hx' := Finset.mem_Ioo.1 hx
  have := bPi_injective (by exact_mod_cast sub_eq_zero.1 e : bPi x = bPi θ)
  omega

theorem bPi_sub_ne {x a : ℕ} (h : x ≠ a) : ((bPi x : ℂ) - bPi a) ≠ 0 := by
  rw [sub_ne_zero]; intro e
  exact h (bPi_injective (by exact_mod_cast e))

section Ell

variable (hB : BoundarySetting p p' x₀ b)
include hB

/-- `∏_{a<x<θ} (h_{aθ} - h_{ax}) = (-ε ς N₀ T_a)^{D(a,θ)-1} Π₁(a,θ)`. -/
theorem bP1_eq {a θ : ℕ} (haθ : a < θ) :
    ∏ x ∈ (Finset.Ioc a θ).erase θ, (bH p p' x₀ b a θ - bH p p' x₀ b a x) =
      pt ((-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ a : ℂ))) ^ (θ - a - 1) *
        ((bPi1 a θ : ℚ) : ℂ)) := by
  rw [← Finset.Ioo_insert_right haθ, Finset.erase_insert (by simp),
    Finset.prod_congr rfl (fun x _ => bH_sub_same hB a θ x), ← map_prod, Finset.prod_mul_distrib,
    Finset.prod_const, Nat.card_Ioo]
  simp only [bPi1, Rat.cast_prod, Rat.cast_sub, Rat.cast_intCast]

theorem b_rho_eq (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) {a θ : ℕ}
    (haθ : a < θ) :
    bRho p p' x₀ b a θ = bTop p p' x₀ b a θ /
      ∏ x ∈ (Finset.Ioc a θ).erase θ, (bH p p' x₀ b a θ - bH p p' x₀ b a x) := by
  rw [← b_Fsum_self hB haθ]
  exact b_Fsum_eq hB hK hH haθ (Finset.mem_Ioc.2 ⟨haθ, le_rfl⟩)

/-- `w_γ = Top(a→μ) ℓ(γ)/(-ε ς N₀ T_a)^{D-1}`. -/
theorem bChW_eq (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    ∀ n : ℕ, ∀ a k : ℕ, k - a = n → ∀ γ ∈ bChains a k,
      bChW p p' x₀ b γ = bTop p p' x₀ b a k *
        pt (((bEll k γ : ℚ) : ℂ) /
          (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ a : ℂ))) ^ (k - a - 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a k hn γ hγ
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  have hc : (bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') ≠ 0 :=
    mul_ne_zero (mul_ne_zero (bEps_ne hB) (varsig_ne hB))
      (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne')) (by exact_mod_cast hp'.ne'))
  have hu : -((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ a : ℂ)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero hc (by exact_mod_cast bT_ne hB a))
  obtain ⟨hak, hcase⟩ := b_chains_cases hγ
  rcases hcase with rfl | ⟨θ, hθ, γ', hγ', rfl⟩
  · rw [bChW_one, b_rho_eq hB hK hH hak, bP1_eq hB hak, div_eq_mul_inv, ← map_inv₀]
    congr 2
    have hP := bPi1_ne (a := a) (θ := k)
    simp only [bEll]
    push_cast
    rw [mul_inv]
    ring
  · obtain ⟨haθ, hθk⟩ := Finset.mem_Ioo.1 hθ
    obtain ⟨x, l, rfl, hx⟩ := b_chain_first hγ'
    obtain ⟨hθx, -⟩ := Finset.mem_Ioc.1 hx
    have IH := ih (k - θ) (by omega) θ k rfl (θ :: x :: l) hγ'
    have hv : -((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ)) ≠ 0 :=
      neg_ne_zero.2 (mul_ne_zero hc (by exact_mod_cast bT_ne hB θ))
    have hP := bPi1_ne (a := a) (θ := θ)
    have hΔ : ((bPi x : ℚ) : ℂ) - ((bPi a : ℚ) : ℂ) ≠ 0 := by
      push_cast; exact bPi_sub_ne (by omega)
    have htop := b_top_identity hB hK hH haθ hθk
    rw [← map_ratCast (RatFunc.C : ℂ →+* Kd)] at htop
    rw [bChW_cons, IH, b_rho_eq hB hK hH haθ, bP1_eq hB haθ, bH_sub_link hB a θ x]
    obtain ⟨m, hm⟩ : ∃ m, k - θ = m + 1 := ⟨k - θ - 1, by omega⟩
    have hq : (((bKfac p p' x₀ a θ k : ℚ) : ℂ)) =
        ((bT p p' x₀ θ : ℂ) / (bT p p' x₀ a : ℂ)) ^ (m + 1) * ((bKappa a θ k : ℚ) : ℂ) := by
      unfold bKfac; rw [hm]; push_cast; ring
    calc bTop p p' x₀ b a θ /
          pt ((-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ a : ℂ))) ^
            (θ - a - 1) * ((bPi1 a θ : ℚ) : ℂ)) *
          (bTop p p' x₀ b θ k * pt (((bEll k (θ :: x :: l) : ℚ) : ℂ) /
            (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ))) ^
              (k - θ - 1))) *
          (pt (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ)) *
            ((bPi x : ℂ) - bPi a)))⁻¹
        = (bTop p p' x₀ b a θ * bTop p p' x₀ b θ k) *
            pt ((((bEll k (θ :: x :: l) : ℚ) : ℂ) /
              (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ))) ^
                (k - θ - 1)) *
              (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ)) *
                ((bPi x : ℂ) - bPi a))⁻¹ /
              ((-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ a : ℂ))) ^
                (θ - a - 1) * ((bPi1 a θ : ℚ) : ℂ))) := by
          simp only [pt, map_div₀, map_mul, map_inv₀, map_pow, map_neg]
          ring
      _ = bTop p p' x₀ b a k * pt (((bKfac p p' x₀ a θ k : ℚ) : ℂ) *
            ((((bEll k (θ :: x :: l) : ℚ) : ℂ) /
              (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ))) ^
                (k - θ - 1)) *
              (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ θ : ℂ)) *
                ((bPi x : ℂ) - bPi a))⁻¹ /
              ((-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ a : ℂ))) ^
                (θ - a - 1) * ((bPi1 a θ : ℚ) : ℂ)))) := by
          rw [htop]
          simp only [pt, map_div₀, map_mul, map_inv₀, map_pow, map_neg]
          ring
      _ = bTop p p' x₀ b a k *
            pt (((bEll k (a :: θ :: x :: l) : ℚ) : ℂ) /
              (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ a : ℂ))) ^
                (k - a - 1)) := by
          congr 2
          rw [hq, show k - θ - 1 = m by omega,
            show k - a - 1 = (θ - a - 1) + (m + 1) by omega]
          rw [show bEll k (a :: θ :: x :: l) = bKappa a θ k /
              (bPi1 a θ * ((bPi x : ℚ) - bPi a)) * bEll k (θ :: x :: l) from rfl]
          have hΔ' : (bPi x : ℂ) - bPi a ≠ 0 := bPi_sub_ne (by omega)
          push_cast
          have hTa : (bT p p' x₀ a : ℂ) ≠ 0 := by exact_mod_cast bT_ne hB a
          have hε := bEps_ne hB
          have hσ := varsig_ne hB
          have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
          have hp'C : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
          exact chainW_alg (θ - a - 1) m hu hv (by push_cast at hP; exact hP) hΔ'
            (by field_simp)

end Ell

end Virasoro
