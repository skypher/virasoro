import Virasoro.Proofs.Sec8DiagValues

/-!
# Lemma 8.7(ii), first part: `w_γ = Top(a→μ) (ς N₀ S_a)^{1-D} ℓ(γ)`

`ℓ(γ)` is a rational number determined by the positions of the nodes of `γ`:
`ℓ([a, μ]) = 1/Π₁(a,μ)` and `ℓ(a, θ, x₂, …) = κ̂(a,θ,μ)/(Π₁(a,θ)(π_{x₂} - π_a)) ℓ(θ, x₂, …)`, with
`Π₁(a,θ) = ∏_{x ∈ FS(a→θ), x ≠ θ} (π_x - π_θ)`.  The proof is the paper's: `ρ_{g_i}` from the proof
of Proposition 8.6, and Proposition 8.6 along the chain.
-/

namespace Virasoro

open scoped LaurentSeries

/-- `Π₁(a,θ) = ∏_{x ∈ FS(a→θ), x ≠ θ} (π_x - π_θ)`. -/
def Pi1 (a θ : Node) : ℚ := ∏ x ∈ (firstSteps a θ).erase θ, (nodePos x - nodePos θ)

/-- The rational number `ℓ(γ)` of a chain ending at `μ`. -/
def ellC (μ : Node) : List Node → ℚ
  | [a, x] => 1 / Pi1 a x
  | a :: θ :: x₂ :: rest =>
      kappaHat a θ μ / (Pi1 a θ * (nodePos x₂ - nodePos a)) * ellC μ (θ :: x₂ :: rest)
  | _ => 0

theorem chainW_alg {K : Type*} [Field K] {u v κ ℓ P Δ ρ : K} (n m : ℕ) (hu : u ≠ 0)
    (hv : v ≠ 0) (hP : P ≠ 0) (hΔ : Δ ≠ 0) (hρ : ρ = v / u) :
    ρ ^ (m + 1) * κ * (ℓ / v ^ m * (v * Δ)⁻¹ / (u ^ n * P)) =
      κ / (P * Δ) * ℓ / u ^ (n + (m + 1)) := by
  subst hρ
  rw [div_pow, pow_add, pow_succ, pow_succ]
  field_simp
  ring

variable {p p' r s : ℕ} {b : ℂ}

theorem nodeH_sub_same {a θ x : Node} (h : x.2 % 2 = θ.2 % 2) :
    nodeH p p' r s b a θ - nodeH p p' r s b a x =
      pt (varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p') *
        (((nodePos x : ℚ) : ℂ) - ((nodePos θ : ℚ) : ℂ))) := by
  have hs := nodeS_sub (p := p) (p' := p') (r := r) (s := s) h
  unfold nodeH
  rw [← map_sub]
  congr 1
  linear_combination (varsig p' b * (nodeS p p' r s a : ℂ)) * hs

theorem nodeH_sub_link {a θ x : Node} (h : x.2 % 2 = a.2 % 2) :
    nodeH p p' r s b a θ - nodeH p p' r s b θ x =
      pt (varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p') *
        (((nodePos x : ℚ) : ℂ) - ((nodePos a : ℚ) : ℂ))) := by
  have hs := nodeS_sub (p := p) (p' := p') (r := r) (s := s) h
  unfold nodeH
  rw [← map_sub]
  congr 1
  linear_combination (varsig p' b * (nodeS p p' r s θ : ℂ)) * hs

theorem nodePos_ne {x y : Node} (h : y.2 < x.2) : nodePos x ≠ nodePos y := by
  have key : ∀ z : Node, nodePos z = (z.2 : ℚ) / 2 ∨ nodePos z = -((z.2 : ℚ) / 2) := fun z => by
    unfold nodePos; split_ifs <;> simp
  have h1 : (y.2 : ℚ) < x.2 := by exact_mod_cast h
  have h0 : (0 : ℚ) ≤ y.2 := by positivity
  intro e
  rcases key x with hx | hx <;> rcases key y with hy | hy <;> rw [hx, hy] at e <;> linarith

/-- The chains of a node: one label, or a first step `θ ≠ μ` followed by a chain from `θ`. -/
theorem chains_cases {a μ : Node} {γ : List Node} (hγ : γ ∈ nodeChains a μ) :
    a.2 < μ.2 ∧ ((γ = [a, μ] ∧ (μ.2 - a.2) % 2 = 1) ∨
      ∃ θ ∈ firstSteps a μ, θ ≠ μ ∧ ∃ γ' ∈ nodeChains θ μ, γ = a :: γ') := by
  rcases Nat.lt_or_ge a.2 μ.2 with h | h
  · refine ⟨h, ?_⟩
    rw [nodeChains_of_lt h] at hγ
    rcases Finset.mem_union.1 hγ with h1 | h1
    · split_ifs at h1 with ho
      · exact Or.inl ⟨Finset.mem_singleton.1 h1, ho⟩
      · simp at h1
    · obtain ⟨θ, -, h2⟩ := Finset.mem_biUnion.1 h1
      obtain ⟨γ', hγ', rfl⟩ := Finset.mem_image.1 h2
      have hθ := Finset.mem_filter.1 θ.2
      exact Or.inr ⟨θ.1, hθ.1, hθ.2, γ', hγ', rfl⟩
  · rw [nodeChains_of_le h] at hγ; simp at hγ

theorem chainW_one (a μ : Node) : chainW p p' r s b [a, μ] = nodeRho p p' r s b a μ := by
  simp [chainW, chainRho, chainLinks]

theorem chainW_cons (a θ x : Node) (l : List Node) :
    chainW p p' r s b (a :: θ :: x :: l) = nodeRho p p' r s b a θ * chainW p p' r s b (θ :: x :: l) *
      (nodeH p p' r s b a θ - nodeH p p' r s b θ x)⁻¹ := by
  rw [show chainW p p' r s b (a :: θ :: x :: l) =
      nodeRho p p' r s b a θ * chainRho p p' r s b (θ :: x :: l) /
        ((nodeH p p' r s b a θ - nodeH p p' r s b θ x) * chainLinks p p' r s b (θ :: x :: l)) from rfl,
    chainW, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

section Ell

variable (hset : MinimalSetting p p' r s b)
include hset

/-- `∏_{x ∈ FS(a→θ), x ≠ θ} (h_{aθ} - h_{ax}) = (ς S_a N₀)^{D(a,θ)-1} Π₁(a,θ)`. -/
theorem P1_eq {a θ : Node} (haθ : a.2 < θ.2) (hodd : (θ.2 - a.2) % 2 = 1) :
    ∏ x ∈ (firstSteps a θ).erase θ, (nodeH p p' r s b a θ - nodeH p p' r s b a x) =
      pt ((varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (θ.2 - a.2 - 1) *
        ((Pi1 a θ : ℚ) : ℂ)) := by
  have hθself : θ ∈ firstSteps a θ := mem_firstSteps.2 (Or.inr ⟨hodd, rfl⟩)
  have hd : ∀ x ∈ (firstSteps a θ).erase θ, nodeH p p' r s b a θ - nodeH p p' r s b a x =
      pt (varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p') *
        (((nodePos x : ℚ) : ℂ) - ((nodePos θ : ℚ) : ℂ))) := by
    intro x hx
    obtain ⟨h1, h1o⟩ := firstSteps_props (Finset.mem_erase.1 hx).2
    exact nodeH_sub_same (by omega)
  rw [Finset.prod_congr rfl hd, ← map_prod, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem hθself, firstSteps_card haθ]
  simp only [Pi1, Rat.cast_prod, Rat.cast_sub]

theorem P1_ne {a θ : Node} (haθ : a.2 < θ.2) (hodd : (θ.2 - a.2) % 2 = 1) :
    ∏ x ∈ (firstSteps a θ).erase θ, (nodeH p p' r s b a θ - nodeH p p' r s b a x) ≠ 0 := by
  have hθself : θ ∈ firstSteps a θ := mem_firstSteps.2 (Or.inr ⟨hodd, rfl⟩)
  refine Finset.prod_ne_zero_iff.2 fun x hx e => ?_
  have hx' := Finset.mem_erase.1 hx
  exact hx'.1 (nodeH_injOn hset haθ hx'.2 hθself (sub_eq_zero.1 e).symm)

theorem Pi1_ne {a θ : Node} (haθ : a.2 < θ.2) (hodd : (θ.2 - a.2) % 2 = 1) :
    ((Pi1 a θ : ℚ) : ℂ) ≠ 0 := by
  have h := P1_ne hset haθ hodd
  rw [P1_eq hset haθ hodd] at h
  intro h0
  apply h
  rw [h0, mul_zero]
  exact map_zero _

/-- `w_γ = Top(a→μ) ℓ(γ)/(ς S_a N₀)^{D-1}` for every chain `γ` from `a` to `μ`. -/
theorem chainW_eq (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    ∀ n : ℕ, ∀ a μ : Node, μ.2 - a.2 = n → ∀ γ ∈ nodeChains a μ,
      chainW p p' r s b γ = nodeTop p p' r s b a μ *
        pt (((ellC μ γ : ℚ) : ℂ) /
          (varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (μ.2 - a.2 - 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a μ hn γ hγ
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb0 := b_ne_zero_of hset
  have hσ : varsig p' b ≠ 0 := by
    unfold varsig
    exact div_ne_zero hb0 (mul_ne_zero two_ne_zero (pow_ne_zero 2 (by exact_mod_cast hp'.ne')))
  have hN : (2 * (p : ℂ) * p') ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne')) (by exact_mod_cast hp'.ne')
  have hSa : (nodeS p p' r s a : ℂ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset a
  have hu : varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p') ≠ 0 :=
    mul_ne_zero (mul_ne_zero hσ hSa) hN
  obtain ⟨haμ, hc⟩ := chains_cases hγ
  rcases hc with ⟨rfl, hodd⟩ | ⟨θ, hθ, hθμ, γ', hγ', rfl⟩
  · rw [chainW_one, rho_eq hK hH hset haμ hodd, P1_eq hset haμ hodd, div_eq_mul_inv, ← map_inv₀]
    congr 2
    have hP := Pi1_ne hset haμ hodd
    simp only [ellC]
    push_cast
    rw [mul_inv]
    ring
  · obtain ⟨haθ, hodd⟩ := firstSteps_props hθ
    have hθμ2 : θ.2 < μ.2 := by
      rcases mem_firstSteps.1 hθ with ⟨-, h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd h hθμ
    obtain ⟨x, l, rfl, hx⟩ := chain_first hγ'
    obtain ⟨hθx, hθxo⟩ := firstSteps_props hx
    have IH := ih (μ.2 - θ.2) (by omega) θ μ rfl (θ :: x :: l) hγ'
    have hSθ : (nodeS p p' r s θ : ℂ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset θ
    have hv : varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p') ≠ 0 :=
      mul_ne_zero (mul_ne_zero hσ hSθ) hN
    have hP := Pi1_ne hset haθ hodd
    have hΔ : ((nodePos x : ℚ) : ℂ) - ((nodePos a : ℚ) : ℂ) ≠ 0 :=
      sub_ne_zero.2 (by exact_mod_cast nodePos_ne (show a.2 < x.2 by omega))
    have htop := top_identity hK hH hset hθ hθμ
    rw [← map_ratCast (RatFunc.C : ℂ →+* Kd)] at htop
    rw [chainW_cons, IH, rho_eq hK hH hset haθ hodd, P1_eq hset haθ hodd,
      nodeH_sub_link (show x.2 % 2 = a.2 % 2 by omega)]
    obtain ⟨m, hm⟩ : ∃ m, μ.2 - θ.2 = m + 1 := ⟨μ.2 - θ.2 - 1, by omega⟩
    have hq : (((topFac p p' r s a θ μ : ℚ) : ℂ)) =
        ((nodeS p p' r s θ : ℂ) / (nodeS p p' r s a : ℂ)) ^ (m + 1) * ((kappaHat a θ μ : ℚ) : ℂ) := by
      unfold topFac
      rw [hm]
      push_cast
      ring
    calc nodeTop p p' r s b a θ /
          pt ((varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (θ.2 - a.2 - 1) *
            ((Pi1 a θ : ℚ) : ℂ)) *
          (nodeTop p p' r s b θ μ * pt (((ellC μ (θ :: x :: l) : ℚ) : ℂ) /
            (varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p')) ^ (μ.2 - θ.2 - 1))) *
          (pt (varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p') *
            (((nodePos x : ℚ) : ℂ) - ((nodePos a : ℚ) : ℂ))))⁻¹
        = (nodeTop p p' r s b a θ * nodeTop p p' r s b θ μ) *
            pt ((((ellC μ (θ :: x :: l) : ℚ) : ℂ) /
              (varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p')) ^ (μ.2 - θ.2 - 1)) *
              (varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p') *
                (((nodePos x : ℚ) : ℂ) - ((nodePos a : ℚ) : ℂ)))⁻¹ /
              ((varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (θ.2 - a.2 - 1) *
                ((Pi1 a θ : ℚ) : ℂ))) := by
          simp only [pt, map_div₀, map_mul, map_inv₀, map_pow]
          ring
      _ = nodeTop p p' r s b a μ * pt (((topFac p p' r s a θ μ : ℚ) : ℂ) *
            ((((ellC μ (θ :: x :: l) : ℚ) : ℂ) /
              (varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p')) ^ (μ.2 - θ.2 - 1)) *
              (varsig p' b * nodeS p p' r s θ * (2 * (p : ℂ) * p') *
                (((nodePos x : ℚ) : ℂ) - ((nodePos a : ℚ) : ℂ)))⁻¹ /
              ((varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (θ.2 - a.2 - 1) *
                ((Pi1 a θ : ℚ) : ℂ)))) := by
          rw [htop]
          simp only [pt, map_div₀, map_mul, map_inv₀, map_pow]
          ring
      _ = nodeTop p p' r s b a μ *
            pt (((ellC μ (a :: θ :: x :: l) : ℚ) : ℂ) /
              (varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (μ.2 - a.2 - 1)) := by
          congr 2
          rw [hq, show μ.2 - θ.2 - 1 = m by omega,
            show μ.2 - a.2 - 1 = (θ.2 - a.2 - 1) + (m + 1) by omega]
          rw [show ellC μ (a :: θ :: x :: l) = kappaHat a θ μ /
              (Pi1 a θ * (nodePos x - nodePos a)) * ellC μ (θ :: x :: l) from rfl]
          push_cast
          have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
          have hp'C : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
          exact chainW_alg (θ.2 - a.2 - 1) m hu hv hP hΔ
            (by first | (field_simp; ring) | field_simp)

end Ell

end Virasoro
