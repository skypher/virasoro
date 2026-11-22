import Virasoro.Proofs.P2Sec9Main
import Virasoro.Proofs.P2Sec10FusRoots
import Virasoro.Proofs.TopLayerArith

/-!
# Proposition 11.2(i), base case `i = 0` (paper.tex l.2412–2421)

`J¹(c⋆,μ) = U(Vir_-)w⁺_{k₀+1} + U(Vir_-)w⁻_{k₀+1}`, where each primitive singular vector has a
Kac label `(R,S)` with `R ≥ min(r,p-r) > k` and `S ≥ min(s,p'-s) > m`
(Lemma 10.3(i)–(iii)).  By Proposition 10.2(ii), `P_{R,S}(b⋆;μ,h_{2k+1,2m+1}(b⋆)) = 0`, so
`ρ⁽⁰⁾(w^±_{k₀+1},v_μ) = 0`, and the Ward-induction fact gives `J¹(c⋆,μ) ⊂ rad ρ⁽⁰⁾`.
-/

namespace Virasoro

open Verma

variable {p p' r s : ℕ}

/-- Paper equation (10.6) for the levels: `4pp'·ℓ^ε_k = (n^ε_k)² - n₀²`. -/
theorem four_ellOrb (hr : r < p) (hs : s < p') (ε : Bool) (k : ℕ) :
    4 * (p : ℤ) * p' * (ellOrb p p' r s ε k : ℤ) =
      nOrb p p' r s ε k ^ 2 - ((p' : ℤ) * r - p * s) ^ 2 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · have e : ellOrb p p' r s ε (2 * 0) = 0 := by simp [ellOrb]
      rw [e]
      cases ε
      · rw [nOrb_even_false]; push_cast; ring
      · rw [nOrb_even_true]; push_cast; ring
    · have hk : 2 * j ≠ 0 := by omega
      cases ε
      · have e : ellOrb p p' r s false (2 * j) = ellMinus p p' r s (2 * j) := by
          unfold ellOrb; rw [if_neg hk]; simp
        rw [e, ellMinus_even_cast hr j, nOrb_even_false]; ring
      · have e : ellOrb p p' r s true (2 * j) = ellPlus p p' r s (2 * j) := by
          unfold ellOrb; rw [if_neg hk]; simp
        rw [e, ellPlus_even_cast hs j, nOrb_even_true]; ring
  · have hk : 2 * j + 1 ≠ 0 := by omega
    cases ε
    · have e : ellOrb p p' r s false (2 * j + 1) = ellMinus p p' r s (2 * j + 1) := by
        unfold ellOrb; rw [if_neg hk]; simp
      rw [e, ellMinus_odd_cast hr hs j, nOrb_odd_false]; ring
    · have e : ellOrb p p' r s true (2 * j + 1) = ellPlus p p' r s (2 * j + 1) := by
        unfold ellOrb; rw [if_neg hk]; simp
      rw [e, ellPlus_odd_cast j, nOrb_odd_true]; ring

/-- The level of the primitive arrow `μ^ε_k → μ^{ε'}_{k+1}` with Kac label `(R,S)` is `RS`. -/
theorem arrow_level (hp : 0 < p) (hp' : 0 < p') (hr : r < p) (hs : s < p') (ε : Bool) (k : ℕ)
    (ε' : Bool) {R S : ℕ} (hsum : (p' : ℤ) * R + p * S = nOrb p p' r s ε' (k + 1))
    (hdiff : (p' : ℤ) * R - p * S = nOrb p p' r s ε k ∨
      (p' : ℤ) * R - p * S = -nOrb p p' r s ε k) :
    ellOrb p p' r s ε' (k + 1) - ellOrb p p' r s ε k = R * S := by
  have h1 := four_ellOrb hr hs ε' (k + 1)
  have h2 := four_ellOrb hr hs ε k
  have hsq : nOrb p p' r s ε k ^ 2 = ((p' : ℤ) * R - p * S) ^ 2 := by
    rcases hdiff with h | h <;> rw [h] <;> ring
  have hpos : (0 : ℤ) < 4 * p * p' := by
    have : (0 : ℤ) < p := by exact_mod_cast hp
    have : (0 : ℤ) < p' := by exact_mod_cast hp'
    positivity
  have h4 : 4 * (p : ℤ) * p' * ((ellOrb p p' r s ε' (k + 1) : ℤ) - ellOrb p p' r s ε k) =
      4 * (p : ℤ) * p' * ((R : ℤ) * S) := by
    rw [mul_sub, h1, h2, hsq, ← hsum]; ring
  have h5 := mul_left_cancel₀ hpos.ne' h4
  have hN : ellOrb p p' r s ε k + R * S = ellOrb p p' r s ε' (k + 1) := by
    have : ((ellOrb p p' r s ε k + R * S : ℕ) : ℤ) = (ellOrb p p' r s ε' (k + 1) : ℕ) := by
      push_cast; linarith
    exact_mod_cast this
  rw [← hN]
  exact Nat.add_sub_cancel_left _ _

/-- `Stmt_sub_vertex_radical_zero` (paper.tex l.2412–2421) from the cited Jantzen layers of the
orbit, the normalization identities, uniqueness of singular vectors and the fusion polynomial
(Proposition 10.2(ii)). -/
theorem sub_vertex_radical_zero (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) : Stmt_sub_vertex_radical_zero := by
  intro p p' r s b hset ε k₀ k m hk hm T hT u hu v
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  obtain ⟨wp, wm, ⟨hsing, hlayer⟩, -⟩ := hJ p p' r s b hset ε k₀
  obtain ⟨hwp, hwm⟩ := hsing 1 le_rfl
  have hzero : ∀ (ε' : Bool) (w : Verma ℂ (kacC b) (muOrb p p' r s ε k₀)),
      IsSingular w (ellOrb p p' r s ε' (k₀ + 1) - ellOrb p p' r s ε k₀) →
        ∀ x ∈ negSpan w, ∀ y, T x y = 0 ∧ T y x = 0 := by
    intro ε' w hw
    obtain ⟨R, S, hR, hS, hsum, hdiff, hcR, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε k₀ ε'
    have hμ : muOrb p p' r s ε k₀ = kacH R S b := by
      rw [kacH_momWt hp hp' hb, muOrb]
      rcases hdiff with h | h
      · rw [h]
      · rw [h, momWt_neg]
    rw [arrow_level hp hp' hr hs ε k₀ ε' hsum hdiff] at hw
    have hRk := min_le_of_congr hcR
    have hSm := min_le_of_congr hcS
    have h0 : T w Verma.hw = 0 := by
      rw [pairing_singular_fus hH hU hF hb0 hR hS _ hμ _ T hT w hw, hμ, fusP_roots]
      exact ⟨2 * k + 1, mem_oddsBelow.2 ⟨by omega, by omega⟩, 2 * m + 1,
        mem_oddsBelow.2 ⟨by omega, by omega⟩, by push_cast; rfl⟩
    exact Verma.ward_induction hT.2 (primary_symm hT) hw h0
  rw [hlayer 1 le_rfl, Submodule.mem_sup] at hu
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu
  have k1 := hzero true (wp 1) hwp u₁ hu₁ v
  have k2 := hzero false (wm 1) hwm u₂ hu₂ v
  constructor
  · rw [map_add, LinearMap.add_apply, k1.1, k2.1, add_zero]
  · rw [map_add, k1.2, k2.2, add_zero]

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) : Stmt_sub_vertex_radical_zero :=
  sub_vertex_radical_zero hJ hH hU hF

end Virasoro
