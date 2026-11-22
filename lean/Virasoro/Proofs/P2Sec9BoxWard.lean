import Virasoro.Proofs.P2Sec9BoxPoly
import Virasoro.Proofs.P2Sec9Descent
import Virasoro.Proofs.Singular

/-!
# Theorem 9.2: the factorization of `f_d(x₁,0)` (paper.tex l.2644–2670)

Restricted to `M(c,Δ₁) × U(Vir_-)χ`, the two-weight form satisfies the Ward identity between
`M(c,Δ₁)` and `M(c,h+ℓ)`; by the uniqueness of Lemma 10.1 it is a multiple of the normalized
form, and Proposition 10.2(ii) evaluates both factors.
-/

namespace Virasoro.P2

open Virasoro Polynomial

/-- A bilinear form that satisfies the Ward identity (10.1) is its value at the highest-weight
vectors times the normalized form (uniqueness in Lemma 10.1). -/
theorem ward_scalar {c h₁ h₂ d : ℂ} {T W : Verma ℂ c h₁ →ₗ[ℂ] Verma ℂ c h₂ →ₗ[ℂ] ℂ}
    (hT : Verma.IsTwoWeightPairing d T)
    (hW : ∀ (n : ℤ) (u : Verma ℂ c h₁) (v : Verma ℂ c h₂),
      W (Verma.L (-n) u) v - W u (Verma.L n v) =
        W (Verma.L 0 u) v - W u (Verma.L 0 v) + (n : ℂ) * d * W u v)
    (u : Verma ℂ c h₁) (v : Verma ℂ c h₂) : W u v = W Verma.hw Verma.hw * T u v := by
  have h1 : Verma.IsTwoWeightPairing d (W + (1 - W Verma.hw Verma.hw) • T) := by
    refine ⟨?_, fun n u v => ?_⟩
    · simp [hT.1]
    · have e1 := hW n u v
      have e2 := hT.2 n u v
      simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      linear_combination e1 + (1 - W Verma.hw Verma.hw) * e2
  have h2 := Verma.twoWeight_unique h1 hT
  have h3 : (W + (1 - W Verma.hw Verma.hw) • T) u v = T u v := by rw [h2]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h3
  linear_combination h3

/-- The factorization of l.2653–2663: for a singular vector `χ` of level `ℓ` in `M(c,h)`,
`ρ_{Δ₁,h;d}(u,χ) = ρ_{Δ₁,h;d}(v_{Δ₁},χ) ρ_{Δ₁,h+ℓ;d}(u,v_{h+ℓ})`. -/
theorem ward_factor {c h Δ₁ d : ℂ} {ℓ : ℕ} {χ : Verma ℂ c h} (hχ : Verma.IsSingular χ ℓ)
    {T : Verma ℂ c Δ₁ →ₗ[ℂ] Verma ℂ c h →ₗ[ℂ] ℂ} (hT : Verma.IsTwoWeightPairing d T)
    {T' : Verma ℂ c Δ₁ →ₗ[ℂ] Verma ℂ c (h + ℓ) →ₗ[ℂ] ℂ} (hT' : Verma.IsTwoWeightPairing d T')
    (u : Verma ℂ c Δ₁) : T u χ = T Verma.hw χ * T' u Verma.hw := by
  obtain ⟨j, hjhw, hjL, -⟩ := Verma.exists_singularHom hχ.2.1 hχ.2.2
  have h := ward_scalar hT' (W := T.compl₂ j) (fun n u v => by
    simp only [LinearMap.compl₂_apply, hjL]
    exact hT.2 n u (j v)) u Verma.hw
  simpa only [LinearMap.compl₂_apply, hjhw] using h

/-- The two evaluations of l.2664–2675: with `χ = 𝒪 v_{h}` singular of level `RS` in
`M(c(b),h)`, `h = h_{R,S}(b)`, there is `κ ≠ 0`, independent of `(Δ₁,d)`, such that
`f_d(Δ₁,h) = κ P_{R,S}(b;Δ₁,d) ρ_{Δ₁,h+RS;d}(𝒪 v_{Δ₁}, v_{h+RS})` and
`ρ_{h,h+RS;d}(χ, v_{h+RS}) = κ P_{R,S}(b;h+RS,d)`. -/
theorem box_ward (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) {b : ℂ} (hb : b ≠ 0) {R S : ℕ}
    (hR : 0 < R) (hS : 0 < S) (x : Nat.Partition (R * S) → ℂ)
    (hx : Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x) (R * S)) :
    ∃ κ : ℂ, κ ≠ 0 ∧
      (∀ Δ₁ d : ℂ, MvPolynomial.eval ![Δ₁, kacH R S b] (twoPoly (kacC b) d x) =
        κ * fusP R S b Δ₁ d *
          tw1Form (kacC b) Δ₁ (kacH R S b + ((R * S : ℕ) : ℂ)) d x) ∧
      ∀ d : ℂ, tw1Form (kacC b) (kacH R S b) (kacH R S b + ((R * S : ℕ) : ℂ)) d x =
        κ * fusP R S b (kacH R S b + ((R * S : ℕ) : ℂ)) d := by
  obtain ⟨p, ⟨hp1, hsing⟩, -⟩ := hH R S hR hS
  obtain ⟨-, h1, hs1, -, -⟩ := lem_regular_everywhere_of_cited hH R S hR hS p hp1 hsing b hb
  obtain ⟨a, ha⟩ := hU _ _ (R * S) _ _ hs1 hx
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hx.1 (ha.trans (by module))
  obtain ⟨C₀, hC0, hC⟩ := hF R S hR hS b hb _ h1 hs1
  have key : ∀ (Δ₁ d : ℂ) (Tf : Verma ℂ (kacC b) (kacH R S b) →ₗ[ℂ] Verma ℂ (kacC b) Δ₁ →ₗ[ℂ] ℂ),
      Verma.IsTwoWeightPairing d Tf →
        Tf (Verma.pbwCoord (R * S) x) Verma.hw = a * C₀ * fusP R S b Δ₁ d := by
    intro Δ₁ d Tf hTf
    rw [ha, map_smul, LinearMap.smul_apply, hC Δ₁ d Tf hTf, smul_eq_mul, mul_assoc]
  refine ⟨a * C₀, mul_ne_zero ha0 hC0, fun Δ₁ d => ?_, fun d => ?_⟩
  · obtain ⟨T, hT⟩ := hE (kacC b) Δ₁ (kacH R S b) d
    obtain ⟨T', hT'⟩ := hE (kacC b) Δ₁ (kacH R S b + ((R * S : ℕ) : ℂ)) d
    obtain ⟨Tf, hTf⟩ := hE (kacC b) (kacH R S b) Δ₁ d
    rw [eval_twoPoly, ← twoWeight_pbwCoord hT, ward_factor hx hT hT',
      twoWeight_pbwCoord_hw hT',
      (lem_two_weight_ward_of_cited hE).2.2.1 _ _ _ d T Tf hT hTf, key Δ₁ d Tf hTf]
  · obtain ⟨T', hT'⟩ := hE (kacC b) (kacH R S b) (kacH R S b + ((R * S : ℕ) : ℂ)) d
    rw [← twoWeight_pbwCoord_hw hT', key _ d T' hT']

end Virasoro.P2
