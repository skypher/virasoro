import Virasoro.Proofs.P2Sec13Complement

/-!
# Lemma 13.1 from Step 4 (paper.tex l.2990–3028)

Steps 2 and 3 of the proof of Lemma 13.1 are proved (`sub_tau_kernel_lift_of_cited`,
`sub_tau_lattice_of_cited`, `sub_tau_depth_one_of_cited`).  This module composes them with
Step 4 (`Stmt_sub_tau_diag_limit`) and freezes the first part of Step 4, the second line of
equation (13.3) with the value of the ratio (l.2972–2977, 3012–3023).
-/

namespace Virasoro.P2

open Virasoro Verma PowerSeries

/-- `Stmt_sub_tau_trace_limit` from Step 4. -/
theorem sub_tau_trace_limit_of_diag (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hI : Cited_VermaHomInjective)
    (h4 : Stmt_sub_tau_diag_limit) : Stmt_sub_tau_trace_limit :=
  sub_tau_trace_limit_of_subs hH (sub_tau_lattice_of_cited hK hE hH hU hF hLau hI) h4

/-- Lemma 13.1 from Step 4 of its proof. -/
theorem lem_degenerate_quotient_t_of_diag (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hI : Cited_VermaHomInjective)
    (h4 : Stmt_sub_tau_diag_limit) : Stmt_lem_degenerate_quotient_t :=
  lem_degenerate_quotient_t_of_trace hK hE hH hU hF hI
    (sub_tau_trace_limit_of_diag hK hE hH hU hF hLau hI h4)

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hI : Cited_VermaHomInjective)
    (h4 : Stmt_sub_tau_diag_limit) : Stmt_lem_degenerate_quotient_t :=
  lem_degenerate_quotient_t_of_diag hK hE hH hU hF hLau hI h4

/-- Equation (13.3), second line, with the value of the ratio (l.2972–2977, 3012–3023): for the
two arrows `μ → ν₁` (label `(R₁,S₁)`), `μ → ν₂` (label `(R₂,S₂)`) and every lift `V₂` over
`ℂ⟦X⟧` of the singular vector `χ_{R₂,S₂}(b⋆)`,
`[X¹] ρ_X(V₂,V₂) = Ω_{u,v}(μ→ν₂) · [X¹] B_X(V₂,V₂)` on `M(c(X),h_{R₁,S₁}(X))`, with
`d(X) = h_{2k+1,2m+1}(b⋆+X)`: both coefficients are `[X¹](Δ₁-Δ₂)` times
`g̃_ρ(t₀,μ)`, `γ_{R₂,S₂}(b⋆)`, whose ratio is `c_{R₂,S₂}(t₀;u,v) = Ω_{u,v}(μ→ν₂)`
(Theorem 9.2 at `t = t₀` with Proposition 12.1(i)).

Demand sheet: `MinimalSetting`; `(k,m)` in the fusion box; node `μ^ε_{k₀}`, `ν₁` of sign `ε₁`,
`ν₂` of sign `!ε₁` in the layer `k₀+1`, labels `arrowLabel`; every singular vector of level
`R₂S₂` at `b⋆` (in coordinates); every lift (l.3000–3003: the coefficient does not depend on
the lift); the ratio is stated cross-multiplied with `[X¹] B_X(V₂,V₂)`, which is nonzero by
`Stmt_sub_tau_deriv_chain`; the value is `cArrow`. -/
def Stmt_sub_tau_ratio : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      ∀ (ε : Bool) (k₀ : ℕ) (ε₁ : Bool) (R₁ S₁ R₂ S₂ : ℕ),
        arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε₁ (k₀ + 1)) =
            ((R₁ : ℤ), (S₁ : ℤ)) →
        arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s (!ε₁) (k₀ + 1)) =
            ((R₂ : ℤ), (S₂ : ℤ)) →
          ∀ x₂ : Nat.Partition (R₂ * S₂) → ℂ,
            Verma.IsSingular
              (Verma.pbwCoord (c := kacC b) (h := kacH R₂ S₂ b) (R₂ * S₂) x₂) (R₂ * S₂) →
            ∀ V₂ : Nat.Partition (R₂ * S₂) → ℂ⟦X⟧, (∀ Y, constantCoeff (V₂ Y) = x₂ Y) →
              coeff 1 (V₂ ⬝ᵥ (torus (cLoc b) (hLoc R₁ S₁ b)
                  (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (R₂ * S₂)).mulVec V₂) =
                (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ) *
                  coeff 1 (V₂ ⬝ᵥ (gram (cLoc b) (hLoc R₁ S₁ b) (R₂ * S₂)).mulVec V₂)

end Virasoro.P2
