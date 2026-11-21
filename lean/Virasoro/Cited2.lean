import Virasoro.Statements.Sec10

/-!
# Results cited from the literature: additions for `paper.tex` at 70bac53

Cited inputs first used by Sections 9–13 of the torus paper.  They are kept apart from
`Virasoro/Cited.lean` because that module is imported by the proofs of the earlier results.
Each `Cited_*` proposition records a result that the paper uses without proof; theorems that
depend on one of them take it as an explicit hypothesis.
-/

namespace Virasoro

open Polynomial

/-- Existence of the two-weight three-point pairing.
Source: L. Hadasz, Z. Jaskólski and P. Suchanek, JHEP 01 (2010) 063, Section 3, p. 4 (the
normalized three-point block of three Verma modules), as quoted in the proof of Lemma 10.1
(paper.tex l.2081–2085): for all `c, Δ₁, Δ₂, d` there is a bilinear form on
`M(c,Δ₁) × M(c,Δ₂)` with value `1` on the highest-weight vectors that satisfies the Ward
identity (10.1). -/
def Cited_TwoWeightPairingExists : Prop :=
  ∀ c Δ₁ Δ₂ d : ℂ, ∃ T : Verma ℂ c Δ₁ →ₗ[ℂ] Verma ℂ c Δ₂ →ₗ[ℂ] ℂ, Verma.IsTwoWeightPairing d T

/-- The normalized singular vector `χ_{R,S}(b)` has PBW coefficients in `ℚ[b²,b⁻²]`.
Source: A. Astashkevich, Comm. Math. Phys. 186 (1997), Theorem 3.1, composed with the Laurent
expressions of `(c,h)` in `t = b²`; see also Iohara–Koga (2011), Propositions 5.1–5.2 and
Corollary 5.2 (proof of Proposition 10.2(i), paper.tex l.2149–2152). -/
def Cited_SingularFamilyLaurent : Prop :=
  ∀ R S : ℕ, 0 < R → 0 < S →
    ∀ p : Nat.Partition (R * S) → RatFunc ℚ, p (onesPartition (R * S)) = 1 →
      Verma.IsSingular
        (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH R S RatFunc.X)
          (R * S) p) (R * S) →
      ∀ Y, ∃ (f : ℚ[X]) (n : ℕ),
        p Y = Polynomial.aeval ((RatFunc.X : RatFunc ℚ) ^ 2) f / RatFunc.X ^ (2 * n)

/-- Zamolodchikov's fusion polynomial.
Source: Al. Zamolodchikov (2004), Section 5, equations (5.9)–(5.12); see also
Hadasz–Jaskólski–Suchanek (2010), Section 3, equations (7)–(9) (proof of Proposition 10.2(ii),
paper.tex l.2152–2155).  For `b ≠ 0` and a singular vector `χ` of level `RS` in
`M(c(b),h_{R,S}(b))` with `L_{-1}^{RS}`-coefficient `1`,
`ρ_{h_{R,S}(b),Δ₁;Δ₂}(χ, v_{Δ₁}) = C_{R,S}(b) P_{R,S}(b;Δ₁,Δ₂)` with `C_{R,S}(b) ≠ 0`
independent of `(Δ₁,Δ₂)`. -/
def Cited_FusionPolynomial : Prop :=
  ∀ R S : ℕ, 0 < R → 0 < S → ∀ b : ℂ, b ≠ 0 →
    ∀ x : Nat.Partition (R * S) → ℂ, x (onesPartition (R * S)) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH R S b) (R * S) x) (R * S) →
      ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ (Δ₁ Δ₂ : ℂ)
        (T : Verma ℂ (kacC b) (kacH R S b) →ₗ[ℂ] Verma ℂ (kacC b) Δ₁ →ₗ[ℂ] ℂ),
        Verma.IsTwoWeightPairing Δ₂ T →
          T (Verma.pbwCoord (R * S) x) Verma.hw = C₀ * fusP R S b Δ₁ Δ₂

/-- The Jantzen layers at every weight of the braided orbit of an interior Kac weight.
Sources: A. Astashkevich (1997), Theorem A(a), (b)(iii), (c) and Theorem B(e) (Class `III₋`);
Iohara–Koga (2011), Proposition 5.4, Figure 5.4 and Theorem 6.3 (proof of Lemma 10.3(i),
paper.tex l.2232–2239).  For `μ = μ^ε_k` in the orbit and `i ≥ 1`:
`J^i(c⋆,μ) = M(c⋆,μ⁺_{k+i}) + M(c⋆,μ⁻_{k+i})`, the two submodules meet in `J^{i+1}(c⋆,μ)`, and
`J^i/J^{i+1} ≅ L(c⋆,μ⁺_{k+i}) ⊕ L(c⋆,μ⁻_{k+i})`; the last clause is recorded as in
`Stmt_lem_bgg_arrows`: each `U(Vir_-) w^±_i / J^{i+1}` is simple. -/
def Cited_JantzenLayersOrbit : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k : ℕ),
    ∃ wp wm : ℕ → Verma ℂ (kacC b) (muOrb p p' r s ε k),
      OrbitLayerSetting p p' r s b ε k wp wm ∧
      ∀ i : ℕ, 1 ≤ i →
        Verma.negSpan (wp i) ⊓ Verma.negSpan (wm i) =
          jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∧
        Verma.negSpan (wp i) ≠ jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∧
        Verma.negSpan (wm i) ≠ jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∧
        ∀ W : Submodule ℂ (Verma ℂ (kacC b) (muOrb p p' r s ε k)), Verma.IsVirSubmodule W →
          jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ≤ W →
            (W ≤ Verma.negSpan (wp i) →
              W = jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∨ W = Verma.negSpan (wp i)) ∧
            (W ≤ Verma.negSpan (wm i) →
              W = jantzen (kacC b) (muOrb p p' r s ε k) (i + 1) ∨ W = Verma.negSpan (wm i))

end Virasoro
