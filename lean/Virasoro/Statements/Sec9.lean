import Virasoro.Statements.Sec8
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Frozen statements: Section 9 (The spin-module level-ten diamond)
-/

namespace Virasoro

open Polynomial Module

/-- Proposition 9.1 (`prop:level-ten-smith`).  Let `h₀ = 1/16`, `U₂ = U(Vir_-) χ₂`,
`U₄ = U(Vir_-) χ₄`.  Their intersection is zero below level `10`,
`(U₂ ∩ U₄)₁₀ = ℂ χ₁₀` for a singular vector `χ₁₀`, and `dim ker G₁₀(1/2,h₀) = 32`.  The `42`
local Smith exponents of `G₁₀(1/2,h₀+x)` are `(0¹⁰, 1³¹, 2)`; in particular the inverse
Shapovalov matrix has a nonzero rank-one coefficient at order `x⁻²`. -/
def Stmt_prop_level_ten_smith : Prop :=
  let U₂ := Verma.negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi2)
  let U₄ := Verma.negSpan (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4)
  let G := gramLocal (1 / 2 : ℂ) (1 / 16) 10
  (∃ χ₁₀ : Verma ℂ (1 / 2) (1 / 16), Verma.IsSingular χ₁₀ 10 ∧
    (∀ N : ℕ, N < 10 → U₂ ⊓ U₄ ⊓ Verma.level N = ⊥) ∧
    U₂ ⊓ U₄ ⊓ Verma.level 10 = Submodule.span ℂ {χ₁₀}) ∧
  finrank ℂ (LinearMap.ker (gram (1 / 2 : ℂ) (1 / 16) 10).mulVecLin) = 32 ∧
  IsSmith G (Multiset.replicate 10 0 + Multiset.replicate 31 1 + {2}) ∧
  (invCoeff G (-2)).rank = 1

/-- `𝒫_{4,2}(b₀,d)`. -/
noncomputable def P42 : ℂ[X] :=
  C (1 / 20736) * X * (X - 20) * (X - 13) * (X - 11) * (X - 6) * (X - 1) *
    (2 * X - 57) * (2 * X - 35) * (2 * X - 15) * (2 * X - 7) * (2 * X - 5) * (2 * X - 1) *
    (3 * X - 14) * (3 * X - 5) * (6 * X - 55) * (6 * X - 1)

/-- `𝒫_{1,6}(b₀,d)`. -/
noncomputable def P16 : ℂ[X] :=
  C (1 / 64) * X * (X - 20) * (X - 13) * (X - 11) * (X - 6) * (X - 1) *
    (2 * X - 57) * (2 * X - 35) * (2 * X - 15) * (2 * X - 7) * (2 * X - 5) * (2 * X - 1)

/-- Lemma 9.3 (`lem:level-ten-constants`).  At `b₀ = 2i/√3`:
`𝒜_{1,2} = -4/7`, `𝒜_{2,2} = 648/13475`, `𝒜_{4,2} = 48/32035128125`,
`𝒜_{1,6} = -8/320945625`; `16 ḣ_{r,s}/(i√3) = 9, -7, -71, 105` for
`(r,s) = (1,2), (2,2), (4,2), (1,6)`;
`(ḣ_{1,2}-ḣ_{2,2})/(ḣ_{1,2}-ḣ_{4,2}) = 1/5`, `(ḣ_{2,2}-ḣ_{1,2})/(ḣ_{2,2}-ḣ_{1,6}) = 1/7`,
`1/5 𝒜_{1,2} 𝒜_{4,2} = 1/7 𝒜_{2,2} 𝒜_{1,6} = -192/1121229484375`;
`𝒫_{1,2}(b₀,d) = P₂(d)`, `𝒫_{2,2}(b₀,d) = P₄(d)`, `𝒫_{4,2}(b₀,d)`, `𝒫_{1,6}(b₀,d)` are the
displayed polynomials, and `P₂ 𝒫_{4,2} = P₄ 𝒫_{1,6}`. -/
def Stmt_lem_level_ten_constants : Prop :=
  (genA 1 2 b0 = -4 / 7 ∧ genA 2 2 b0 = 648 / 13475 ∧ genA 4 2 b0 = 48 / 32035128125 ∧
    genA 1 6 b0 = -8 / 320945625) ∧
  (16 * hdot0 1 2 / (Complex.I * (Real.sqrt 3 : ℂ)) = 9 ∧
    16 * hdot0 2 2 / (Complex.I * (Real.sqrt 3 : ℂ)) = -7 ∧
    16 * hdot0 4 2 / (Complex.I * (Real.sqrt 3 : ℂ)) = -71 ∧
    16 * hdot0 1 6 / (Complex.I * (Real.sqrt 3 : ℂ)) = 105) ∧
  ((hdot0 1 2 - hdot0 2 2) / (hdot0 1 2 - hdot0 4 2) = 1 / 5 ∧
    (hdot0 2 2 - hdot0 1 2) / (hdot0 2 2 - hdot0 1 6) = 1 / 7 ∧
    1 / 5 * genA 1 2 b0 * genA 4 2 b0 = -192 / 1121229484375 ∧
    1 / 7 * genA 2 2 b0 * genA 1 6 b0 = -192 / 1121229484375) ∧
  (∀ d : ℂ, genP 1 2 b0 d = P2.eval d ∧ genP 2 2 b0 d = P4.eval d ∧
    genP 4 2 b0 d = P42.eval d ∧ genP 1 6 b0 d = P16.eval d) ∧
  P2 * P42 = P4 * P16

/-- The polynomial `Θ₁₀(d)` of equation (A.2). -/
noncomputable def Theta10 : ℂ[X] :=
  -(C (1 / 552735279561465000000) * X ^ 2 * (X - 1) ^ 2 * (2 * X - 7) ^ 2 * (2 * X - 1) ^ 2 *
      (3 * X - 14) * (3 * X - 5) * (6 * X - 55) * (6 * X - 1) *
      (424640464 * X ^ 8 - 41506307104 * X ^ 7 + 1664502727528 * X ^ 6
        - 35552058801520 * X ^ 5 + 438148123547677 * X ^ 4 - 3142854705332170 * X ^ 3
        + 12488401942129875 * X ^ 2 - 23870935242348750 * X + 14566042731240000))

/-- Theorem 9.4 (`thm:level-ten-principal-part`).  With
`Q₈ = ∂_z{(z-33/16) H₈(1/2,z,d)}|_{z=33/16}`, `Q₆ = ∂_z{(z-65/16) H₆(1/2,z,d)}|_{z=65/16}` and
`Θ₁₀ = T₁ + T₂` the derivative term of Proposition 7.7 for `κ₁ = (1,2)`, `τ₁ = (4,2)`,
`κ₂ = (2,2)`, `τ₂ = (1,6)`, whose factored form is (A.2), the entire principal part of the
level-ten reduced coefficient at `Δ = h₀ = 1/16` is
`PP_{Δ=h₀} H₁₀(1/2,Δ,d) = - 192 P₂ 𝒫_{4,2}(b₀,d) / (1121229484375 (Δ-h₀)²)
   + (-4/7 P₂ Q₈ + 648/13475 P₄ Q₆ + Θ₁₀)/(Δ-h₀)`  (9.1). -/
def Stmt_thm_level_ten_principal_part : Prop :=
  let Q8 : Kd := finitePart (1 / 2) 8 (33 / 16)
  let Q6 : Kd := finitePart (1 / 2) 6 (65 / 16)
  let Θ10 : Kd := Tterm b0 (1, 2) (4, 2) + Tterm b0 (2, 2) (1, 6)
  Θ10 = algebraMap ℂ[X] Kd Theta10 ∧
  PP (HN (1 / 2) 10) (pt (1 / 16)) =
    poleTerm (-(192 * algebraMap ℂ[X] Kd (P2 * P42)) / 1121229484375) (1 / 16) 2 +
    poleTerm (-(4 / 7 : Kd) * algebraMap ℂ[X] Kd P2 * Q8
      + (648 / 13475 : Kd) * algebraMap ℂ[X] Kd P4 * Q6 + Θ10) (1 / 16) 1

/-- The operator `∑_Y q_Y L_{-Y}` of `U(Vir_-)` with level-`N` coordinates `q`. -/
noncomputable def coordOp (c : ℂ) {N : ℕ} (q : Nat.Partition N → ℂ) : VirEnv ℂ c :=
  ∑ Y : Nat.Partition N, q Y • VirEnv.negOp c Y.word

/-- Proposition 9.5 (`thm:level-ten-leading`).  Normalize all singular vectors by setting their
`L_{-1}^ℓ` coefficient equal to `1`, and let `ψ₈ ∈ M(1/2,33/16)`, `ψ₆ ∈ M(1/2,65/16)` be the
singular vectors of levels `8` and `6` (coordinates `q₈`, `q₆`).  Then
`χ₁₀ = j_{χ₂}(ψ₈) = j_{χ₄}(ψ₆)`, `⟨ψ₈|V_d(1)|ψ₈⟩ = 𝒫_{4,2}(b₀,d)`,
`⟨ψ₆|V_d(1)|ψ₆⟩ = 𝒫_{1,6}(b₀,d)`; with `G₁₀(1/2,h₀+x) = G₀ + x G₁ + x² G₂ + O(x³)` and `v₁`
chosen with `G₀ v₁ = - G₁ χ₁₀`, the number `γ₁₀ = χ₁₀ᵀ (G₂ χ₁₀ + G₁ v₁)` is independent of the
choice of `v₁`, `γ₁₀ = -1121229484375/192`, and
`lim_{Δ→h₀} (Δ-h₀)² H₁₀(1/2,Δ,d) = P₂ 𝒫_{4,2}(b₀,d)/γ₁₀ = P₄ 𝒫_{1,6}(b₀,d)/γ₁₀`.
The limit is read as: `H₁₀` has a pole of order at most `2` at `h₀` and its coefficient of
`(Δ-h₀)⁻²` is the stated value; `x₁₀` denotes the level-ten coordinates of `χ₁₀`. -/
def Stmt_thm_level_ten_leading : Prop :=
  ∀ (q₈ : Nat.Partition 8 → ℂ) (q₆ : Nat.Partition 6 → ℂ),
    q₈ (onesPartition 8) = 1 →
    Verma.IsSingular (Verma.pbwCoord (c := (1 / 2 : ℂ)) (h := (33 / 16 : ℂ)) 8 q₈) 8 →
    q₆ (onesPartition 6) = 1 →
    Verma.IsSingular (Verma.pbwCoord (c := (1 / 2 : ℂ)) (h := (65 / 16 : ℂ)) 6 q₆) 6 →
    let χ₁₀ : Verma ℂ (1 / 2) (1 / 16) := coordOp (1 / 2) q₈ • St.toVerma chi2
    let G := gramLocal (1 / 2 : ℂ) (1 / 16) 10
    χ₁₀ = coordOp (1 / 2) q₆ • St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4 ∧
    torusPolyForm (1 / 2) (33 / 16) q₈ = P42 ∧
    torusPolyForm (1 / 2) (65 / 16) q₆ = P16 ∧
    (∃ x₁₀ : Nat.Partition 10 → ℂ, Verma.pbwCoord 10 x₁₀ = χ₁₀ ∧
      (∀ v₁ v₁' : Nat.Partition 10 → ℂ,
        (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec x₁₀ →
        (coeffMat 0 G).mulVec v₁' = -(coeffMat 1 G).mulVec x₁₀ →
        cross2 G x₁₀ x₁₀ v₁ = cross2 G x₁₀ x₁₀ v₁') ∧
      (∀ v₁ : Nat.Partition 10 → ℂ,
        (coeffMat 0 G).mulVec v₁ = -(coeffMat 1 G).mulVec x₁₀ →
        cross2 G x₁₀ x₁₀ v₁ = -1121229484375 / 192)) ∧
    poleOrder (HN (1 / 2) 10) (pt (1 / 16)) ≤ 2 ∧
    ppCoeff (HN (1 / 2) 10) (pt (1 / 16)) 2 =
      algebraMap ℂ[X] Kd (P2 * P42) / (-1121229484375 / 192) ∧
    ppCoeff (HN (1 / 2) 10) (pt (1 / 16)) 2 =
      algebraMap ℂ[X] Kd (P4 * P16) / (-1121229484375 / 192)

end Virasoro
