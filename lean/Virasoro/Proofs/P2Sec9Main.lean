import Virasoro.Proofs.P2Sec9Descent

/-!
# Theorem 9.1 (fusion-descent and exact Verma regularity): assembly (paper.tex l.2554–2606)

Injectivity is Lemma 11.1(ii) and part (i) is `descent_iff_of_cited`.  The remaining steps of
the paper's proof are recorded as the sub-statements below.
-/

namespace Virasoro

open Polynomial

/-- "so `𝒯^irr_{c⋆,λ,d}(q)` is well-defined" (Theorem 9.1(i), paper.tex l.1857–1858): when
`ρ(c⋆,λ,d)` descends to `L(c⋆,λ) × L(c⋆,λ)`, each coefficient `T^irr_N(c⋆,λ,d)` exists and is
unique.

Demand sheet: the setting of Theorem 9.1 (no labelling condition); every complex `d` with
descent; every `N ≥ 0`; existence and uniqueness of `T` with `IsIrrTrace` (the trace does not
depend on the basis of `L(c⋆,λ)_N`). -/
def Stmt_sub_irr_trace_unique : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → b ^ 2 = -(p' : ℂ) / p →
    0 < r → r < p → 0 < s → s < p' →
    ∀ d : ℂ, TorusDescends (kacC b) (kacH r s b) d →
      ∀ N : ℕ, ∃! T : ℂ, IsIrrTrace (kacC b) (kacH r s b) d N T

/-- The converse half of Theorem 9.1(ii), paper.tex l.2578–2606: if `d ∉ ℱ^±_{p,p'}(r,s)` then
`F_N(c⋆,Δ,d)` has a pole at `Δ = λ` for `N = ℓ_min` or `N = ℓ_max` (Lemma 11.1(iii),
Lemma 10.3(iv) and the top-layer residue formula of Theorem 5.9).

Demand sheet: the setting of Theorem 9.1; every complex `d` outside `ℱ^±`; some level `N` with
nonzero pole order of `Frat c⋆ d N` at `λ` (the paper names `N ∈ {ℓ_min, ℓ_max}`; the consumer
uses only the existence of a level). -/
def Stmt_sub_pole_outside : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → b ^ 2 = -(p' : ℂ) / p →
    0 < r → r < p → 0 < s → s < p' →
    ∀ d : ℂ, d ∉ fusionSetPM p p' r s b →
      ∃ N : ℕ, poleOrder (Frat (kacC b) d N) (kacH r s b) ≠ 0

/-- "and hence regularity of `F_N(c⋆,Δ,d)` at `Δ = μ`" (paper.tex l.2570–2574): for
`d = h_{2k+1,ε(2m+1)}(b⋆) ∈ ℱ^±`, joint regularity at `(b⋆,μ)` (Lemma 11.3) gives pole order
zero of `F_N(c⋆,Δ,d)` at every orbit weight `μ`.

Demand sheet: the setting of Theorem 9.1; all `(k,m)` in the fusion box and both signs; all
orbit weights; all `N`; pole order `0` of `Frat c⋆ d N` over `ℂ`. -/
def Stmt_sub_orbit_regular : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), 2 ≤ p → 2 ≤ p' → Nat.Coprime p p' → b ^ 2 = -(p' : ℂ) / p →
    0 < r → r < p → 0 < s → s < p' →
    ∀ (k m : ℕ) (ε : Bool), k < min r (p - r) → m < min s (p' - s) →
      ∀ μ ∈ orbitSet p p' r s, ∀ N : ℕ,
        poleOrder
          (Frat (kacC b) (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) b) N) μ = 0

/-- First step of the proof of Lemma 11.3, paper.tex l.2508–2540: over `ℚ(b)`, the denominator
of `F_N(c(b),Δ,d(b))`, `d(b) = h_{2k+1,ε(2m+1)}(b)`, divides
`∏_{(R,S) ∈ 𝒦_N} (Δ - h_{R,S}(b))`, `𝒦_N = {(R,S) : RS ≤ N, R ≤ k or S ≤ m}`, up to a power
of `b`: the product of `F_N` with `b^e ∏_{𝒦_N} (Δ - h_{R,S}(b))` is a polynomial in `(b,Δ)`.

Demand sheet: every `k, m`, both signs, every `N` (no condition on `(k,m)`: the cancellation of
the inactive factors holds identically in `b`, l.2527–2533); coefficients in `ℂ` (the paper's
`ℚ` after extension of scalars, as in `JointRegular`); the exponent `e` is existential (the
consumer evaluates at `b⋆ ≠ 0`). -/
def Stmt_sub_joint_denominator : Prop :=
  ∀ (k m : ℕ) (ε : Bool) (N : ℕ), ∃ (e : ℕ) (P : Polynomial (Polynomial ℂ)),
    Frat (kacC (RatFunc.X : RatFunc ℂ))
        (kacH (2 * (k : ℤ) + 1) (sgnInt ε (2 * (m : ℤ) + 1)) (RatFunc.X : RatFunc ℂ)) N *
      (RatFunc.C ((RatFunc.X : RatFunc ℂ) ^ e) *
        ∏ a ∈ (labels N).filter (fun a => a.1 ≤ k ∨ a.2 ≤ m),
          (RatFunc.X - RatFunc.C (kacHL a (RatFunc.X : RatFunc ℂ)))) =
      algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))

/-- Base case of Proposition 11.2(i), paper.tex l.2412–2421: for every orbit weight `μ` and
`d = h_{2k+1,2m+1}(b⋆) ∈ ℱ_{p,p'}(r,s)`, `J¹(c⋆,μ) ⊂ rad ρ_{c⋆,μ,d}`.

Demand sheet: `MinimalSetting`; every node `μ^ε_{k₀}`; `(k,m)` in the fusion box; every primary
pairing of weight `d` on `M(c⋆,μ)`; both slots. -/
def Stmt_sub_vertex_radical_zero : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (ε : Bool) (k₀ k m : ℕ),
    k < min r (p - r) → m < min s (p' - s) →
      ∀ T : Verma ℂ (kacC b) (muOrb p p' r s ε k₀) →ₗ[ℂ]
          Verma ℂ (kacC b) (muOrb p p' r s ε k₀) →ₗ[ℂ] ℂ,
        Verma.IsPrimaryPairing (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) T →
          ∀ u ∈ jantzen (kacC b) (muOrb p p' r s ε k₀) 1, ∀ v, T u v = 0 ∧ T v u = 0

/-- Step 1 of the proof of Lemma 13.1 (generic-`τ` splitting, equation (13.2)), paper.tex
l.2883–2913: for generic `b`, `R, S ≥ 1`, `k < R`, `m < S`, `d = h_{2k+1,2m+1}(b)`,
`F_N(c(b),h_{R,S}(b),d) = Tr_{V_{R,S}(b)_N} V_d(1) +
c_{R,S}(b²;2k+1,2m+1) F_{N-RS}(c(b),h_{R,-S}(b),d)`, where `V_{R,S}(b)` is the irreducible
quotient of `M(c(b),h_{R,S}(b))`.

Demand sheet: generic `b` read as `b ≠ 0`, `b² ∉ ℚ` (l.2884); `R, S ≥ 1`, `k < R`, `m < S`
(l.2880–2881); every `N ≥ 0`; both Verma coefficients are regular at the weights where they are
evaluated; the trace on the irreducible quotient is `IsIrrTrace`, for every such `T`; the
identity is multiplied by the denominator `boxDen` of the box ratio; the last term is absent
when `N < RS`. -/
def Stmt_sub_generic_tau_split : Prop :=
  ∀ b : ℂ, b ≠ 0 → (∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) →
    ∀ R S k m : ℕ, 0 < R → 0 < S → k < R → m < S → ∀ N : ℕ,
      let c : ℂ := kacC b
      let d : ℂ := kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b
      poleOrder (Frat c d N) (kacH R S b) = 0 ∧
      (R * S ≤ N → poleOrder (Frat c d (N - R * S)) (kacH (R : ℤ) (-(S : ℤ)) b) = 0) ∧
      ∀ T : ℂ, IsIrrTrace c (kacH R S b) d N T →
        FvalAt c d N (kacH R S b) * boxDen R S (b ^ 2) =
          T * boxDen R S (b ^ 2) +
            boxNum R S k m (b ^ 2) *
              (if R * S ≤ N then FvalAt c d (N - R * S) (kacH (R : ℤ) (-(S : ℤ)) b) else 0)

/-- Theorem 9.1 from Lemma 11.1, part (i) (`descent_iff_of_cited`), Lemma 11.3 and the three
sub-statements above. -/
theorem thm_descent_regularity_of_subs (hJ : Cited_JantzenLayersOrbit)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (h113 : Stmt_lem_joint_holomorphicity) (h1 : Stmt_sub_irr_trace_unique)
    (h2 : Stmt_sub_pole_outside) (h3 : Stmt_sub_orbit_regular) :
    Stmt_thm_descent_regularity := by
  intro p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs
  have hfus := lem_fusion_injective
  have hlam : kacH r s b ∈ orbitSet p p' r s := by
    refine ⟨true, 0, ?_⟩
    rw [kacH_momWt (by omega) (by omega) hb, muOrb]
    congr 1
    simp [nOrb]
  refine ⟨(hfus p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs).2.1, fun d => ⟨?_, ?_, ?_⟩,
    fun k m ε hk hm μ hμ N => ⟨?_, ?_⟩⟩
  · exact descent_iff_of_cited hJ hH hU hF hfus p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs d
  · exact h1 p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs d
  · constructor
    · intro hreg
      by_contra hd
      obtain ⟨N, hN⟩ := h2 p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs d hd
      exact hN (hreg N)
    · rintro ⟨k, m, hk, hm, hd | hd⟩ N
      · have := h3 p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs k m true hk hm _ hlam N
        rw [hd]
        simpa [sgnInt] using this
      · have := h3 p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs k m false hk hm _ hlam N
        rw [hd]
        simpa [sgnInt] using this
  · exact h3 p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs k m ε hk hm μ hμ N
  · exact h113 p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs k m ε hk hm N μ hμ

end Virasoro
