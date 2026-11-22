import Virasoro.Proofs.P2Sec13DerivChain
import Virasoro.Proofs.P2Sec13Reduce

/-!
# Lemma 13.1, Steps 2–4: the parts of `Stmt_sub_tau_trace_limit` (paper.tex l.2906–3028)

In the paper's order:

* Step 2 (l.2906–2918): the free lattice.  `Stmt_sub_tau_kernel_lift` (proved in
  `P2Sec13KernelLift`) and `Stmt_sub_tau_lattice` below: a family `E` of vectors of
  `M(c⋆,μ)_N` completing the descendants of `χ_{R₁,S₁}(b⋆)` to a basis, which stays a complement
  of the radical at generic `b`; the quotient `𝒱_N` is represented by the coordinates along `E`.
* Step 2 (l.2919–2937), the length-two structure of `V₀`: `eq_of_length_two`,
  `orbit_length_two` (from Lemma 10.3(i)).
* Step 3 (l.2939–2988): `Stmt_sub_tau_depth_one`, proved here as `sub_tau_depth_one_of_cited`.
* Step 4 (l.2990–3028): `Stmt_sub_tau_diag_limit` below.

`sub_tau_trace_limit_of_subs` composes Steps 2 and 4.
-/

namespace Virasoro.P2

open Virasoro Verma

/-- Step 3 of the proof of Lemma 13.1 (l.2939–2988): `J_τ^2 = 0`. -/
theorem sub_tau_depth_one_of_cited (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit) :
    Stmt_sub_tau_depth_one :=
  sub_tau_depth_one_of_subs hJ hU (sub_tau_kernel_lift_of_cited hK hE hH hU hF hLau)
    (tau_first_order_gram hJ hH hU hLau)

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit) :
    Stmt_sub_tau_depth_one := sub_tau_depth_one_of_cited hK hE hH hU hF hLau hJ

/-- Step 2, l.2910–2918: completing the PBW descendants `{L_{-I}χ_{R,S}(b⋆)}` to a basis of
`M(c⋆,μ)_N` gives a family `E` whose span is a complement of `(U(Vir_-)χ_{R,S}(b⋆))_N` and,
at generic `b` outside a finite set, of the radical `ker G_N(c(b),h_{R,S}(b))`
(`= (U(Vir_-)χ_{R,S}(b))_N`): the classes of `E` are a basis of the free lattice `𝒱_N` and of
its fibres.

Demand sheet: every `b⋆ ≠ 0`, `R, S ≥ 1` (the consumer uses `b⋆² = -p'/p` and an arrow
label); every singular vector `χ` of level `RS` at `b⋆`; every `N`; generic `b`: `b ≠ 0`,
`b² ∉ ℚ`, outside a finite set; the rank `p(N) - p(N-RS)` (l.2916) is not used by the consumer
and is not stated. -/
def Stmt_sub_tau_lattice : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ R S : ℕ, 0 < R → 0 < S →
    ∀ χ : Verma ℂ (kacC b) (kacH R S b), Verma.IsSingular χ (R * S) → ∀ N : ℕ,
      ∃ (n : ℕ) (E : Fin n → (Nat.Partition N → ℂ)) (S₀ : Finset ℂ),
        LinearIndependent ℂ E ∧
        IsCompl (Submodule.span ℂ (Set.range E))
          ((Verma.negSpan χ).comap (Verma.pbwCoord N)) ∧
        ∀ b' : ℂ, b' ≠ 0 → (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → b' ∉ S₀ →
          IsCompl (Submodule.span ℂ (Set.range E))
            (LinearMap.ker (gram (kacC b') (kacH R S b') N).mulVecLin)

/-- Step 4 of the proof of Lemma 13.1 (l.2990–3028): for a family `E` as in Step 2, the trace
on the generic irreducible quotient `V_{R₁,S₁}(b)_N` (computed in the basis `E`) is the value
at generic `b` of a rational function of `b` that is regular at `b⋆` with value
`T^irr_N(c⋆,μ,d⋆) + Ω_{u,v}(μ→ν₂) T^irr_{N-R₂S₂}(c⋆,ν₂,d⋆)`.

Demand sheet: `MinimalSetting`; `(k,m)` in the fusion box; node `μ = μ^ε_{k₀}`, `ν₁` of sign
`ε₁` with label `(R,S) = arrowLabel`, `ν₂` the other node of the layer `k₀+1`; every singular
vector `χ` of level `RS` at `b⋆`; every family `E` with the three properties of
`Stmt_sub_tau_lattice` (with its finite set `S₀`); the conclusion is that of
`Stmt_sub_tau_trace_limit`. -/
def Stmt_sub_tau_diag_limit : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      ∀ (ε : Bool) (k₀ : ℕ) (ε₁ : Bool) (N R S : ℕ),
        arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε₁ (k₀ + 1)) = ((R : ℤ), (S : ℤ)) →
        ∀ χ : Verma ℂ (kacC b) (kacH R S b), Verma.IsSingular χ (R * S) →
          ∀ (n : ℕ) (E : Fin n → (Nat.Partition N → ℂ)) (S₀ : Finset ℂ),
            LinearIndependent ℂ E →
            IsCompl (Submodule.span ℂ (Set.range E))
              ((Verma.negSpan χ).comap (Verma.pbwCoord N)) →
            (∀ b' : ℂ, b' ≠ 0 → (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → b' ∉ S₀ →
              IsCompl (Submodule.span ℂ (Set.range E))
                (LinearMap.ker (gram (kacC b') (kacH R S b') N).mulVecLin)) →
            ∃ (g : RatFunc ℂ) (S₁ : Finset ℂ),
              (∀ b' : ℂ, b' ≠ 0 → (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → b' ∉ S₁ →
                RegAt b' g ∧
                  ∀ T : ℂ, IsIrrTrace (kacC b') (kacH R S b')
                    (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b') N T → evalAt b' g = T) ∧
              RegAt b g ∧
                ∀ T₁ T₂ : ℂ,
                  IsIrrTrace (kacC b) (muOrb p p' r s ε k₀)
                    (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N T₁ →
                  (ellOrb p p' r s (!ε₁) (k₀ + 1) - ellOrb p p' r s ε k₀ ≤ N →
                    IsIrrTrace (kacC b) (muOrb p p' r s (!ε₁) (k₀ + 1))
                      (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
                      (N - (ellOrb p p' r s (!ε₁) (k₀ + 1) - ellOrb p p' r s ε k₀)) T₂) →
                  (N < ellOrb p p' r s (!ε₁) (k₀ + 1) - ellOrb p p' r s ε k₀ → T₂ = 0) →
                    evalAt b g = T₁ + (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ) * T₂

/-- `Stmt_sub_tau_trace_limit` from Step 2 (the lattice) and Step 4. -/
theorem sub_tau_trace_limit_of_subs (hH : Cited_HJSNormalizations)
    (h2 : Stmt_sub_tau_lattice) (h4 : Stmt_sub_tau_diag_limit) : Stmt_sub_tau_trace_limit := by
  intro p p' r s b hset k m hk hm ε k₀ ε₁ N
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  obtain ⟨R, S, hR, hS, hsum, hdiff, -, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε k₀ ε₁
  have hL := arrowLabel_eq hcop hp hp' hsum hdiff (not_dvd_of_congr hs0 hs hcS)
  have hb0 := minimalSetting_b_ne_zero hset
  obtain ⟨pf, ⟨hp1, hsing⟩, -, -, -, hspec⟩ := normalization_at hH R S hR hS
  have hχ := (hspec ℂ b hb0 fun Y => regular_of_normalized hR hS pf hp1 hsing hb0 Y).1
  obtain ⟨n, E, S₀, hLI, hc, hgen⟩ := h2 b hb0 R S hR hS _ hχ N
  simp only [hL]
  exact h4 p p' r s b hset k m hk hm ε k₀ ε₁ N R S hL _ hχ n E S₀ hLI hc hgen

/-- Lemma 13.1 from the two open parts of Steps 2 and 4. -/
theorem lem_degenerate_quotient_t_of_subs (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective)
    (h2 : Stmt_sub_tau_lattice) (h4 : Stmt_sub_tau_diag_limit) :
    Stmt_lem_degenerate_quotient_t :=
  lem_degenerate_quotient_t_of_trace hK hE hH hU hF hI (sub_tau_trace_limit_of_subs hH h2 h4)

end Virasoro.P2
