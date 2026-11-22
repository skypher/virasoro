import Virasoro.Proofs.P2Sec13GenFinal
import Virasoro.Proofs.P2Sec9TruncEval
import Virasoro.Proofs.P2Sec12Cocycle
import Mathlib.Analysis.Complex.Cardinality

/-!
# Lemma 13.1: the limit `τ → 0` of equation (13.2) (paper.tex l.2869–3037)

Reading of l.2878–2883 and of "taking `τ → 0`" (l.3034–3037).  The deformation is parametrized by
`b` itself: `c(b)`, `h_{R,S}(b)`, `d(b)` and the frozen Lemma 11.3 are stated in `b`, and
`b(τ) = √(t₀+τ)` is a local coordinate at `b⋆` (`τ = b² - b⋆²`), so no square root is formed.
Each term of (13.2) is the value at generic `b` of a rational function of `b` that is regular at
`b⋆`; "the limit `τ → 0`" of the term is the value of that rational function at `b⋆`.  Equation
(13.2) holds at all generic `b` (Step 1), hence as an identity of rational functions, hence at
`b⋆`.

The three limits are the sub-statements below; `lem_degenerate_quotient_t_of_limits` is the last
sentence of the proof (l.3034–3037).
-/

namespace Virasoro.P2

open Virasoro Polynomial

/-- The limits of the Verma terms of (13.2) (l.3029–3034, by Lemma 11.3): for integers `(u,v)`
with `h_{u,v}(b⋆)` in the orbit, `b ↦ F_N(c(b),h_{u,v}(b),d(b))` is, at generic `b`, the value
of a rational function of `b` that is regular at `b⋆` with value `F_N(c⋆,h_{u,v}(b⋆),d⋆)`.

Demand sheet: `MinimalSetting`; `(k,m)` in the fusion box; `(u,v) ∈ ℤ²` with `h_{u,v}(b⋆)` an
orbit weight (the consumer uses `(R₁,S₁)` and `(R₁,-S₁)`, l.3031–3033); every `N`; generic `b`:
`b ≠ 0`, `b² ∉ ℚ`, outside a finite set; the values are `FvalAt`. -/
def Stmt_sub_tau_verma_limit : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      ∀ u v : ℤ, kacH u v b ∈ orbitSet p p' r s → ∀ N : ℕ,
        ∃ (g : RatFunc ℂ) (S₀ : Finset ℂ),
          (∀ b' : ℂ, b' ≠ 0 → (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → b' ∉ S₀ →
            RegAt b' g ∧
              evalAt b' g = FvalAt (kacC b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b') N
                (kacH u v b')) ∧
          RegAt b g ∧
            evalAt b g = FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N
              (kacH u v b)

/-- The limit of the box ratio (l.3018–3023, 3031–3033, by Proposition 12.1(i)): for a primitive
arrow with label `(R,S)`, `c_{R,S}(b²;2k+1,2m+1)` is, at generic `b`, the value of a rational
function of `b` that is regular at `b⋆` with value `Ω_{u,v}` of the arrow.

Demand sheet: `MinimalSetting`; `(k,m)` in the fusion box; every arrow `μ^ε_j → μ^{ε'}_{j+1}`
with its label `arrowLabel`; generic `b` as above; the ratio is cross-multiplied with `boxDen`;
the value at `b⋆` is `cArrow`. -/
def Stmt_sub_tau_box_limit : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      ∀ (ε : Bool) (j : ℕ) (ε' : Bool),
        let L := arrowLabel p p' (nOrb p p' r s ε j) (nOrb p p' r s ε' (j + 1))
        ∃ (g : RatFunc ℂ) (S₀ : Finset ℂ),
          (∀ b' : ℂ, b' ≠ 0 → (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → b' ∉ S₀ →
            RegAt b' g ∧ evalAt b' g * boxDen L.1 L.2 (b' ^ 2) = boxNum L.1 L.2 k m (b' ^ 2)) ∧
          RegAt b g ∧ evalAt b g = (cArrow p p' r s k m ε j ε' : ℂ)

/-- Steps 2–4 of the proof of Lemma 13.1 (l.2906–3028): the trace on the generic irreducible
quotient `V_{R₁,S₁}(b)_N` is, at generic `b`, the value of a rational function of `b` that is
regular at `b⋆` with value
`T^irr_N(c⋆,μ,d⋆) + Ω_{u,v}(μ→ν₂) T^irr_{N-R₂S₂}(c⋆,ν₂,d⋆)`.

Demand sheet: `MinimalSetting`; `(k,m)` in the fusion box; node `μ = μ^ε_{k₀}`, `ν₁` the node of
sign `ε₁` in the layer `k₀+1` with label `(R₁,S₁) = arrowLabel`, `ν₂` the other node; every `N`;
generic `b` as above; the trace at generic `b` is every `T` with `IsIrrTrace`; at `b⋆`, for all
`T₁`, `T₂` as in `Stmt_lem_degenerate_quotient_t` (`T₂` absent when `N < ν₂ - μ`). -/
def Stmt_sub_tau_trace_limit : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ k m : ℕ, k < min r (p - r) → m < min s (p' - s) →
      ∀ (ε : Bool) (k₀ : ℕ) (ε₁ : Bool) (N : ℕ),
        let L := arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε₁ (k₀ + 1))
        ∃ (g : RatFunc ℂ) (S₀ : Finset ℂ),
          (∀ b' : ℂ, b' ≠ 0 → (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → b' ∉ S₀ →
            RegAt b' g ∧
              ∀ T : ℂ, IsIrrTrace (kacC b') (kacH L.1 L.2 b')
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

/-- The generic values of `b` outside a finite set form an infinite set. -/
theorem generic_infinite (S₀ : Finset ℂ) :
    {z : ℂ | z ≠ 0 ∧ (∀ q : ℚ, z ^ 2 ≠ (q : ℂ)) ∧ z ∉ S₀}.Infinite := by
  intro hfin
  apply not_countable_complex
  have hq : ∀ q : ℚ, {z : ℂ | z ^ 2 = (q : ℂ)}.Countable := by
    intro q
    have hne : (X ^ 2 - C (q : ℂ) : ℂ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) _
    refine ((Polynomial.finite_setOf_isRoot hne).subset ?_).countable
    intro z hz
    show (X ^ 2 - C (q : ℂ) : ℂ[X]).IsRoot z
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C]
    rw [Set.mem_setOf_eq] at hz
    rw [hz, sub_self]
  have hcov : (Set.univ : Set ℂ) ⊆
      {z : ℂ | z ≠ 0 ∧ (∀ q : ℚ, z ^ 2 ≠ (q : ℂ)) ∧ z ∉ S₀} ∪
        (({0} ∪ ⋃ q : ℚ, {z : ℂ | z ^ 2 = (q : ℂ)}) ∪ (↑S₀ : Set ℂ)) := by
    intro z _
    by_cases h0 : z = 0
    · exact Or.inr (Or.inl (Or.inl h0))
    · by_cases h1 : ∃ q : ℚ, z ^ 2 = (q : ℂ)
      · obtain ⟨q, hq'⟩ := h1
        exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨q, hq'⟩)))
      · by_cases h2 : z ∈ S₀
        · exact Or.inr (Or.inr h2)
        · exact Or.inl ⟨h0, fun q hq' => h1 ⟨q, hq'⟩, h2⟩
  refine Set.Countable.mono hcov (hfin.countable.union ?_)
  exact (((Set.countable_singleton 0).union (Set.countable_iUnion hq)).union
    S₀.finite_toSet.countable)

/-- Two rational functions that are regular and take the same values on an infinite set are
equal. -/
theorem ratFunc_eq_of_evalAt_infinite {x y : RatFunc ℂ} {G : Set ℂ} (hG : G.Infinite)
    (h : ∀ z ∈ G, RegAt z x ∧ RegAt z y ∧ evalAt z x = evalAt z y) : x = y := by
  have hpoly : x.num * y.denom - y.num * x.denom = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
    refine Set.Infinite.mono (s := G) ?_ hG
    intro z hz
    obtain ⟨hx, hy, he⟩ := h z hz
    simp only [evalAt, RatFunc.eval, Polynomial.eval₂_id] at he
    unfold RegAt at hx hy
    rw [div_eq_div_iff hx hy] at he
    show (x.num * y.denom - y.num * x.denom).IsRoot z
    rw [Polynomial.IsRoot, eval_sub, eval_mul, eval_mul, he]
    ring
  rw [← RatFunc.num_div_denom x, ← RatFunc.num_div_denom y,
    div_eq_div_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x))
      (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero y)), ← map_mul, ← map_mul]
  congr 1
  linear_combination hpoly

set_option maxHeartbeats 800000 in
/-- Lemma 13.1 from Step 1 and the three limits: "taking `τ → 0` in (13.2) yields (13.1)"
(l.3034–3037). -/
theorem lem_degenerate_quotient_t_of_limits (hK : Cited_KacDeterminant)
    (hE : Cited_TwoWeightPairingExists) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective)
    (hA : Stmt_sub_tau_verma_limit) (hB : Stmt_sub_tau_box_limit)
    (hT : Stmt_sub_tau_trace_limit) : Stmt_lem_degenerate_quotient_t := by
  classical
  intro p p' r s b hset k m hk hm ε k₀ ε₁ N c d μ lev₁ lev₂ T₁ T₂ hT₁ hT₂ hT₂0
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  obtain ⟨R, S, hR, hS, hsum, hdiff, hcR, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε k₀ ε₁
  have hL := arrowLabel_eq hcop hp hp' hsum hdiff (not_dvd_of_congr hs0 hs hcS)
  have hkR : k < R := lt_of_lt_of_le hk (min_le_of_congr hcR)
  have hmS : m < S := lt_of_lt_of_le hm (min_le_of_congr hcS)
  have hlev : lev₁ = R * S := arrow_level hp hp' hr hs ε k₀ ε₁ hsum hdiff
  have hμ : kacH R S b = μ := by
    show kacH R S b = muOrb p p' r s ε k₀
    rw [kacH_momWt hp hp' hb, muOrb]
    rcases hdiff with h | h
    · rw [h]
    · rw [h, momWt_neg]
  have hν : kacH (R : ℤ) (-(S : ℤ)) b = muOrb p p' r s ε₁ (k₀ + 1) := by
    rw [kacH_momWt hp hp' hb, muOrb, ← hsum]
    congr 1
    ring
  -- the three limits
  obtain ⟨gA, SA, hAgen, hAreg, hAval⟩ := hA p p' r s b hset k m hk hm R S
    (by rw [hμ]; exact ⟨ε, k₀, rfl⟩) N
  obtain ⟨gC, SC, hCgen, hCreg, hCval⟩ : ∃ (gC : RatFunc ℂ) (SC : Finset ℂ),
      (∀ b' : ℂ, b' ≠ 0 → (∀ q : ℚ, b' ^ 2 ≠ (q : ℂ)) → b' ∉ SC → RegAt b' gC ∧
        evalAt b' gC = if R * S ≤ N then
          FvalAt (kacC b') (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b') (N - R * S)
            (kacH (R : ℤ) (-(S : ℤ)) b') else 0) ∧
      RegAt b gC ∧ evalAt b gC = if R * S ≤ N then
        FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (N - R * S)
          (kacH (R : ℤ) (-(S : ℤ)) b) else 0 := by
    by_cases hle : R * S ≤ N
    · obtain ⟨g, S₀, h1, h2, h3⟩ := hA p p' r s b hset k m hk hm R (-(S : ℤ))
        (by rw [hν]; exact ⟨ε₁, k₀ + 1, rfl⟩) (N - R * S)
      refine ⟨g, S₀, fun b' hb' hirr' hS₀ => ?_, h2, ?_⟩
      · rw [if_pos hle]
        exact h1 b' hb' hirr' hS₀
      · rw [if_pos hle]
        exact h3
    · refine ⟨(0 : RatFunc ℂ), (∅ : Finset ℂ), fun b' _ _ _ => ⟨regAt_zero b', ?_⟩,
        regAt_zero b, ?_⟩
      · rw [if_neg hle]
        exact RatFunc.eval_zero (f := RingHom.id ℂ) (a := b')
      · rw [if_neg hle]
        exact RatFunc.eval_zero (f := RingHom.id ℂ) (a := b)
  have hB' := hB p p' r s b hset k m hk hm ε k₀ ε₁
  simp only [hL] at hB'
  obtain ⟨gB, SB, hBgen, hBreg, hBval⟩ := hB'
  have hT' := hT p p' r s b hset k m hk hm ε k₀ ε₁ N
  simp only [hL] at hT'
  obtain ⟨gT, ST, hTgen, hTreg, hTval⟩ := hT'
  -- (13.2) at generic `b`, as an identity of rational functions
  have hStep1 := sub_generic_tau_split_of_cited hK hE hH hU hF hI
  have hLay := sub_generic_layers_of_cited hK hE hH hU hF
  have hid : gA = gT + gB * gC := by
    refine ratFunc_eq_of_evalAt_infinite (generic_infinite (SA ∪ SC ∪ SB ∪ ST)) ?_
    rintro b' ⟨hb', hirr', hnot⟩
    simp only [Finset.mem_union, not_or] at hnot
    obtain ⟨⟨⟨hnA, hnC⟩, hnB⟩, hnT⟩ := hnot
    obtain ⟨rA, vA⟩ := hAgen b' hb' hirr' hnA
    obtain ⟨rC, vC⟩ := hCgen b' hb' hirr' hnC
    obtain ⟨rB, vB⟩ := hBgen b' hb' hirr' hnB
    obtain ⟨rT, vT⟩ := hTgen b' hb' hirr' hnT
    obtain ⟨T, hTirr, -⟩ := irrTrace_existsUnique
      (generic_descends hH hU hF hLay hb' hirr' hR hS hkR hmS) N
    obtain ⟨-, -, h13⟩ := hStep1 b' hb' hirr' R S k m hR hS hkR hmS N
    have h13' := h13 T hTirr
    have hden : boxDen R S (b' ^ 2) ≠ 0 := (box_gamma_generic hb' hirr' hkR hmS).1
    refine ⟨rA, rT.add (rB.mul rC), ?_⟩
    rw [evalAt_add rT (rB.mul rC), evalAt_mul rB rC, vA, vC, vT T hTirr]
    refine mul_right_cancel₀ hden ?_
    rw [h13', ← vB]
    ring
  -- the value at `b⋆`
  have hfin := congrArg (evalAt b) hid
  rw [evalAt_add hTreg (hBreg.mul hCreg), evalAt_mul hBreg hCreg, hAval, hCval, hBval,
    hTval T₁ T₂ hT₁ hT₂ hT₂0, hμ, hν, ← hlev] at hfin
  show T₁ + (cArrow p p' r s k m ε k₀ (!ε₁) : ℂ) * T₂ = FvalAt c d N μ -
    (if lev₁ ≤ N then (cArrow p p' r s k m ε k₀ ε₁ : ℂ) *
      FvalAt c d (N - lev₁) (muOrb p p' r s ε₁ (k₀ + 1)) else 0)
  rw [hfin]
  split_ifs <;> ring

example (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hI : Cited_VermaHomInjective) (hA : Stmt_sub_tau_verma_limit)
    (hB : Stmt_sub_tau_box_limit) (hT : Stmt_sub_tau_trace_limit) :
    Stmt_lem_degenerate_quotient_t :=
  lem_degenerate_quotient_t_of_limits hK hE hH hU hF hI hA hB hT

end Virasoro.P2
