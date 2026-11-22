import Virasoro.Proofs.P2Sec13TauLattice
import Virasoro.Proofs.P2Sec13Limit
import Virasoro.Proofs.P2Sec11LayerBasis
import Virasoro.Proofs.Sec8Ising11

/-!
# Lemma 13.1, Steps 2–3: the depth-one `τ`-Jantzen filtration (paper.tex l.2906–2988)

The formal curve is `b = b⋆ + X`: `c(X) = c(b⋆+X)`, `Δ₁(X) = h_{R₁,S₁}(b⋆+X)` in `ℂ⟦X⟧`
(`cLoc`, `hLoc`).  Since `b⋆ ≠ 0`, `τ = b² - b⋆² = X(2b⋆+X)` is a unit multiple of `X`, so the
`τ`-adic and `X`-adic orders agree; no square root is formed.

Step 3 in coordinates: on every level `N` the layer of order `2` of `G_N(c(X),Δ₁(X))` is the
level-`N` part of `U(Vir_-)χ_{R₁,S₁}(b⋆) = M(c⋆,ν₁)`, that is `J_τ^2 = 0` in `V₀`.

`sub_tau_depth_one_of_subs` proves it from Lemma 10.3(i) (cited), the lift of
`U(Vir_-)χ_{R₁,S₁}` into the kernel (Step 2, `Stmt_sub_tau_kernel_lift`) and the first-order
coefficient (13.3) (`Stmt_sub_tau_deriv_chain`).
-/

namespace Virasoro.P2

open Virasoro Verma PowerSeries

/-- `b = b⋆ + X`. -/
noncomputable def bLoc (b : ℂ) : ℂ⟦X⟧ := C b + X

/-- `c(b⋆ + X)` as a power series. -/
noncomputable def cLoc (b : ℂ) : ℂ⟦X⟧ := 1 + 6 * (bLoc b + (bLoc b)⁻¹) ^ 2

/-- `h_{u,v}(b⋆ + X)` as a power series. -/
noncomputable def hLoc (u v : ℤ) (b : ℂ) : ℂ⟦X⟧ :=
  C (1 / 4 : ℂ) * ((bLoc b + (bLoc b)⁻¹) ^ 2 - ((u : ℂ⟦X⟧) * bLoc b + (v : ℂ⟦X⟧) * (bLoc b)⁻¹) ^ 2)

theorem constantCoeff_bLoc (b : ℂ) : constantCoeff (bLoc b) = b := by
  simp [bLoc]

theorem constantCoeff_cLoc (b : ℂ) : constantCoeff (cLoc b) = kacC b := by
  simp only [cLoc, kacC, map_add, map_mul, map_pow, map_one, map_ofNat, constantCoeff_inv,
    constantCoeff_bLoc]

theorem constantCoeff_hLoc (u v : ℤ) (b : ℂ) : constantCoeff (hLoc u v b) = kacH u v b := by
  simp only [hLoc, kacH, map_mul, map_sub, map_pow, map_add, constantCoeff_inv, constantCoeff_bLoc,
    constantCoeff_C, map_intCast]
  ring

/-- The well-definedness argument of l.2978–2986 in matrix form: if `v ∈ ker G(0)` has a lift
`V₂` with `[X¹] V₂ᵀ G V₂ ≠ 0`, then `v` has no lift of order `2`. -/
theorem not_mem_layer_two {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ⟦X⟧}
    (hG : G.IsSymm) {v : ι → ℂ} {V₂ : ι → ℂ⟦X⟧} (h0 : ∀ j, constantCoeff (V₂ j) = v j)
    (hker : ∀ j, (X : ℂ⟦X⟧) ∣ (G.mulVec V₂) j)
    (hne : coeff 1 (V₂ ⬝ᵥ G.mulVec V₂) ≠ 0) : v ∉ layer G 2 := by
  rintro ⟨V, hV0, hd⟩
  have hdiv : ∀ j, (X : ℂ⟦X⟧) ∣ V j - V₂ j := fun j => by
    rw [X_dvd_iff, map_sub, hV0, h0, sub_self]
  choose U hU using hdiv
  have hV : V = V₂ + (X : ℂ⟦X⟧) • U := by
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← hU j]
    ring
  have h1 : (X : ℂ⟦X⟧) ^ 2 ∣ V ⬝ᵥ G.mulVec V := dvd_dot_right hd
  have hsym : U ⬝ᵥ G.mulVec V₂ = V₂ ⬝ᵥ G.mulVec U := by
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hG.eq]
  obtain ⟨q, hq⟩ : (X : ℂ⟦X⟧) ∣ U ⬝ᵥ G.mulVec V₂ := dvd_dot_right hker
  have hexp : V ⬝ᵥ G.mulVec V = V₂ ⬝ᵥ G.mulVec V₂ +
      (X : ℂ⟦X⟧) ^ 2 * (2 * q + U ⬝ᵥ G.mulVec U) := by
    rw [hV]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← hsym, hq]
    ring
  have h2 : (X : ℂ⟦X⟧) ^ 2 ∣ V₂ ⬝ᵥ G.mulVec V₂ := by
    have := dvd_sub h1 (Dvd.intro _ rfl : (X : ℂ⟦X⟧) ^ 2 ∣ X ^ 2 * (2 * q + U ⬝ᵥ G.mulVec U))
    rwa [hexp, add_sub_cancel_right] at this
  exact hne ((X_pow_dvd_iff.1 h2) 1 (by norm_num))

/-- Step 3 for a formal curve through `(c,h)` at which `M(c,h)` has the length-two structure of
Step 2 (l.2919–2937, 2939–2988). -/
theorem layer_two_eq_of_length_two {c h : ℂ} {cL hL : ℂ⟦X⟧} (hc : constantCoeff cL = c)
    (hh : constantCoeff hL = h) {χ₁ χ₂ : Verma ℂ c h} {ℓ₁ ℓ₂ : ℕ} (hχ₁ : IsSingular χ₁ ℓ₁)
    (hχ₂ : IsSingular χ₂ ℓ₂) (hJ1 : jantzen c h 1 = negSpan χ₁ ⊔ negSpan χ₂)
    (hsimple : ∀ W : Submodule ℂ (Verma ℂ c h), IsVirSubmodule W →
      negSpan χ₁ ⊓ negSpan χ₂ ≤ W → W ≤ negSpan χ₂ →
        W = negSpan χ₁ ⊓ negSpan χ₂ ∨ W = negSpan χ₂)
    (hA : ∀ (N : ℕ) (v : Nat.Partition N → ℂ), pbwCoord N v ∈ negSpan χ₁ →
      v ∈ layer (gram cL hL N) 2)
    (hB : ∀ x₂ : Nat.Partition ℓ₂ → ℂ, pbwCoord ℓ₂ x₂ = χ₂ → x₂ ∉ layer (gram cL hL ℓ₂) 2)
    (N : ℕ) (v : Nat.Partition N → ℂ) :
    v ∈ layer (gram cL hL N) 2 ↔ pbwCoord N v ∈ negSpan χ₁ := by
  subst hc hh
  have hV2 := negSpan_isVir hχ₂
  have h1 : negSpan χ₁ ≤ tauJ cL hL 2 := by
    intro x hx
    obtain ⟨T, hT⟩ := exists_decomp x
    rw [hT]
    exact Submodule.sum_mem _ fun M _ => pbwCoord_mem_tauJ.2 (hA M _ (level_part_mem hχ₁ M hx))
  have hle : tauJ cL hL 2 ≤ negSpan χ₁ ⊔ negSpan χ₂ := by
    rw [← hJ1, ← tauJ_one]
    exact tauJ_anti (by norm_num)
  have h2 : χ₂ ∉ tauJ cL hL 2 := by
    intro hmem
    obtain ⟨x₂, hx₂⟩ := mem_level_of_L_zero hχ₂.2.1
    rw [← hx₂] at hmem
    exact hB x₂ hx₂ (pbwCoord_mem_tauJ.1 hmem)
  have hJeq := eq_of_length_two (tauJ_isVir 2) hV2 h1 hle hsimple h2
  rw [← pbwCoord_mem_tauJ, hJeq]

/-- Lemma 10.3(i) at the node `μ = μ^ε_{k₀}` for the first layer (l.2919–2921), with the weight
written as a variable: singular vectors `χ₁`, `χ₂` of weights `ν₁`, `ν₂` with
`J¹ = M(ν₁) + M(ν₂)` and `M(ν₂)/(M(ν₁) ∩ M(ν₂))` simple. -/
theorem orbit_length_two (hJ : Cited_JantzenLayersOrbit) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) (ε : Bool) (k₀ : ℕ) (ε₁ : Bool) :
    ∀ μ' : ℂ, μ' = muOrb p p' r s ε k₀ →
      ∃ χ₁ χ₂ : Verma ℂ (kacC b) μ',
        IsSingular χ₁ (ellOrb p p' r s ε₁ (k₀ + 1) - ellOrb p p' r s ε k₀) ∧
        IsSingular χ₂ (ellOrb p p' r s (!ε₁) (k₀ + 1) - ellOrb p p' r s ε k₀) ∧
        jantzen (kacC b) μ' 1 = negSpan χ₁ ⊔ negSpan χ₂ ∧
        ∀ W : Submodule ℂ (Verma ℂ (kacC b) μ'), IsVirSubmodule W →
          negSpan χ₁ ⊓ negSpan χ₂ ≤ W → W ≤ negSpan χ₂ →
            W = negSpan χ₁ ⊓ negSpan χ₂ ∨ W = negSpan χ₂ := by
  rintro μ' rfl
  obtain ⟨wp, wm, ⟨hsing, hsum⟩, hlay⟩ := hJ p p' r s b hset ε k₀
  obtain ⟨hp1, hm1⟩ := hsing 1 le_rfl
  obtain ⟨hinf, -, -, hW⟩ := hlay 1 le_rfl
  have hs := hsum 1 le_rfl
  cases ε₁
  · refine ⟨wm 1, wp 1, hm1, hp1, by rw [hs, sup_comm], fun W hWv hle1 hle2 => ?_⟩
    rw [inf_comm (negSpan (wm 1)), hinf] at hle1 ⊢
    exact (hW W hWv hle1).1 hle2
  · refine ⟨wp 1, wm 1, hp1, hm1, hs, fun W hWv hle1 hle2 => ?_⟩
    rw [hinf] at hle1 ⊢
    exact (hW W hWv hle1).2 hle2

/-- Step 2, l.2906–2910, with the radical property of Step 1 (l.2893–2897) over `ℂ⟦X⟧`: every
vector of `U(Vir_-)χ_{R,S}(b⋆)` of level `N` is the value at `X = 0` of a family over `ℂ⟦X⟧`
(a combination of descendants of `χ_{R,S}(b⋆+X)`) that lies in the kernel of
`G_N(c(X),h_{R,S}(X))`, and, for `k < R`, `m < S`, in the left and right kernels of
`ρ_N(c(X),h_{R,S}(X),h_{2k+1,2m+1}(X))`.

Demand sheet: every `b⋆ ≠ 0` (the consumer uses `b⋆² = -p'/p`), `R, S ≥ 1`; every singular
vector of level `RS` at `b⋆`; every level `N`; one family for the Gram matrix and for all
`(k,m)` in the box `k < R`, `m < S` (l.2880–2881); kernel on both sides of `ρ` (the consumer
uses both slots, l.3000–3003). -/
def Stmt_sub_tau_kernel_lift : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ R S : ℕ, 0 < R → 0 < S →
    ∀ χ : Verma ℂ (kacC b) (kacH R S b), Verma.IsSingular χ (R * S) →
      ∀ (N : ℕ) (v : Nat.Partition N → ℂ), Verma.pbwCoord N v ∈ Verma.negSpan χ →
        ∃ V : Nat.Partition N → ℂ⟦X⟧, (∀ Y, constantCoeff (V Y) = v Y) ∧
          (gram (cLoc b) (hLoc R S b) N).mulVec V = 0 ∧
          ∀ k m : ℕ, k < R → m < S →
            (torus (cLoc b) (hLoc R S b) (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N).mulVec V
                = 0 ∧
              Matrix.vecMul V
                (torus (cLoc b) (hLoc R S b) (hLoc (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N) = 0

/-- Equation (13.3), first line (l.2948–2983): for the two arrows `μ → ν₁` (label `(R₁,S₁)`)
and `μ → ν₂` (label `(R₂,S₂)`) and every lift `V₂` over `ℂ⟦X⟧` of the singular vector
`χ_{R₂,S₂}(b⋆)`, the coefficient of `X¹` in `B_X(V₂,V₂)` on `M(c(X),h_{R₁,S₁}(X))` is nonzero
(it is a nonzero multiple of `α γ_{R₂,S₂}(b⋆)`).

Demand sheet: `MinimalSetting`; node `μ^ε_{k₀}`, `ν₁` of sign `ε₁`, `ν₂` of sign `!ε₁` in the
layer `k₀+1`, labels `arrowLabel`; every singular vector of level `R₂S₂` at `b⋆` (in
coordinates); every lift (l.2978–2983); the consumer uses only the nonvanishing (l.2984–2986). -/
def Stmt_sub_tau_deriv_chain : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ (ε : Bool) (k₀ : ℕ) (ε₁ : Bool) (R₁ S₁ R₂ S₂ : ℕ),
      arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε₁ (k₀ + 1)) = ((R₁ : ℤ), (S₁ : ℤ)) →
      arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s (!ε₁) (k₀ + 1)) =
          ((R₂ : ℤ), (S₂ : ℤ)) →
        ∀ x₂ : Nat.Partition (R₂ * S₂) → ℂ,
          Verma.IsSingular
            (Verma.pbwCoord (c := kacC b) (h := kacH R₂ S₂ b) (R₂ * S₂) x₂) (R₂ * S₂) →
          ∀ V₂ : Nat.Partition (R₂ * S₂) → ℂ⟦X⟧, (∀ Y, constantCoeff (V₂ Y) = x₂ Y) →
            coeff 1 (V₂ ⬝ᵥ (gram (cLoc b) (hLoc R₁ S₁ b) (R₂ * S₂)).mulVec V₂) ≠ 0

/-- Step 3 (l.2939–2988), `J_τ^2 = 0`, in coordinates: on every level the layer of order `2` of
`G_N(c(X),h_{R₁,S₁}(X))` is the level-`N` part of `U(Vir_-)χ_{R₁,S₁}(b⋆)`.

Demand sheet: `MinimalSetting`; node `μ^ε_{k₀}` and the arrow to the node of sign `ε₁` in the
layer `k₀+1` with label `(R,S) = arrowLabel`; every singular vector `χ` of level `RS` at `b⋆`;
every level `N`; the filtration is by `X`-adic order with `X = b - b⋆`. -/
def Stmt_sub_tau_depth_one : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ (ε : Bool) (k₀ : ℕ) (ε₁ : Bool) (R S : ℕ),
      arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε₁ (k₀ + 1)) = ((R : ℤ), (S : ℤ)) →
      ∀ χ : Verma ℂ (kacC b) (kacH R S b), Verma.IsSingular χ (R * S) →
        ∀ (N : ℕ) (v : Nat.Partition N → ℂ),
          v ∈ layer (gram (cLoc b) (hLoc R S b) N) 2 ↔ Verma.pbwCoord N v ∈ Verma.negSpan χ

theorem isSingular_pbwCoord_congr {c h h' : ℂ} (hh : h = h') {n : ℕ} {x : Nat.Partition n → ℂ}
    (hx : IsSingular (pbwCoord (c := c) (h := h) n x) n) :
    IsSingular (pbwCoord (c := c) (h := h') n x) n := by
  subst hh
  exact hx

/-- The arrow data of a node: positivity, the label, the weight and the level. -/
theorem arrow_facts {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool)
    (k₀ : ℕ) (ε' : Bool) {R S : ℕ}
    (hlab : arrowLabel p p' (nOrb p p' r s ε k₀) (nOrb p p' r s ε' (k₀ + 1)) =
      ((R : ℤ), (S : ℤ))) :
    0 < R ∧ 0 < S ∧ kacH R S b = muOrb p p' r s ε k₀ ∧
      ellOrb p p' r s ε' (k₀ + 1) - ellOrb p p' r s ε k₀ = R * S := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  obtain ⟨R', S', hR, hS, hsum, hdiff, hcR, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε k₀ ε'
  have hL := arrowLabel_eq hcop hp hp' hsum hdiff (not_dvd_of_congr hs0 hs hcS)
  rw [hlab, Prod.mk.injEq] at hL
  obtain ⟨e1, e2⟩ := hL
  have e1' : R = R' := by exact_mod_cast e1
  have e2' : S = S' := by exact_mod_cast e2
  subst e1' e2'
  refine ⟨hR, hS, ?_, arrow_level hp hp' hr hs ε k₀ ε' hsum hdiff⟩
  rw [kacH_momWt hp hp' hb, muOrb]
  rcases hdiff with h | h
  · rw [h]
  · rw [h, momWt_neg]

theorem minimalSetting_b_ne_zero {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) :
    b ≠ 0 := by
  obtain ⟨hp2, hp2', -, -, -, -, -, -, hb⟩ := hset
  rintro rfl
  rw [zero_pow two_ne_zero] at hb
  have h1 : (p' : ℂ) ≠ 0 := by exact_mod_cast (by omega : p' ≠ 0)
  have h2 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  exact (div_ne_zero (neg_ne_zero.2 h1) h2) hb.symm

/-- Step 3 from Lemma 10.3(i), the kernel lifts of Step 2 and the first line of (13.3). -/
theorem sub_tau_depth_one_of_subs (hJ : Cited_JantzenLayersOrbit) (hU : Cited_SingularUnique)
    (hA : Stmt_sub_tau_kernel_lift) (hB : Stmt_sub_tau_deriv_chain) :
    Stmt_sub_tau_depth_one := by
  intro p p' r s b hset ε k₀ ε₁ R S hlab χ hχ N v
  obtain ⟨hR, hS, hμ₁, hlev₁⟩ := arrow_facts hset ε k₀ ε₁ hlab
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  obtain ⟨R₂, S₂, -, -, hsum₂, hdiff₂, -, hcS₂, -⟩ := arrow_data hr0 hr hs0 hs ε k₀ (!ε₁)
  have hlab₂ := arrowLabel_eq hcop hp hp' hsum₂ hdiff₂ (not_dvd_of_congr hs0 hs hcS₂)
  obtain ⟨hR₂, hS₂, hμ₂, hlev₂⟩ := arrow_facts hset ε k₀ (!ε₁) hlab₂
  have hb0 := minimalSetting_b_ne_zero hset
  obtain ⟨χ₁, χ₂, hs1, hs2, hJ1, hsimple⟩ :=
    orbit_length_two hJ hset ε k₀ ε₁ (kacH R S b) hμ₁
  rw [hlev₁] at hs1
  rw [hlev₂] at hs2
  obtain ⟨a, ha⟩ := hU _ _ _ χ₁ χ hs1 hχ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hχ.1 (ha.trans (zero_smul ℂ χ₁))
  rw [ha, negSpan_smul χ₁ ha0]
  refine layer_two_eq_of_length_two (constantCoeff_cLoc b) (constantCoeff_hLoc R S b) hs1 hs2
    hJ1 hsimple (fun N v hv => ?_) (fun x₂ hx₂ => ?_) N v
  · obtain ⟨V, hV0, hG, -⟩ := hA b hb0 R S hR hS χ₁ hs1 N v hv
    exact ⟨V, hV0, fun Y => by rw [hG]; exact dvd_zero _⟩
  · have hrad : (gram (kacC b) (kacH R S b) (R₂ * S₂)).mulVec x₂ = 0 := by
      have hmem : χ₂ ∈ (jantzen (kacC b) (kacH R S b) 1 : Set _) := by
        rw [SetLike.mem_coe, hJ1]
        exact Submodule.mem_sup_right (mem_negSpan_self χ₂)
      rw [jantzen_one_eq_radical] at hmem
      funext Y
      have h := hmem (neg Y.word)
      rw [← hx₂, shap_neg_pbwCoord] at h
      exact h
    have hsing₂ : IsSingular
        (pbwCoord (c := kacC b) (h := kacH R₂ S₂ b) (R₂ * S₂) x₂) (R₂ * S₂) :=
      isSingular_pbwCoord_congr (hμ₁.trans hμ₂.symm) (hx₂ ▸ hs2)
    refine not_mem_layer_two (V₂ := fun Y => (C (x₂ Y) : ℂ⟦X⟧)) ?_ (fun Y => constantCoeff_C _)
      (fun Y => ?_) (hB p p' r s b hset ε k₀ ε₁ R S R₂ S₂ hlab hlab₂ x₂ hsing₂ _
        fun Y => constantCoeff_C _)
    · exact gram_transpose _ _ _
    · rw [X_dvd_iff]
      have e : constantCoeff ((gram (cLoc b) (hLoc R S b) (R₂ * S₂)).mulVec
          (fun Y => (C (x₂ Y) : ℂ⟦X⟧)) Y) =
          (gram (kacC b) (kacH R S b) (R₂ * S₂)).mulVec x₂ Y := by
        rw [← constantCoeff_cLoc b, ← constantCoeff_hLoc R S b, gram_map]
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
          constantCoeff_C]
      rw [e, hrad]
      rfl

end Virasoro.P2
