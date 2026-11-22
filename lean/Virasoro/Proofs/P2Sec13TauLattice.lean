import Virasoro.Proofs.P2Sec11Lattice
import Virasoro.Proofs.SmithLayers
import Virasoro.Proofs.JantzenSub
import Virasoro.Proofs.SingularPull
import Virasoro.Proofs.P2Sec11VertexRad

/-!
# Lemma 13.1, Step 3: the `τ`-Jantzen lattices (paper.tex l.2939–2945)

Reading of l.2878–2883 and l.2939–2945.  The deformation is a formal curve
`(c(X), Δ(X)) ∈ ℂ⟦X⟧²` (in the application `X = b - b⋆`, `c(X) = c(b⋆+X)`,
`Δ(X) = h_{R₁,S₁}(b⋆+X)`; the uniformizer `τ = b² - b⋆²` differs from `X` by a unit).  The lattice
`𝒥_τ^{(i)}` is taken inside the Verma module over `ℂ⟦X⟧`: the vectors `W` with
`B_X(u, W) ∈ X^i ℂ⟦X⟧` for all `u`.  Since `B_X` vanishes on `U(Vir_-)χ_{R₁,S₁}(b)` (Step 1),
this is the preimage of the paper's lattice in the quotient `𝒱`, and its image `J_τ^i` at `X = 0`
is the preimage in `M(c⋆,μ)` of the paper's `J_τ^i ⊂ V₀`.

`J_τ^i` is a `Vir`-submodule (contravariance), `J_τ^1` is the radical of the Shapovalov form, and
on level `N` it is the layer of order `i` of the matrix `G_N(c(X),Δ(X))`.
-/

namespace Virasoro.P2

open Virasoro Verma PowerSeries

variable {cL hL : ℂ⟦X⟧}

/-- Evaluation at `X = 0`: `M(c(X),Δ(X)) → M(c(0),Δ(0))`. -/
noncomputable def tauEv (cL hL : ℂ⟦X⟧) :
    Verma ℂ⟦X⟧ cL hL →ₛₗ[(constantCoeff : ℂ⟦X⟧ →+* ℂ)]
      Verma ℂ (constantCoeff cL) (constantCoeff hL) :=
  Verma.baseChange (constantCoeff : ℂ⟦X⟧ →+* ℂ) rfl rfl

/-- The lattice `𝒥_τ^{(i)}`: `B_X(u, W) ∈ X^i ℂ⟦X⟧` for all `u`. -/
def InTau (cL hL : ℂ⟦X⟧) (i : ℕ) (W : Verma ℂ⟦X⟧ cL hL) : Prop :=
  ∀ u, (X : ℂ⟦X⟧) ^ i ∣ shap cL hL u W

theorem inTau_zero (i : ℕ) : InTau cL hL i 0 := fun u => by rw [map_zero]; exact dvd_zero _

theorem InTau.add {i : ℕ} {U W : Verma ℂ⟦X⟧ cL hL} (hU : InTau cL hL i U)
    (hW : InTau cL hL i W) : InTau cL hL i (U + W) := fun u => by
  rw [map_add]; exact dvd_add (hU u) (hW u)

theorem InTau.smul {i : ℕ} {U : Verma ℂ⟦X⟧ cL hL} (a : ℂ⟦X⟧) (hU : InTau cL hL i U) :
    InTau cL hL i (a • U) := fun u => by
  rw [map_smul, smul_eq_mul]; exact Dvd.dvd.mul_left (hU u) _

theorem InTau.mono {i i' : ℕ} (h : i ≤ i') {U : Verma ℂ⟦X⟧ cL hL} (hU : InTau cL hL i' U) :
    InTau cL hL i U := fun u => (pow_dvd_pow _ h).trans (hU u)

/-- `𝒥_τ^{(i)}` is stable under all modes (contravariance of `B_X`). -/
theorem InTau.L {i : ℕ} {U : Verma ℂ⟦X⟧ cL hL} (hU : InTau cL hL i U) (n : ℤ) :
    InTau cL hL i (Verma.L n U) := fun u => by
  have h := (isShapovalov_shap (c := cL) (h := hL)).2 (-n) u U
  rw [neg_neg] at h
  rw [← h]
  exact hU _

theorem tauEv_pbwCoord (N : ℕ) (w : Nat.Partition N → ℂ⟦X⟧) :
    tauEv cL hL (pbwCoord N w) = pbwCoord N fun Y => constantCoeff (w Y) :=
  Verma.baseChange_pbwCoord _ _ _ N w

theorem tauEv_L (n : ℤ) (U : Verma ℂ⟦X⟧ cL hL) :
    tauEv cL hL (Verma.L n U) = Verma.L n (tauEv cL hL U) :=
  Verma.baseChange_L _ _ _ n U

theorem shap_tauEv (U W : Verma ℂ⟦X⟧ cL hL) :
    shap (constantCoeff cL) (constantCoeff hL) (tauEv cL hL U) (tauEv cL hL W) =
      constantCoeff (shap cL hL U W) :=
  Verma.shap_baseChange _ rfl rfl U W

/-- Every vector of `M(c(0),Δ(0))` is the value at `X = 0` of a vector over `ℂ⟦X⟧`. -/
theorem tauEv_surjective (x : Verma ℂ (constantCoeff cL) (constantCoeff hL)) :
    ∃ W : Verma ℂ⟦X⟧ cL hL, tauEv cL hL W = x := by
  obtain ⟨T, hT⟩ := exists_decomp x
  refine ⟨∑ M ∈ T, pbwCoord M fun Y => (C (Verma.comp M x Y) : ℂ⟦X⟧), ?_⟩
  rw [map_sum]
  conv_rhs => rw [hT]
  refine Finset.sum_congr rfl fun M _ => ?_
  have e : (fun Y => constantCoeff (C (Verma.comp M x Y) : ℂ⟦X⟧)) = Verma.comp M x :=
    funext fun Y => constantCoeff_C _
  rw [tauEv_pbwCoord, e]

/-- The level components of a vector of `𝒥_τ^{(i)}` lie in `𝒥_τ^{(i)}`. -/
theorem InTau.comp {i : ℕ} {W : Verma ℂ⟦X⟧ cL hL} (hW : InTau cL hL i W) (N : ℕ) :
    InTau cL hL i (pbwCoord N (Verma.comp N W)) := by
  intro u
  refine induction_neg (P := fun u => (X : ℂ⟦X⟧) ^ i ∣
    shap cL hL u (pbwCoord N (Verma.comp N W))) ?_ ?_ ?_ u
  · intro w hw
    have hl : neg (c := cL) (h := hL) w ∈ level w.sum := neg_mem_level _ w hw le_rfl
    by_cases hN : w.sum = N
    · have h0 : shap cL hL (neg w) (W - pbwCoord N (Verma.comp N W)) = 0 := by
        refine shap_level_comp_zero (hN ▸ hl) ?_
        rw [map_sub, comp_pbwCoord_same, sub_self]
      rw [map_sub, sub_eq_zero] at h0
      rw [← h0]
      exact hW _
    · rw [shap_level_ne hN hl ⟨_, rfl⟩]
      exact dvd_zero _
  · intro u v hu hv
    rw [map_add, LinearMap.add_apply]
    exact dvd_add hu hv
  · intro r v hv
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left hv _

/-- A power-series family of order `i` on level `N` is a homogeneous vector of `𝒥_τ^{(i)}`. -/
theorem inTau_of_family {N i : ℕ} {w : Nat.Partition N → ℂ⟦X⟧}
    (hw : ∀ Y, (X : ℂ⟦X⟧) ^ i ∣ ((gram cL hL N).mulVec w) Y) : InTau cL hL i (pbwCoord N w) := by
  intro u
  refine induction_neg (P := fun u => (X : ℂ⟦X⟧) ^ i ∣ shap cL hL u (pbwCoord N w)) ?_ ?_ ?_ u
  · intro w' hw'
    have hl : neg (c := cL) (h := hL) w' ∈ level w'.sum := neg_mem_level _ w' hw' le_rfl
    by_cases hN : w'.sum = N
    · rw [hN] at hl
      obtain ⟨a, ha⟩ := hl
      rw [← ha, pbwCoord_apply, map_sum, LinearMap.sum_apply]
      refine Finset.dvd_sum fun Y _ => ?_
      rw [map_smul, LinearMap.smul_apply, shap_neg_pbwCoord, smul_eq_mul]
      exact Dvd.dvd.mul_left (hw Y) _
    · rw [shap_level_ne hN hl ⟨_, rfl⟩]
      exact dvd_zero _
  · intro u v hu hv
    rw [map_add, LinearMap.add_apply]
    exact dvd_add hu hv
  · intro r v hv
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left hv _

theorem family_of_inTau {N i : ℕ} {w : Nat.Partition N → ℂ⟦X⟧}
    (hw : InTau cL hL i (pbwCoord N w)) (Y : Nat.Partition N) :
    (X : ℂ⟦X⟧) ^ i ∣ ((gram cL hL N).mulVec w) Y := by
  have h := hw (neg Y.word)
  rw [shap_neg_pbwCoord] at h
  exact h

/-- The level coordinates commute with `X ↦ 0`. -/
theorem comp_tauEv (N : ℕ) (W : Verma ℂ⟦X⟧ cL hL) (Y : Nat.Partition N) :
    Verma.comp N (tauEv cL hL W) Y = constantCoeff (Verma.comp N W Y) := by
  classical
  have hW : W ∈ Submodule.span ℂ⟦X⟧ (Set.range fun Y : (Σ N : ℕ, Nat.Partition N) =>
      neg (c := cL) (h := hL) Y.2.word) := by
    rw [span_neg_word_eq_top]; trivial
  refine Submodule.span_induction (p := fun W _ =>
    Verma.comp N (tauEv cL hL W) Y = constantCoeff (Verma.comp N W Y)) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨Z, rfl⟩
    have e : tauEv cL hL (neg Z.2.word) = neg Z.2.word := Verma.baseChange_neg _ _ _ _
    rw [e, comp_neg_word, comp_neg_word]
    split_ifs <;> simp
  · simp
  · intro U V _ _ hU hV
    simp only [map_add, Pi.add_apply, hU, hV]
  · intro a U _ hU
    rw [LinearMap.map_smulₛₗ, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, hU, smul_eq_mul,
      smul_eq_mul, map_mul]

/-- The `τ`-Jantzen submodule `J_τ^i`: the values at `X = 0` of the vectors of `𝒥_τ^{(i)}`
(l.2940–2943). -/
noncomputable def tauJ (cL hL : ℂ⟦X⟧) (i : ℕ) :
    Submodule ℂ (Verma ℂ (constantCoeff cL) (constantCoeff hL)) where
  carrier := {x | ∃ W, InTau cL hL i W ∧ tauEv cL hL W = x}
  add_mem' := by
    rintro _ _ ⟨U, hU, rfl⟩ ⟨W, hW, rfl⟩
    exact ⟨U + W, hU.add hW, map_add _ _ _⟩
  zero_mem' := ⟨0, inTau_zero i, map_zero _⟩
  smul_mem' := by
    rintro a _ ⟨W, hW, rfl⟩
    refine ⟨(C a : ℂ⟦X⟧) • W, hW.smul _, ?_⟩
    rw [LinearMap.map_smulₛₗ, constantCoeff_C]

/-- "Each `J_τ^i` is a `Vir`-submodule" (l.2944). -/
theorem tauJ_isVir (i : ℕ) : IsVirSubmodule (tauJ cL hL i) := by
  rintro n _ ⟨W, hW, rfl⟩
  exact ⟨Verma.L n W, hW.L n, tauEv_L n W⟩

theorem tauJ_anti {i i' : ℕ} (h : i ≤ i') : tauJ cL hL i' ≤ tauJ cL hL i := by
  rintro _ ⟨W, hW, rfl⟩
  exact ⟨W, hW.mono h, rfl⟩

/-- `J_τ^1` is the radical of the Shapovalov form at `X = 0` (l.2944–2945). -/
theorem mem_tauJ_one {x : Verma ℂ (constantCoeff cL) (constantCoeff hL)} :
    x ∈ tauJ cL hL 1 ↔ ∀ u, shap (constantCoeff cL) (constantCoeff hL) u x = 0 := by
  constructor
  · rintro ⟨W, hW, rfl⟩ u
    obtain ⟨U, rfl⟩ := tauEv_surjective u
    rw [shap_tauEv]
    have h := hW U
    rw [pow_one] at h
    exact X_dvd_iff.1 h
  · intro h
    obtain ⟨W, rfl⟩ := tauEv_surjective x
    refine ⟨W, fun U => ?_, rfl⟩
    rw [pow_one, X_dvd_iff, ← shap_tauEv]
    exact h _

theorem tauJ_one : tauJ cL hL 1 = jantzen (constantCoeff cL) (constantCoeff hL) 1 := by
  refine SetLike.coe_injective ?_
  rw [jantzen_one_eq_radical]
  ext x
  exact mem_tauJ_one

/-- On level `N`, `J_τ^i` is the layer of order `i` of the matrix `G_N(c(X),Δ(X))`. -/
theorem pbwCoord_mem_tauJ {N i : ℕ} {v : Nat.Partition N → ℂ} :
    pbwCoord N v ∈ tauJ cL hL i ↔ v ∈ layer (gram cL hL N) i := by
  constructor
  · rintro ⟨W, hW, hev⟩
    refine ⟨Verma.comp N W, fun Y => ?_, fun Y => family_of_inTau (hW.comp N) Y⟩
    rw [← comp_tauEv, hev, comp_pbwCoord_same]
  · rintro ⟨V, hV0, hd⟩
    refine ⟨pbwCoord N V, inTau_of_family hd, ?_⟩
    rw [tauEv_pbwCoord]
    congr 1
    funext Y
    exact hV0 Y

/-- The level components of a vector of `J_τ^i` lie in `J_τ^i`. -/
theorem tauJ_comp {i : ℕ} {x : Verma ℂ (constantCoeff cL) (constantCoeff hL)}
    (hx : x ∈ tauJ cL hL i) (N : ℕ) : pbwCoord N (Verma.comp N x) ∈ tauJ cL hL i := by
  obtain ⟨W, hW, rfl⟩ := hx
  refine ⟨pbwCoord N (Verma.comp N W), hW.comp N, ?_⟩
  rw [tauEv_pbwCoord]
  congr 1
  funext Y
  exact (comp_tauEv N W Y).symm

/-- The last deduction of Step 3 with the length-two structure of Step 2 (l.2919–2937,
2944–2947, 2986–2988), on the preimages in `M(c⋆,μ)`: a `Vir`-submodule `J` with
`M(ν₁) ⊂ J ⊂ M(ν₁) + M(ν₂)` that does not contain the generator of `M(ν₂)` equals `M(ν₁)`,
because `M(ν₂)/(M(ν₁) ∩ M(ν₂))` is simple. -/
theorem eq_of_length_two {c h : ℂ} {χ₁ χ₂ : Verma ℂ c h} {J : Submodule ℂ (Verma ℂ c h)}
    (hJ : IsVirSubmodule J) (hV2 : IsVirSubmodule (negSpan χ₂)) (h1 : negSpan χ₁ ≤ J)
    (hle : J ≤ negSpan χ₁ ⊔ negSpan χ₂)
    (hsimple : ∀ W : Submodule ℂ (Verma ℂ c h), IsVirSubmodule W →
      negSpan χ₁ ⊓ negSpan χ₂ ≤ W → W ≤ negSpan χ₂ →
        W = negSpan χ₁ ⊓ negSpan χ₂ ∨ W = negSpan χ₂)
    (h2 : χ₂ ∉ J) : J = negSpan χ₁ := by
  refine le_antisymm (fun x hx => ?_) h1
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 (hle hx)
  have hy₂J : y₂ ∈ J := by
    have := J.sub_mem hx (h1 hy₁)
    rwa [add_sub_cancel_left] at this
  rcases hsimple (J ⊓ negSpan χ₂) (isVirSubmodule_inf hJ hV2) (inf_le_inf_right _ h1)
    inf_le_right with h | h
  · have : y₂ ∈ negSpan χ₁ ⊓ negSpan χ₂ := by rw [← h]; exact ⟨hy₂J, hy₂⟩
    exact Submodule.add_mem _ hy₁ this.1
  · have : χ₂ ∈ J ⊓ negSpan χ₂ := by rw [h]; exact mem_negSpan_self χ₂
    exact absurd this.1 h2

end Virasoro.P2
