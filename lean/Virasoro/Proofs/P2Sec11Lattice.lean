import Virasoro.Proofs.P2Sec11VertexBase
import Virasoro.Proofs.JantzenLevel

/-!
# The Jantzen lattices `𝒥^{(i)}` of Section 11 (paper.tex l.2330–2372)

`𝒥^{(i)}` is the set of vectors `W(x)` of `M(c,μ+x)` over `ℂ[x]` with
`B_x(u, W(x)) ∈ x^i ℂ[x]` for every `u` (Definition 5.2, used through polynomial families).  It
is a `Vir`-submodule, `x𝒥^{(i-1)} = 𝒥^{(i)} ∩ x M` (equation (11.2)), and its image under
`x ↦ 0` is the Jantzen layer `J^i(c,μ)`.
-/

namespace Virasoro

open Polynomial Verma

variable {c μ : ℂ}

theorem latEv0_c (c : ℂ) : evalRingHom (0 : ℂ) (C c) = c := by simp

theorem latEv0_h (μ : ℂ) : evalRingHom (0 : ℂ) (C μ + X) = μ := by simp

/-- Evaluation at `x = 0`: `M(c,μ+x) → M(c,μ)`. -/
noncomputable def latEv0 (c μ : ℂ) :
    Verma ℂ[X] (C c) (C μ + X) →ₛₗ[evalRingHom (0 : ℂ)] Verma ℂ c μ :=
  Verma.baseChange (evalRingHom (0 : ℂ)) (latEv0_c c) (latEv0_h μ)

/-- The lattice `𝒥^{(i)}`: `B_x(u, W) ∈ x^i ℂ[x]` for all `u`. -/
def InLat (c μ : ℂ) (i : ℕ) (W : Verma ℂ[X] (C c) (C μ + X)) : Prop :=
  ∀ u, (X : ℂ[X]) ^ i ∣ shap (C c) (C μ + X) u W

theorem inLat_zero (i : ℕ) : InLat c μ i 0 := fun u => by rw [map_zero]; exact dvd_zero _

theorem InLat.add {i : ℕ} {U W : Verma ℂ[X] (C c) (C μ + X)} (hU : InLat c μ i U)
    (hW : InLat c μ i W) : InLat c μ i (U + W) := fun u => by
  rw [map_add]; exact dvd_add (hU u) (hW u)

theorem InLat.smul {i : ℕ} {U : Verma ℂ[X] (C c) (C μ + X)} (a : ℂ[X]) (hU : InLat c μ i U) :
    InLat c μ i (a • U) := fun u => by
  rw [map_smul, smul_eq_mul]; exact Dvd.dvd.mul_left (hU u) _

theorem InLat.sub {i : ℕ} {U W : Verma ℂ[X] (C c) (C μ + X)} (hU : InLat c μ i U)
    (hW : InLat c μ i W) : InLat c μ i (U - W) := fun u => by
  rw [map_sub]; exact dvd_sub (hU u) (hW u)

theorem InLat.mono {i i' : ℕ} (h : i ≤ i') {U : Verma ℂ[X] (C c) (C μ + X)}
    (hU : InLat c μ i' U) : InLat c μ i U := fun u => (pow_dvd_pow _ h).trans (hU u)

theorem inLat_sum {i : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Verma ℂ[X] (C c) (C μ + X))
    (h : ∀ j ∈ s, InLat c μ i (f j)) : InLat c μ i (∑ j ∈ s, f j) := fun u => by
  rw [map_sum]; exact Finset.dvd_sum fun j hj => h j hj u

/-- `𝒥^{(i)}` is stable under all modes (contravariance of `B_x`). -/
theorem InLat.L {i : ℕ} {U : Verma ℂ[X] (C c) (C μ + X)} (hU : InLat c μ i U) (n : ℤ) :
    InLat c μ i (Verma.L n U) := fun u => by
  have h := (isShapovalov_shap (c := C c) (h := C μ + (X : ℂ[X]))).2 (-n) u U
  rw [neg_neg] at h
  rw [← h]
  exact hU _

/-- `x𝒥^{(i)} ⊂ 𝒥^{(i+1)}`. -/
theorem InLat.X_smul {i : ℕ} {V : Verma ℂ[X] (C c) (C μ + X)} (hV : InLat c μ i V) :
    InLat c μ (i + 1) ((X : ℂ[X]) • V) := fun u => by
  rw [map_smul, smul_eq_mul, pow_succ']
  exact mul_dvd_mul_left _ (hV u)

/-- Equation (11.2): `𝒥^{(i+1)} ∩ xM ⊂ x𝒥^{(i)}`. -/
theorem inLat_of_X_smul {i : ℕ} {V : Verma ℂ[X] (C c) (C μ + X)}
    (hV : InLat c μ (i + 1) ((X : ℂ[X]) • V)) : InLat c μ i V := fun u => by
  have h := hV u
  rw [map_smul, smul_eq_mul, pow_succ'] at h
  exact (mul_dvd_mul_iff_left X_ne_zero).1 h

/-- The kernel of `x ↦ 0` is `x M(c,μ+x)`. -/
theorem latEv0_eq_zero {U : Verma ℂ[X] (C c) (C μ + X)} (hU : latEv0 c μ U = 0) :
    ∃ V : Verma ℂ[X] (C c) (C μ + X), U = (X : ℂ[X]) • V := by
  refine Verma.baseChange_eq_zero (evalRingHom (0 : ℂ)) (latEv0_c c) (latEv0_h μ) (π := X) ?_ U hU
  intro a ha
  have : (X : ℂ[X]) ∣ a := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero]
    exact ha
  exact this

theorem latEv0_pbwCoord (N : ℕ) (w : Nat.Partition N → ℂ[X]) :
    latEv0 c μ (pbwCoord N w) = pbwCoord N fun Y => (w Y).eval 0 :=
  Verma.baseChange_pbwCoord _ _ _ N w

theorem latEv0_L (n : ℤ) (U : Verma ℂ[X] (C c) (C μ + X)) :
    latEv0 c μ (Verma.L n U) = Verma.L n (latEv0 c μ U) :=
  Verma.baseChange_L _ _ _ n U

/-- A vector whose level-`N` component vanishes is `B`-orthogonal to level `N`. -/
theorem shap_level_comp_zero {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R} {N : ℕ}
    {v W : Verma R c h} (hv : v ∈ level N) (hW : comp N W = 0) : shap c h v W = 0 := by
  obtain ⟨S, hS⟩ := exists_decomp W
  rw [hS, map_sum]
  refine Finset.sum_eq_zero fun M _ => ?_
  by_cases hM : M = N
  · subst hM
    rw [hW, map_zero, map_zero]
  · exact shap_level_ne (Ne.symm hM) hv ⟨_, rfl⟩

/-- The level components of a vector of `𝒥^{(i)}` lie in `𝒥^{(i)}`. -/
theorem InLat.comp {i : ℕ} {W : Verma ℂ[X] (C c) (C μ + X)} (hW : InLat c μ i W) (N : ℕ) :
    InLat c μ i (pbwCoord N (Verma.comp N W)) := by
  intro u
  refine induction_neg (P := fun u => (X : ℂ[X]) ^ i ∣
    shap (C c) (C μ + X) u (pbwCoord N (Verma.comp N W))) ?_ ?_ ?_ u
  · intro w hw
    have hl : neg (c := C c) (h := C μ + (X : ℂ[X])) w ∈ level w.sum :=
      neg_mem_level _ w hw le_rfl
    by_cases hN : w.sum = N
    · have h0 : shap (C c) (C μ + X) (neg w) (W - pbwCoord N (Verma.comp N W)) = 0 := by
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

/-- A polynomial family of order `i` (Definition 5.2) is a homogeneous vector of `𝒥^{(i)}`. -/
theorem inLat_of_family {N i : ℕ} {w : Nat.Partition N → ℂ[X]}
    (hw : ∀ Y, (X : ℂ[X]) ^ i ∣ ((gramShift c μ N).mulVec w) Y) : InLat c μ i (pbwCoord N w) := by
  intro u
  refine induction_neg (P := fun u => (X : ℂ[X]) ^ i ∣
    shap (C c) (C μ + X) u (pbwCoord N w)) ?_ ?_ ?_ u
  · intro w' hw'
    have hl : neg (c := C c) (h := C μ + (X : ℂ[X])) w' ∈ level w'.sum :=
      neg_mem_level _ w' hw' le_rfl
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

theorem family_of_inLat {N i : ℕ} {w : Nat.Partition N → ℂ[X]}
    (hw : InLat c μ i (pbwCoord N w)) (Y : Nat.Partition N) :
    (X : ℂ[X]) ^ i ∣ ((gramShift c μ N).mulVec w) Y := by
  have h := hw (neg Y.word)
  rw [shap_neg_pbwCoord] at h
  exact h

theorem IsJFamily.inLat {N i : ℕ} {a : Nat.Partition N → ℂ} {w : Nat.Partition N → ℂ[X]}
    (h : IsJFamily c μ N i a w) : InLat c μ i (pbwCoord N w) := inLat_of_family h.2

theorem IsJFamily.ev0 {N i : ℕ} {a : Nat.Partition N → ℂ} {w : Nat.Partition N → ℂ[X]}
    (h : IsJFamily c μ N i a w) : latEv0 c μ (pbwCoord N w) = pbwCoord N a := by
  rw [latEv0_pbwCoord]
  congr 1
  exact funext h.1

/-- The level coordinates commute with `x ↦ 0`. -/
theorem comp_ev0 (N : ℕ) (W : Verma ℂ[X] (C c) (C μ + X)) (Y : Nat.Partition N) :
    Verma.comp N (latEv0 c μ W) Y = (Verma.comp N W Y).eval 0 := by
  classical
  have hW : W ∈ Submodule.span ℂ[X] (Set.range fun Y : (Σ N : ℕ, Nat.Partition N) =>
      neg (c := C c) (h := C μ + (X : ℂ[X])) Y.2.word) := by
    rw [span_neg_word_eq_top]; trivial
  refine Submodule.span_induction (p := fun W _ =>
    Verma.comp N (latEv0 c μ W) Y = (Verma.comp N W Y).eval 0) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨Z, rfl⟩
    have e : latEv0 c μ (neg Z.2.word) = neg Z.2.word := Verma.baseChange_neg _ _ _ _
    rw [e, comp_neg_word, comp_neg_word]
    split_ifs <;> simp
  · simp
  · intro U V _ _ hU hV
    rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, hU, hV, eval_add]
  · intro a U _ hU
    rw [LinearMap.map_smulₛₗ, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, hU, smul_eq_mul,
      smul_eq_mul, eval_mul, coe_evalRingHom]

/-- The image of `𝒥^{(i)}` under `x ↦ 0` lies in `J^i(c,μ)`. -/
theorem InLat.ev0_mem {i : ℕ} {W : Verma ℂ[X] (C c) (C μ + X)} (hW : InLat c μ i W) :
    latEv0 c μ W ∈ jantzen c μ i := by
  obtain ⟨S, hS⟩ := exists_decomp W
  rw [hS, map_sum]
  refine Submodule.sum_mem _ fun M _ => ?_
  rw [latEv0_pbwCoord]
  exact pbwCoord_mem_jantzen ⟨Verma.comp M W, fun Y => rfl, family_of_inLat (hW.comp M)⟩

/-- Every vector of `J^i(c,μ)` is the value at `x = 0` of a vector of `𝒥^{(i)}`. -/
theorem exists_lift {i : ℕ} {x : Verma ℂ c μ} (hx : x ∈ jantzen c μ i) :
    ∃ W, InLat c μ i W ∧ latEv0 c μ W = x := by
  unfold jantzen at hx
  refine Submodule.iSup_induction (motive := fun x => ∃ W, InLat c μ i W ∧ latEv0 c μ W = x) _ hx
    ?_ ?_ ?_
  · rintro N _ ⟨v₀, ⟨w, hw0, hdvd⟩, rfl⟩
    exact ⟨pbwCoord N w, inLat_of_family hdvd, IsJFamily.ev0 ⟨hw0, hdvd⟩⟩
  · exact ⟨0, inLat_zero i, map_zero _⟩
  · rintro x y ⟨U, hU, rfl⟩ ⟨W, hW, rfl⟩
    exact ⟨U + W, hU.add hW, map_add _ _ _⟩

end Virasoro
