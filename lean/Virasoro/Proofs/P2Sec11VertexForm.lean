import Virasoro.Proofs.P2Sec11Lattice

/-!
# Proposition 11.2(i), induction step: the form `ρ^{(i)}` on `J^i` (paper.tex l.2423–2437)

Assume part (i) at order `i`.  For `a(x), b(x) ∈ 𝒥^{(i+1)}`: `ρ_x(a(x),b(x)) ∈ x^{i+1}ℂ[x]`
(l.2423–2427); the coefficient of `x^{i+1}` depends only on `a(0), b(0)` (l.2427–2432); and it
satisfies the exact `V_d(1)` Ward identity (l.2432–2437).
-/

namespace Virasoro

open Polynomial Verma

variable {c μ d : ℂ}
  {T : Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] ℂ[X]}

/-- The primary pairing is symmetric, over any coefficient ring (equation (10.2)). -/
theorem primary_symm' {R : Type*} [CommRing R] [Algebra ℚ R] {c h d : R}
    {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hT : IsPrimaryPairing d T)
    (u v : Verma R c h) : T u v = T v u := by
  have hT2 : IsTwoWeightPairing d T := hT
  have h := twoWeight_unique hT2 hT2.flip
  conv_lhs => rw [h]
  rfl

/-- Part (i) of Proposition 11.2 at order `i`, for all vectors of `𝒥^{(i)}`:
`ρ_x(𝒥^{(i)},𝒥^{(i)}) ⊂ x^i ℂ[x]`, and `[x^i]ρ_x(U,W) = 0` when `W(0) ∈ J^{i+1}`. -/
def VertexGen (c μ : ℂ)
    (T : Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] ℂ[X])
    (i : ℕ) : Prop :=
  ∀ U W, InLat c μ i U → InLat c μ i W → (X : ℂ[X]) ^ i ∣ T U W ∧
    ((∃ W', InLat c μ (i + 1) W' ∧ latEv0 c μ W' = latEv0 c μ W) → (T U W).coeff i = 0)

/-- The clauses of part (i) for homogeneous families give them for all vectors of the lattice
(sum over the level components). -/
theorem vertexGen_of_clauses {i : ℕ}
    (H : ∀ (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
      (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]),
      IsJFamily c μ N₁ i a wa → IsJFamily c μ N₂ i a₂ wb →
        VertexClausesAt c μ d i T N₁ N₂ a a₂ wa wb) : VertexGen c μ T i := by
  intro U W hU hW
  obtain ⟨S, hS⟩ := exists_decomp U
  obtain ⟨S', hS'⟩ := exists_decomp W
  have eU : T U W = ∑ M ∈ S, T (pbwCoord M (Verma.comp M U)) W := by
    conv_lhs => rw [hS]
    rw [map_sum, LinearMap.sum_apply]
  have eW : ∀ V, T V W = ∑ M' ∈ S', T V (pbwCoord M' (Verma.comp M' W)) := fun V => by
    conv_lhs => rw [hS']
    rw [map_sum]
  have e : T U W = ∑ M ∈ S, ∑ M' ∈ S',
      T (pbwCoord M (Verma.comp M U)) (pbwCoord M' (Verma.comp M' W)) :=
    eU.trans (Finset.sum_congr rfl fun M _ => eW _)
  have key : ∀ M M', VertexClausesAt c μ d i T M M' (fun Y => (Verma.comp M U Y).eval 0)
      (fun Y => (Verma.comp M' W Y).eval 0) (Verma.comp M U) (Verma.comp M' W) :=
    fun M M' => H M M' _ _ _ _ ⟨fun _ => rfl, family_of_inLat (hU.comp M)⟩
      ⟨fun _ => rfl, family_of_inLat (hW.comp M')⟩
  refine ⟨?_, ?_⟩
  · rw [e]
    exact Finset.dvd_sum fun M _ => Finset.dvd_sum fun M' _ => (key M M').1
  · rintro ⟨W', hW', hev⟩
    rw [e, finsetSum_coeff]
    refine Finset.sum_eq_zero fun M _ => ?_
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun M' _ => ?_
    refine (key M M').2.2.2 (Or.inr ⟨Verma.comp M' W', fun Y => ?_,
      family_of_inLat (hW'.comp M')⟩)
    rw [← comp_ev0, hev, comp_ev0]

section Step

variable {i : ℕ} (hT : IsPrimaryPairing (C d) T) (G : VertexGen c μ T i)

include G in
/-- `ρ_x(𝒥^{(i+1)},𝒥^{(i+1)}) ⊂ x^{i+1}ℂ[x]` (l.2423–2427). -/
theorem vg_dvd {U W : Verma ℂ[X] (C c) (C μ + X)} (hU : InLat c μ (i + 1) U)
    (hW : InLat c μ (i + 1) W) : (X : ℂ[X]) ^ (i + 1) ∣ T U W := by
  obtain ⟨h1, h2⟩ := G U W (hU.mono (Nat.le_succ i)) (hW.mono (Nat.le_succ i))
  rw [X_pow_dvd_iff] at h1 ⊢
  intro k hk
  rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
  · exact h1 k hk
  · exact h2 ⟨W, hW, rfl⟩

include G in
/-- Independence of the lift in the first slot (l.2427–2431). -/
theorem vg_congr_left {U U' W : Verma ℂ[X] (C c) (C μ + X)} (hU : InLat c μ (i + 1) U)
    (hU' : InLat c μ (i + 1) U') (hW : InLat c μ (i + 1) W) (h : latEv0 c μ U = latEv0 c μ U') :
    (T U W).coeff (i + 1) = (T U' W).coeff (i + 1) := by
  obtain ⟨V, hV⟩ := latEv0_eq_zero (U := U - U') (by rw [map_sub, h, sub_self])
  have hVl : InLat c μ i V := inLat_of_X_smul (hV ▸ hU.sub hU')
  have e : T U W = T U' W + X * T V W := by
    have : U = U' + (X : ℂ[X]) • V := by rw [← hV]; abel
    rw [this, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [e, coeff_add, coeff_X_mul,
    (G V W hVl (hW.mono (Nat.le_succ i))).2 ⟨W, hW, rfl⟩, add_zero]

include hT G in
/-- Independence of the lift in the second slot ("by symmetry", l.2431–2432). -/
theorem vg_congr_right {U W W' : Verma ℂ[X] (C c) (C μ + X)} (hU : InLat c μ (i + 1) U)
    (hW : InLat c μ (i + 1) W) (hW' : InLat c μ (i + 1) W') (h : latEv0 c μ W = latEv0 c μ W') :
    (T U W).coeff (i + 1) = (T U W').coeff (i + 1) := by
  rw [primary_symm' hT U W, primary_symm' hT U W']
  exact vg_congr_left G hW hW' hU h

open Classical in
/-- A chosen lift to `𝒥^{(j)}` of a vector of `J^j(c,μ)`. -/
noncomputable def latLift (c μ : ℂ) (j : ℕ) (x : Verma ℂ c μ) : Verma ℂ[X] (C c) (C μ + X) :=
  if h : ∃ W, InLat c μ j W ∧ latEv0 c μ W = x then h.choose else 0

theorem latLift_spec {j : ℕ} {x : Verma ℂ c μ} (hx : x ∈ jantzen c μ j) :
    InLat c μ j (latLift c μ j x) ∧ latEv0 c μ (latLift c μ j x) = x := by
  unfold latLift
  rw [dif_pos (exists_lift hx)]
  exact (exists_lift hx).choose_spec

/-- The `j`-th Jantzen vertex form `ρ^{(j)}(x,y) = [x^j]ρ_x(x(x),y(x))` on `J^j(c,μ)`, through
chosen lifts. -/
noncomputable def rhoJ
    (T : Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] Verma ℂ[X] (C c) (C μ + X) →ₗ[ℂ[X]] ℂ[X])
    (j : ℕ) (x y : Verma ℂ c μ) : ℂ :=
  (T (latLift c μ j x) (latLift c μ j y)).coeff j

include hT G in
/-- `ρ^{(i+1)}` is computed by any lifts (l.2427–2432). -/
theorem rhoJ_eq {U W : Verma ℂ[X] (C c) (C μ + X)} (hU : InLat c μ (i + 1) U)
    (hW : InLat c μ (i + 1) W) :
    (T U W).coeff (i + 1) = rhoJ T (i + 1) (latEv0 c μ U) (latEv0 c μ W) := by
  obtain ⟨h1, h2⟩ := latLift_spec hU.ev0_mem
  obtain ⟨h3, h4⟩ := latLift_spec hW.ev0_mem
  rw [rhoJ, vg_congr_left G hU h1 hW h2.symm, vg_congr_right hT G h1 hW h3 h4.symm]

include hT in
theorem rhoJ_symm (j : ℕ) (x y : Verma ℂ c μ) : rhoJ T j x y = rhoJ T j y x := by
  rw [rhoJ, rhoJ, primary_symm' hT]

include hT G in
theorem rhoJ_add_left {x x' y : Verma ℂ c μ} (hx : x ∈ jantzen c μ (i + 1))
    (hx' : x' ∈ jantzen c μ (i + 1)) (hy : y ∈ jantzen c μ (i + 1)) :
    rhoJ T (i + 1) (x + x') y = rhoJ T (i + 1) x y + rhoJ T (i + 1) x' y := by
  obtain ⟨h1, h2⟩ := latLift_spec hx
  obtain ⟨h1', h2'⟩ := latLift_spec hx'
  obtain ⟨h3, h4⟩ := latLift_spec hy
  have e := rhoJ_eq hT G (h1.add h1') h3
  have e1 : latEv0 c μ (latLift c μ (i + 1) x + latLift c μ (i + 1) x') = x + x' := by
    rw [map_add, h2, h2']
  rw [e1, h4] at e
  rw [← e, map_add, LinearMap.add_apply, coeff_add]
  rfl

include hT G in
theorem rhoJ_smul_left (a : ℂ) {x y : Verma ℂ c μ} (hx : x ∈ jantzen c μ (i + 1))
    (hy : y ∈ jantzen c μ (i + 1)) :
    rhoJ T (i + 1) (a • x) y = a * rhoJ T (i + 1) x y := by
  obtain ⟨h1, h2⟩ := latLift_spec hx
  obtain ⟨h3, h4⟩ := latLift_spec hy
  have e := rhoJ_eq hT G (h1.smul (C a)) h3
  have e1 : latEv0 c μ (C a • latLift c μ (i + 1) x) = a • x := by
    rw [LinearMap.map_smulₛₗ, h2, coe_evalRingHom, eval_C]
  rw [e1, h4] at e
  rw [← e, map_smul, LinearMap.smul_apply, smul_eq_mul, coeff_C_mul]
  rfl

include hT G in
/-- The exact `V_d(1)` Ward identity for `ρ^{(i+1)}` on `J^{i+1}` (l.2432–2437). -/
theorem rhoJ_ward (n : ℤ) {x y : Verma ℂ c μ} (hx : x ∈ jantzen c μ (i + 1))
    (hy : y ∈ jantzen c μ (i + 1)) :
    rhoJ T (i + 1) (Verma.L (-n) x) y - rhoJ T (i + 1) x (Verma.L n y) =
      rhoJ T (i + 1) (Verma.L 0 x) y - rhoJ T (i + 1) x (Verma.L 0 y) +
        (n : ℂ) * d * rhoJ T (i + 1) x y := by
  obtain ⟨h1, h2⟩ := latLift_spec hx
  obtain ⟨h3, h4⟩ := latLift_spec hy
  have e := congrArg (fun q : ℂ[X] => q.coeff (i + 1))
    (hT.2 n (latLift c μ (i + 1) x) (latLift c μ (i + 1) y))
  have hn : ((n : ℂ[X])) * C d = C ((n : ℂ) * d) := by
    rw [map_mul, map_intCast]
  simp only [coeff_sub, coeff_add, hn, coeff_C_mul] at e
  rw [rhoJ_eq hT G (h1.L (-n)) h3, rhoJ_eq hT G h1 (h3.L n), rhoJ_eq hT G (h1.L 0) h3,
    rhoJ_eq hT G h1 (h3.L 0), rhoJ_eq hT G h1 h3, latEv0_L, latEv0_L, latEv0_L, latEv0_L, h2, h4] at e
  exact e

end Step

end Virasoro
