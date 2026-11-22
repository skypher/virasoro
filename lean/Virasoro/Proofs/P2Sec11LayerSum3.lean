import Virasoro.Proofs.P2Sec11LayerSum2

/-!
# Proposition 11.2(ii), first step (paper.tex l.2461–2485)

`F_N(c⋆,μ+x,d) = ∑_a ρ_x(v_a(x),v_a(x)) / (x^{e_a} u_a(x))`; by part (i) every factor `x^{e_a}`
cancels, so `F_N(c⋆,μ+x,d)` is regular at `x = 0` with value
`∑_i Tr_{J^i_N/J^{i+1}_N}((B̄^{(i)}_N)⁻¹ ρ̄^{(i)}_N)`, the trace of the layer `i` being computed in
the basis `{v_a(0) : e_a = i}`, which diagonalizes `B̄^{(i)}_N` with diagonal entries `u_a(0)`.
-/

namespace Virasoro

open scoped LaurentSeries
open Matrix

variable {c μ d : ℂ} {N : ℕ} {w : Nat.Partition N → Nat.Partition N → PowerSeries ℂ}
  {e : Nat.Partition N → ℕ} {u : Nat.Partition N → PowerSeries ℂ}

theorem jantzenLayer_eq_span (h : OrthBasis (gramLocal c μ N) w e u) (j : ℕ) :
    jantzenLayer c μ N j = Submodule.span ℂ (val0 w '' {a | j ≤ e a}) := by
  rw [jantzenLayer_eq_layer, h.layer_eq_span]

/-- `B^{(i)}(v_a(0),v_b(0)) = δ_{ab} u_a(0)` for `e_a = i ≤ e_b` (l.2470–2472). -/
theorem jform_val (h : OrthBasis (gramLocal c μ N) w e u) (a b : Nat.Partition N)
    (hab : e a ≤ e b) :
    jform c μ N (e a) (val0 w a) (val0 w b) =
      if a = b then PowerSeries.constantCoeff (u a) else 0 := by
  rw [jform_eq_psForm c μ (h.psFam a le_rfl) (h.psFam b hab), h.psForm_val]

/-- The trace of the layer `i` in the basis `{v_a(0) : e_a = i}` (l.2470–2472). -/
theorem isLayerTrace_orth (h : OrthBasis (gramLocal c μ N) w e u) (i : ℕ) :
    IsLayerTrace c μ d N i (∑ a : {a // e a = i},
      (PowerSeries.constantCoeff (u a.1))⁻¹ * vform c μ d N i (val0 w a.1) (val0 w a.1)) := by
  have hr : Set.range (fun a : {a // e a = i} => val0 w a.1) = val0 w '' {a | e a = i} := by
    have := Set.range_comp (val0 w) (Subtype.val : {a // e a = i} → Nat.Partition N)
    rw [Subtype.range_coe_subtype] at this
    exact this
  have hA : (Matrix.of fun a b : {a // e a = i} => jform c μ N i (val0 w a.1) (val0 w b.1)) =
      Matrix.diagonal fun a : {a // e a = i} => PowerSeries.constantCoeff (u a.1) := by
    refine Matrix.ext fun a b => ?_
    have h1 := jform_val h a.1 b.1 (by rw [a.2, b.2])
    rw [a.2] at h1
    rw [Matrix.of_apply, Matrix.diagonal_apply, h1]
    by_cases hab : a = b
    · rw [if_pos hab, if_pos (congrArg Subtype.val hab)]
    · rw [if_neg hab, if_neg fun h' => hab (Subtype.ext h')]
  have hne : ∀ a : Nat.Partition N, PowerSeries.constantCoeff (u a) ≠ 0 := fun a =>
    (PowerSeries.isUnit_iff_constantCoeff.1 (h.hu a)).ne_zero
  refine ⟨{a // e a = i}, inferInstance, inferInstance, fun a => val0 w a.1, fun a => ?_,
    h.linearIndependent_val0.comp Subtype.val Subtype.val_injective, ?_, ?_, ?_, ?_⟩
  · rw [jantzenLayer_eq_span h]
    exact Submodule.subset_span ⟨a.1, a.2.ge, rfl⟩
  · rw [hr, jantzenLayer_eq_span h (i + 1)]
    refine h.linearIndependent_val0.disjoint_span_image (Set.disjoint_left.2 fun a ha hb => ?_)
    rw [Set.mem_setOf_eq] at ha hb
    omega
  · rw [hr, jantzenLayer_eq_span h (i + 1), jantzenLayer_eq_span h i, ← Submodule.span_union,
      ← Set.image_union]
    congr 2
    ext a
    simp only [Set.mem_union, Set.mem_setOf_eq]
    omega
  · rw [hA, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => hne a.1
  · have hinv : (Matrix.diagonal fun a : {a // e a = i} => PowerSeries.constantCoeff (u a.1))⁻¹ =
        Matrix.diagonal fun a : {a // e a = i} => (PowerSeries.constantCoeff (u a.1))⁻¹ := by
      refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      exact mul_inv_cancel₀ (hne a.1)
    rw [hA, hinv]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg (Ne.symm hb), zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha

theorem OrthBasis.mul_transpose {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {G : Matrix ι ι (PowerSeries K)} {w : ι → ι → PowerSeries K} {e : ι → ℕ}
    {u : ι → PowerSeries K} (h : OrthBasis G w e u) :
    G * (Matrix.of w)ᵀ =
      (Matrix.of w)⁻¹ * Matrix.diagonal fun a => (PowerSeries.X : PowerSeries K) ^ e a * u a := by
  rw [← h.gram, Matrix.mul_assoc (Matrix.of w), ← Matrix.mul_assoc (Matrix.of w)⁻¹,
    Matrix.nonsing_inv_mul _ h.unit, Matrix.one_mul]

/-- `F_N(c,μ+x,d) = ∑_a ρ_x(v_a,v_a)/(x^{e_a}u_a)` is a power series in `x` with constant term
`∑_a ρ^{(e_a)}(v_a(0),v_a(0))/u_a(0)` (l.2472–2480). -/
theorem expand_Frat (HV : VertexPartI c μ d) (h : OrthBasis (gramLocal c μ N) w e u) :
    ∃ Φ : PowerSeries ℂ, expandAt (Frat c d N) μ = HahnSeries.ofPowerSeries ℤ ℂ Φ ∧
      PowerSeries.constantCoeff Φ = ∑ a, (PowerSeries.constantCoeff (u a))⁻¹ *
        vform c μ d N (e a) (val0 w a) (val0 w a) := by
  choose r hr using fun a => (vform_ps HV (h.psFam a le_rfl) (h.psFam a le_rfl)).1
  have hr0 : ∀ a, PowerSeries.constantCoeff (r a) = vform c μ d N (e a) (val0 w a) (val0 w a) := by
    intro a
    have h2 := (vform_ps HV (h.psFam a le_rfl) (h.psFam a le_rfl)).2
    rw [hr a] at h2
    have h3 := PowerSeries.coeff_X_pow_mul (r a) (e a) 0
    rw [zero_add] at h3
    rw [← h2, h3, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  choose ui hui using fun a => (h.hu a).exists_right_inv
  set m : ℕ := ∑ a, e a with hm
  have he : ∀ a, e a ≤ m := fun a => Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ a)
  set dd : Nat.Partition N → PowerSeries ℂ :=
    fun a => (PowerSeries.X : PowerSeries ℂ) ^ (m - e a) * ui a with hdd
  set S : Matrix (Nat.Partition N) (Nat.Partition N) (PowerSeries ℂ) :=
    (Matrix.of w)ᵀ * Matrix.diagonal dd * Matrix.of w with hSdef
  have hDD : (Matrix.diagonal fun a => (PowerSeries.X : PowerSeries ℂ) ^ e a * u a) *
      Matrix.diagonal dd = (PowerSeries.X : PowerSeries ℂ) ^ m • 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1
    funext a
    have h1 : (PowerSeries.X : PowerSeries ℂ) ^ e a * PowerSeries.X ^ (m - e a) =
        PowerSeries.X ^ m := by rw [← pow_add, Nat.add_sub_cancel' (he a)]
    rw [hdd]
    linear_combination (u a * ui a) * h1 + (PowerSeries.X : PowerSeries ℂ) ^ m * hui a
  have hS : gramLocal c μ N * S = (PowerSeries.X : PowerSeries ℂ) ^ m • 1 := by
    rw [hSdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h.mul_transpose,
      Matrix.mul_assoc (Matrix.of w)⁻¹, hDD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.nonsing_inv_mul _ h.unit]
  have hSe : ∀ Y Y', S Y Y' = ∑ a, w a Y * dd a * w a Y' := by
    intro Y Y'
    rw [hSdef, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal]
    rfl
  have hsum : (∑ Y, ∑ Y', S Y Y' * torusLocal c μ d N Y Y') =
      (PowerSeries.X : PowerSeries ℂ) ^ m * ∑ a, ui a * r a := by
    have h1 : (∑ Y, ∑ Y', S Y Y' * torusLocal c μ d N Y Y') =
        ∑ a, dd a * (w a ⬝ᵥ (torusLocal c μ d N).mulVec (w a)) := by
      simp only [hSe, Finset.sum_mul]
      have h2 : ∀ Y, (∑ Y', ∑ a, w a Y * dd a * w a Y' * torusLocal c μ d N Y Y') =
          ∑ a, ∑ Y', w a Y * dd a * w a Y' * torusLocal c μ d N Y Y' := fun Y => Finset.sum_comm
      simp only [h2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => by ring
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h3 : (PowerSeries.X : PowerSeries ℂ) ^ (m - e a) * PowerSeries.X ^ e a =
        PowerSeries.X ^ m := by rw [← pow_add, Nat.sub_add_cancel (he a)]
    rw [hr a, hdd]
    linear_combination (ui a * r a) * h3
  have E := expandAt_Frat_of_scaled c d μ N m S hS
  have hX0 : (HahnSeries.single (m : ℤ) (1 : ℂ) : ℂ⸨X⸩) ≠ 0 := by simp
  refine ⟨∑ a, ui a * r a, ?_, ?_⟩
  · rw [E]
    have e1 : (∑ Y, ∑ Y', S Y Y' * torus (PowerSeries.C c) (PowerSeries.C μ + PowerSeries.X)
        (PowerSeries.C d) N Y Y') = (PowerSeries.X : PowerSeries ℂ) ^ m * ∑ a, ui a * r a := hsum
    rw [e1, map_mul, HahnSeries.ofPowerSeries_X_pow, mul_div_cancel_left₀ _ hX0]
  · rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h4 := congrArg PowerSeries.constantCoeff (hui a)
    rw [map_mul, map_one] at h4
    rw [map_mul, hr0, eq_inv_of_mul_eq_one_right h4]

/-- `Stmt_sub_vertex_layer_sum` (paper.tex l.2461–2485). -/
theorem sub_vertex_layer_sum (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_vertex_layer_sum := by
  intro p p' r s b hset ε k₀ k m hk hm c μ d N
  have HV : VertexPartI c μ d := fun i N₁ N₂ a a₂ wa wb ha hb =>
    vertex_part_i hJ hH hU hF hI p p' r s b hset ε k₀ k m hk hm _
      (Verma.isPrimaryPairing_pairing _) i N₁ N₂ a a₂ wa wb ha hb
  obtain ⟨w, e, u, hw, hu, hd, ho⟩ :=
    exists_orth_basis (gramLocal_isSymm c μ N) (gramLocal_det_ne_zero c μ N)
  have h : OrthBasis (gramLocal c μ N) w e u := ⟨hw, hu, hd, ho⟩
  obtain ⟨Φ, hΦ, hΦ0⟩ := expand_Frat HV h
  obtain ⟨hp, hval⟩ := regular_of_expandAt hΦ
  refine ⟨hp, fun i => ∑ a : {a // e a = i}, (PowerSeries.constantCoeff (u a.1))⁻¹ *
    vform c μ d N i (val0 w a.1) (val0 w a.1), fun i => isLayerTrace_orth h i, fun M hM => ?_⟩
  have he : ∀ a, e a ≤ M := by
    intro a
    by_contra hlt
    push_neg at hlt
    have hmem : val0 w a ∈ jantzenLayer c μ N (e a) := by
      rw [jantzenLayer_eq_span h]
      exact Submodule.subset_span ⟨a, show e a ≤ e a from le_rfl, rfl⟩
    rw [hM (e a) hlt, Submodule.mem_bot] at hmem
    exact h.linearIndependent_val0.ne_zero a hmem
  rw [FvalAt, hval, hΦ0, ← Finset.sum_fiberwise_of_maps_to (g := e) (t := Finset.range (M + 1))
    (fun a _ => Finset.mem_range.2 (Nat.lt_succ_of_le (he a)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (Finset.sum_subtype (Finset.univ.filter fun a => e a = i) (fun x => by simp)
    (fun a => (PowerSeries.constantCoeff (u a))⁻¹ * vform c μ d N (e a) (val0 w a)
      (val0 w a))).trans (Finset.sum_congr rfl fun x _ => ?_)
  rw [x.2]

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_vertex_layer_sum := sub_vertex_layer_sum hJ hH hU hF hI

end Virasoro
