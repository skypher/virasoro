import Virasoro.Sphere.Proofs.Sec3FockOps
import Mathlib.Data.Finsupp.Multiset
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Combinatorics.Enumerative.Partition.Basic

/-!
# Levels of the Fock space (sphere paper Lemma 3.2(i))

sphere/paper.tex l.480–482: `dim ℱ_{μ,λ,N} = p(N) = dim M(c,Δ)_N`, so the vectors `l_{-Y}1`,
`|Y| = N`, whose Gram matrix is nondegenerate, form a basis of the level-`N` part.
-/

namespace Virasoro.Sphere

open MvPolynomial

/-- The level-`N` part of the Fock space. -/
noncomputable abbrev levelSub (N : ℕ) : Submodule ℂ Fock :=
  weightedHomogeneousSubmodule ℂ fockWeight N

/-! ### The operators `l_{-k}` raise the level by `k` -/

theorem weight_uVar {j : ℕ} (hj : 0 < j) :
    IsWeightedHomogeneous fockWeight (uVar j : Fock) j := by
  have h := isWeightedHomogeneous_X ℂ fockWeight j.toPNat'
  have e : fockWeight j.toPNat' = j := PNat.toPNat'_coe hj
  rw [e] at h
  exact h

theorem weight_dVar_monomial {j : ℕ} (hj : 0 < j) (d : ℕ+ →₀ ℕ) {n : ℕ}
    (hd : Finsupp.weight fockWeight d = n) :
    (∃ n' : ℕ, n = n' + j ∧
      IsWeightedHomogeneous fockWeight (dVar j (monomial d (1 : ℂ))) n') ∨
    dVar j (monomial d (1 : ℂ)) = 0 := by
  by_cases h0 : d j.toPNat' = 0
  · refine Or.inr ?_
    show pderiv j.toPNat' (monomial d (1 : ℂ)) = 0
    rw [pderiv_monomial, h0]
    simp
  · refine Or.inl ⟨Finsupp.weight fockWeight (d - Finsupp.single j.toPNat' 1), ?_, ?_⟩
    · have hle : Finsupp.single j.toPNat' 1 ≤ d := by
        rw [Finsupp.single_le_iff]
        omega
      have hsplit : d = (d - Finsupp.single j.toPNat' 1) + Finsupp.single j.toPNat' 1 :=
        (tsub_add_cancel_of_le hle).symm
      have hw : Finsupp.weight fockWeight (Finsupp.single j.toPNat' 1) = j := by
        rw [Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
        show 1 • ((j.toPNat' : ℕ)) = j
        rw [PNat.toPNat'_coe hj]
        simp
      rw [← hd]
      conv_lhs => rw [hsplit]
      rw [map_add, hw]
    · show IsWeightedHomogeneous fockWeight (pderiv j.toPNat' (monomial d (1 : ℂ))) _
      rw [pderiv_monomial]
      exact isWeightedHomogeneous_monomial _ _ _ rfl

theorem ffOpMono_neg_homog (μ lam : ℂ) (K : ℕ) (hK : 1 ≤ K) (d : ℕ+ →₀ ℕ) {n : ℕ}
    (hd : Finsupp.weight fockWeight d = n) :
    ffOpMono μ lam (-(K : ℤ)) d ∈ levelSub (n + K) := by
  have hk0 : ¬ (-(K : ℤ)) = 0 := by omega
  have hkp : ¬ 0 < (-(K : ℤ)) := by omega
  have hKK : (-(-(K : ℤ))).toNat = K := by simp
  have hmono : IsWeightedHomogeneous fockWeight (monomial d (1 : ℂ)) n :=
    isWeightedHomogeneous_monomial _ _ _ hd
  unfold ffOpMono
  simp only [hk0, hkp, if_false, hKK]
  refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
  · refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    have hj1 : 0 < j := (Finset.mem_Icc.mp hj).1
    rcases weight_dVar_monomial hj1 d hd with ⟨n', hn', hh⟩ | h0
    · have h := (weight_uVar (show 0 < j + K by omega)).mul hh
      rw [mem_weightedHomogeneousSubmodule, show n + K = j + K + n' by omega]
      exact h
    · rw [h0, mul_zero]
      exact Submodule.zero_mem _
  · have hsum : (∑ j ∈ Finset.Icc 1 (K - 1),
        ((j * (K - j) : ℕ) : ℂ) • ((uVar j : Fock) * uVar (K - j))) ∈ levelSub K := by
      refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
      have hj1 := Finset.mem_Icc.mp hj
      have h := (weight_uVar (show 0 < j by omega)).mul (weight_uVar (show 0 < K - j by omega))
      have e : j + (K - j) = K := by omega
      rw [e] at h
      exact h
    have h := (mem_weightedHomogeneousSubmodule ℂ fockWeight K _).mp hsum |>.mul hmono
    rw [mem_weightedHomogeneousSubmodule, add_comm n K]
    exact h
  · have h := ((isWeightedHomogeneous_C fockWeight
      (2 * (K : ℂ) * (μ * (K : ℂ) - algebraMap ℂ ℂ Complex.I * lam))).mul
        (weight_uVar (show 0 < K by omega))).mul hmono
    rw [mem_weightedHomogeneousSubmodule, show n + K = 0 + K + n by omega]
    exact h

theorem ffOp_neg_homog (μ lam : ℂ) (K : ℕ) (hK : 1 ≤ K) (f : Fock) {n : ℕ}
    (hf : IsWeightedHomogeneous fockWeight f n) :
    IsWeightedHomogeneous fockWeight (ffOp μ lam (-(K : ℤ)) f) (n + K) := by
  rw [← mem_weightedHomogeneousSubmodule, as_sum f, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have e : monomial d (coeff d f) = coeff d f • monomial d (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, ffOp_monomial]
  exact Submodule.smul_mem _ _ (ffOpMono_neg_homog μ lam K hK d (hf (mem_support_iff.mp hd)))

/-- `l_{-w}1` has level `|w|`. -/
theorem fockWord_homog (μ lam : ℂ) : ∀ w : List ℕ, PosWord w →
    IsWeightedHomogeneous fockWeight (fockWord μ lam w) w.sum := by
  intro w
  induction w with
  | nil => intro _; exact isWeightedHomogeneous_one ℂ fockWeight
  | cons y w ih =>
    intro hw
    have hy : 0 < y := hw y List.mem_cons_self
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have h := ffOp_neg_homog μ lam y hy _ (ih hw')
    rw [List.sum_cons, add_comm]
    exact h

/-! ### `dim ℱ_N ≤ p(N)` -/

/-- The partition `1^{d₁} 2^{d₂} ⋯` of the weight of the exponent `d`. -/
noncomputable def partOfExp (d : ℕ+ →₀ ℕ) {N : ℕ} (hd : Finsupp.weight fockWeight d = N) :
    Nat.Partition N where
  parts := (Finsupp.toMultiset d).map fun m : ℕ+ => (m : ℕ)
  parts_pos := by
    intro i hi
    obtain ⟨m, _, rfl⟩ := Multiset.mem_map.mp hi
    exact m.pos
  parts_sum := by
    rw [Finsupp.toMultiset_map, Finsupp.sum_toMultiset,
      Finsupp.sum_mapDomain_index (by simp) (by intro a m n; rw [add_smul]), ← hd,
      Finsupp.weight_apply]
    rfl

/-- The monomial `∏ u_m^{(number of parts of Y equal to m)}`. -/
noncomputable def partMono {N : ℕ} (Y : Nat.Partition N) : Fock :=
  monomial (Multiset.toFinsupp (Y.parts.map Nat.toPNat')) 1

theorem partMono_partOfExp (d : ℕ+ →₀ ℕ) {N : ℕ} (hd : Finsupp.weight fockWeight d = N) :
    partMono (partOfExp d hd) = monomial d 1 := by
  unfold partMono partOfExp
  simp only [Multiset.map_map]
  have : (Finsupp.toMultiset d).map (Nat.toPNat' ∘ fun m : ℕ+ => (m : ℕ)) = Finsupp.toMultiset d := by
    conv_rhs => rw [← Multiset.map_id (Finsupp.toMultiset d)]
    apply Multiset.map_congr rfl
    intro m _
    exact PNat.coe_toPNat' m
  rw [this, Finsupp.toMultiset_toFinsupp]

theorem levelSub_le_span (N : ℕ) :
    levelSub N ≤ Submodule.span ℂ (Set.range (partMono : Nat.Partition N → Fock)) := by
  intro f hf
  rw [mem_weightedHomogeneousSubmodule] at hf
  rw [as_sum f]
  refine Submodule.sum_mem _ fun d hd => ?_
  have e : monomial d (coeff d f) = coeff d f • monomial d (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, ← partMono_partOfExp d (hf (mem_support_iff.mp hd))]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

instance levelSub_finite (N : ℕ) : FiniteDimensional ℂ (levelSub N) := by
  have : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (partMono : Nat.Partition N → Fock))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le (levelSub_le_span N)

theorem finrank_levelSub_le (N : ℕ) :
    Module.finrank ℂ (levelSub N) ≤ Fintype.card (Nat.Partition N) := by
  have : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (partMono : Nat.Partition N → Fock))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact (Submodule.finrank_mono (levelSub_le_span N)).trans (finrank_range_le_card _)

/-! ### Vectors with a nondegenerate Gram matrix form a basis of the level -/

theorem gram_li {N : ℕ} (v : Nat.Partition N → Fock)
    (G : Matrix (Nat.Partition N) (Nat.Partition N) ℂ) (hG : G.det ≠ 0)
    (hiso : ∀ Y Y', fockForm (v Y) (v Y') = G Y Y') (z : Nat.Partition N → ℂ)
    (hz : ∑ Y, z Y • v Y = 0) : z = 0 := by
  have hmul : G.mulVec z = 0 := by
    funext Y'
    have h := congrArg (fockForm (v Y')) hz
    rw [fockForm_sum_right, fockForm_zero_right] at h
    simp only [fockForm_smul_right, hiso] at h
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← h]
    exact Finset.sum_congr rfl fun Y _ => mul_comm _ _
  exact Matrix.eq_zero_of_mulVec_eq_zero hG hmul

/-- Lemma 3.2(i), the level-by-level bijection: vectors of level `N` indexed by the partitions
of `N` whose Gram matrix under (3.1) is nondegenerate form a basis of the level-`N` part. -/
theorem level_basis {N : ℕ} (v : Nat.Partition N → Fock)
    (hv : ∀ Y, IsWeightedHomogeneous fockWeight (v Y) N)
    (G : Matrix (Nat.Partition N) (Nat.Partition N) ℂ) (hG : G.det ≠ 0)
    (hiso : ∀ Y Y', fockForm (v Y) (v Y') = G Y Y') (f : Fock)
    (hf : IsWeightedHomogeneous fockWeight f N) :
    ∃! x : Nat.Partition N → ℂ, f = ∑ Y, x Y • v Y := by
  let v' : Nat.Partition N → levelSub N := fun Y => ⟨v Y, hv Y⟩
  have hli : LinearIndependent ℂ v' := by
    rw [Fintype.linearIndependent_iff]
    intro z hz Y
    have h := congrArg Subtype.val hz
    rw [Submodule.coe_sum] at h
    have h2 : ∑ Y, z Y • v Y = 0 := h
    exact congrFun (gram_li v G hG hiso z h2) Y
  have hcard : Fintype.card (Nat.Partition N) = Module.finrank ℂ (levelSub N) :=
    le_antisymm hli.fintype_card_le_finrank (finrank_levelSub_le N)
  have htop := hli.span_eq_top_of_card_eq_finrank' hcard
  have hmem : (⟨f, hf⟩ : levelSub N) ∈ Submodule.span ℂ (Set.range v') := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have hx' := congrArg Subtype.val hx
  rw [Submodule.coe_sum] at hx'
  have hx2 : ∑ Y, x Y • v Y = f := hx'
  refine ⟨x, hx2.symm, fun x' hx3 => ?_⟩
  have hz : ∑ Y, (x' - x) Y • v Y = 0 := by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
    rw [← hx3, hx2, sub_self]
  exact sub_eq_zero.mp (gram_li v G hG hiso _ hz)

end Virasoro.Sphere
