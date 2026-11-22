import Virasoro.Sphere.Proofs.Sec3UVirNorm
import Virasoro.Proofs.PBWSpan
import Virasoro.Proofs.Shapovalov

/-!
# The dimension of the primary spaces (sphere paper, Lemma 3.7, Step 1)

sphere/paper.tex l.1053–1060: the space decomposes orthogonally into Verma modules
`M(c, h₀+n)`, irreducible when the Gram determinants do not vanish; comparing graded characters,
`dim V_N = ∑_{n ≤ N} dim 𝒫_n · p(N-n)`.  The vectors `L_{-Y}P_a` (`P_a` a basis of `𝒫_n`,
`n ≤ N`, `Y` a partition of `N - n`) are a basis of `V_N`.
-/

namespace Virasoro.Sphere

namespace UVir

open Verma

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {R : UVir V}

/-- In the Verma module `L_{-w}|h⟩` is a combination of the `L_{-Y}|h⟩`, `Y` a partition of
`|w|`; in terms of the Shapovalov values. -/
theorem gramWord_straighten (c h : ℂ) (w : List ℕ) (hw : PosWord w) {M : ℕ} (hM : w.sum = M) :
    ∃ a : Nat.Partition M → ℂ, ∀ w' : List ℕ,
      gramWord c h w' w = ∑ Y, a Y * gramWord c h w' Y.word := by
  subst hM
  obtain ⟨a, ha⟩ := Verma.neg_mem_level (c := c) (h := h) w.length w hw le_rfl
  refine ⟨a, fun w' => ?_⟩
  rw [← (Verma.isShapovalov_shap (c := c) (h := h)).gramWord w' w hw, ← ha,
    Verma.pbwCoord_apply, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, (Verma.isShapovalov_shap (c := c) (h := h)).gramWord _ _ (posWord_word Y),
    smul_eq_mul]

/-- `L_{-w}P` is a combination of the `L_{-Y}P`, `Y` a partition of `|w|`, for a highest-weight
vector `P`. -/
theorem wordOp_straighten {P : V} {h : ℂ} (hP : R.IsHW P h) (w : List ℕ) (hw : PosWord w)
    {M : ℕ} (hM : w.sum = M) :
    ∃ a : Nat.Partition M → ℂ, R.wordOp w P = ∑ Y, a Y • R.wordOp Y.word P := by
  obtain ⟨a, ha⟩ := gramWord_straighten (R.c : ℂ) h w hw hM
  refine ⟨a, ?_⟩
  rw [← sub_eq_zero]
  apply R.form_def
  have key : ∀ w' : List ℕ,
      R.wordOp w' P ∈ R.orthTo (R.wordOp w P - ∑ Y, a Y • R.wordOp Y.word P) := by
    intro w'
    show R.form (R.wordOp w' P) (R.wordOp w P - ∑ Y, a Y • R.wordOp Y.word P) = 0
    rw [form_sub_right, form_sum_right, form_wordOp_wordOp hP hP.1 w' w hw, ha w', Finset.sum_mul,
      sub_eq_zero]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [R.form_smul_right, form_wordOp_wordOp hP hP.1 w' Y.word (posWord_word Y)]
    ring
  exact Submodule.sub_mem _ (key w)
    (Submodule.sum_mem _ fun Y _ => Submodule.smul_mem _ _ (key Y.word))

theorem prim_finite (R : UVir V) (n : ℕ) : Module.Finite ℂ (R.prim n) := by
  haveI := R.lev_fin n
  exact Submodule.finiteDimensional_of_le (inf_le_left : R.prim n ≤ R.lev n)

instance (R : UVir V) (n : ℕ) : Module.Finite ℂ (R.prim n) := R.prim_finite n

variable (R)

/-- The vectors `L_{-Y}P_a` of level `N`: `P_a` in a basis of the primaries of level `n ≤ N`,
`Y` a partition of `N - n`. -/
noncomputable def descFam (N : ℕ) :
    (Σ n : Fin (N + 1), Fin (Module.finrank ℂ (R.prim n)) × Nat.Partition (N - n)) → V :=
  fun x => R.wordOp x.2.2.word ((Module.finBasis ℂ (R.prim x.1) x.2.1 : R.prim x.1) : V)

theorem descFam_mk (N : ℕ) (n : Fin (N + 1)) (a : Fin (Module.finrank ℂ (R.prim n)))
    (Y : Nat.Partition (N - n)) :
    R.descFam N ⟨n, a, Y⟩ =
      R.wordOp Y.word ((Module.finBasis ℂ (R.prim n) a : R.prim n) : V) := rfl

theorem descFam_mem (N : ℕ)
    (x : Σ n : Fin (N + 1), Fin (Module.finrank ℂ (R.prim n)) × Nat.Partition (N - n)) :
    R.descFam N x ∈ R.lev N := by
  obtain ⟨n, a, Y⟩ := x
  rw [descFam_mk]
  refine R.wordOp_mem_lev (R.mem_prim.mp (Module.finBasis ℂ (R.prim n) a).2).1 _ _ ?_
  rw [word_sum']
  have := n.2
  omega

variable {R}

set_option maxHeartbeats 800000 in
theorem descFam_linearIndependent
    (hdet : ∀ n M : ℕ, (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) M).det ≠ 0) (N : ℕ) :
    LinearIndependent ℂ (R.descFam N) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rintro ⟨n', a', Z'⟩
  have hpair : ∀ (b' : Fin (Module.finrank ℂ (R.prim n'))) (Z : Nat.Partition (N - n')),
      ∑ a, ∑ Y, g ⟨n', a, Y⟩ *
        (gramWord (R.c : ℂ) ((R.h0 : ℂ) + ((n' : ℕ) : ℂ)) Z.word Y.word *
          R.form ((Module.finBasis ℂ (R.prim n') b' : R.prim n') : V)
            ((Module.finBasis ℂ (R.prim n') a : R.prim n') : V)) = 0 := by
    intro b' Z
    have h1 := congrArg
      (R.form (R.wordOp Z.word ((Module.finBasis ℂ (R.prim n') b' : R.prim n') : V))) hg
    rw [form_zero_right, form_sum_right, Fintype.sum_sigma,
      Finset.sum_eq_single_of_mem n' (Finset.mem_univ _)] at h1
    · rw [Fintype.sum_prod_type] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun Y _ => ?_
      rw [R.form_smul_right, descFam_mk,
        form_wordOp_wordOp (R.prim_isHW (Module.finBasis ℂ (R.prim n') a).2)
          (R.prim_isHW (Module.finBasis ℂ (R.prim n') b').2).1 _ _ (posWord_word Y)]
    · intro n _ hne
      rw [Fintype.sum_prod_type]
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun Y _ => ?_
      rw [R.form_smul_right, descFam_mk,
        form_wordOp_wordOp (R.prim_isHW (Module.finBasis ℂ (R.prim n) a).2)
          (R.prim_isHW (Module.finBasis ℂ (R.prim n') b').2).1 _ _ (posWord_word Y),
        R.orth n' n _ _ (fun h => hne (Fin.ext h).symm)
          (R.mem_prim.mp (Module.finBasis ℂ (R.prim n') b').2).1
          (R.mem_prim.mp (Module.finBasis ℂ (R.prim n) a).2).1, mul_zero, mul_zero]
  -- invert the Gram matrix of the basis of the primaries
  have he : LinearIndependent ℂ
      (fun a => ((Module.finBasis ℂ (R.prim n') a : R.prim n') : V)) :=
    (Module.finBasis ℂ (R.prim n')).linearIndependent.map' (R.prim n').subtype
      (Submodule.ker_subtype _)
  have hG := R.gramF_det_ne_zero _ he
  have hu : ∀ (Z : Nat.Partition (N - n')) (a : Fin (Module.finrank ℂ (R.prim n'))),
      ∑ Y, g ⟨n', a, Y⟩ * gramWord (R.c : ℂ) ((R.h0 : ℂ) + ((n' : ℕ) : ℂ)) Z.word Y.word = 0 := by
    intro Z
    have h2 : (Matrix.of fun i j =>
        R.form ((Module.finBasis ℂ (R.prim n') i : R.prim n') : V)
          ((Module.finBasis ℂ (R.prim n') j : R.prim n') : V)).mulVec
        (fun a => ∑ Y, g ⟨n', a, Y⟩ *
          gramWord (R.c : ℂ) ((R.h0 : ℂ) + ((n' : ℕ) : ℂ)) Z.word Y.word) = 0 := by
      funext b'
      rw [Pi.zero_apply, ← hpair b' Z]
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun Y _ => by ring
    intro a
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hG h2) a
  have h3 : (gram (R.c : ℂ) ((R.h0 : ℂ) + ((n' : ℕ) : ℂ)) (N - n')).mulVec
      (fun Y => g ⟨n', a', Y⟩) = 0 := by
    funext Z
    rw [Pi.zero_apply, ← hu Z a']
    simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply]
    exact Finset.sum_congr rfl fun Y _ => by ring
  exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero (hdet n' _) h3) Z'

theorem lev_le_span_descFam (N : ℕ) :
    R.lev N ≤ Submodule.span ℂ (Set.range (R.descFam N)) := by
  refine (R.lev_le_sup N).trans (iSup₂_le fun n hn => Submodule.span_le.mpr ?_)
  rintro v ⟨P, hP, w, hw, hN, rfl⟩
  have hn' : n < N + 1 := Finset.mem_range.1 hn
  obtain ⟨a, ha⟩ := wordOp_straighten (R.prim_isHW hP) w hw (M := N - n) (by omega)
  have hPr : P = ∑ i, (Module.finBasis ℂ (R.prim n)).repr ⟨P, hP⟩ i •
      ((Module.finBasis ℂ (R.prim n) i : R.prim n) : V) := by
    have h2 := congrArg (R.prim n).subtype ((Module.finBasis ℂ (R.prim n)).sum_repr ⟨P, hP⟩)
    rw [map_sum] at h2
    simpa using h2.symm
  rw [SetLike.mem_coe, ha]
  refine Submodule.sum_mem _ fun Y _ => Submodule.smul_mem _ _ ?_
  rw [hPr, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨n, hn'⟩, i, Y⟩, rfl⟩)

/-- `dim V_N = ∑_{n ≤ N} dim 𝒫_n · p(N-n)` (the comparison of graded characters,
sphere/paper.tex l.1056–1060). -/
theorem finrank_lev (hdet : ∀ n M : ℕ, (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) M).det ≠ 0)
    (N : ℕ) :
    Module.finrank ℂ (R.lev N) = ∑ n ∈ Finset.range (N + 1),
      Module.finrank ℂ (R.prim n) * Fintype.card (Nat.Partition (N - n)) := by
  have hli := descFam_linearIndependent hdet N
  have hspan : Submodule.span ℂ (Set.range (R.descFam N)) = R.lev N :=
    le_antisymm (Submodule.span_le.mpr (by
      rintro _ ⟨x, rfl⟩
      exact R.descFam_mem N x)) (lev_le_span_descFam N)
  rw [← hspan, finrank_span_eq_card hli, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact (Finset.sum_range fun n =>
    Module.finrank ℂ (R.prim n) * Fintype.card (Nat.Partition (N - n))).symm

/-- If `dim V_N = ∑_{n ≤ N} p(n) p(N-n)` for all `N`, then `dim 𝒫_n = p(n)`. -/
theorem finrank_prim (hdet : ∀ n M : ℕ, (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) M).det ≠ 0)
    (hlev : ∀ N : ℕ, Module.finrank ℂ (R.lev N) = ∑ n ∈ Finset.range (N + 1),
      Fintype.card (Nat.Partition n) * Fintype.card (Nat.Partition (N - n))) (N : ℕ) :
    Module.finrank ℂ (R.prim N) = Fintype.card (Nat.Partition N) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have h1 := finrank_lev hdet N
    have h3 : ∑ n ∈ Finset.range N,
        Module.finrank ℂ (R.prim n) * Fintype.card (Nat.Partition (N - n)) =
        ∑ n ∈ Finset.range N,
          Fintype.card (Nat.Partition n) * Fintype.card (Nat.Partition (N - n)) :=
      Finset.sum_congr rfl fun n hn => by rw [ih n (Finset.mem_range.1 hn)]
    rw [hlev N, Finset.sum_range_succ, Finset.sum_range_succ, h3] at h1
    have h2 := Nat.add_left_cancel h1
    have hpos : 0 < Fintype.card (Nat.Partition (N - N)) := by
      rw [Nat.sub_self]
      exact Fintype.card_pos_iff.mpr ⟨{ parts := 0, parts_pos := by simp, parts_sum := by simp }⟩
    exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

end UVir

end Virasoro.Sphere
