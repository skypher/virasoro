import Virasoro.Sphere.Proofs.Sec3UVirDecomp

/-!
# The norm of a Ward family in a unitary representation (sphere paper, Lemma 3.7, Step 1)

sphere/paper.tex l.1060–1071: because the Ward equations determine the descendant projections
of `F` inside the module of each primary from its primary component, orthogonal projection
gives `‖F_N‖² = ∑_n c_n ℬ_{N-n}`, with `c_n` the squared norm of the projection of `F_n` to the
primary space of level `n`, equal to `∑_{a,b} conj⟨P_a,F⟩ (G⁻¹)_{a,b} ⟨P_b,F⟩` in any basis.
-/

namespace Virasoro.Sphere

namespace UVir

open Verma

variable {V : Type*} [AddCommGroup V] [Module ℂ V] {R : UVir V}

theorem conj_gram_real (c h : ℝ) (n M : ℕ) :
    (gram (c : ℂ) ((h : ℂ) + (n : ℂ)) M).map (starRingEnd ℂ) = gram (c : ℂ) ((h : ℂ) + (n : ℂ)) M := by
  rw [← gram_map (starRingEnd ℂ)]
  simp [Complex.conj_ofReal]

set_option maxHeartbeats 800000 in
/-- `‖F_N‖² = ∑_{n ≤ N} ‖p_n‖² ∑_{Y,Z} γ_Y (G_{N-n}(c, h₀+n)⁻¹)_{Y,Z} γ_Z`, with `p_n` the
orthogonal projection of `F_n` to the primary space of level `n`. -/
theorem norm_decomp
    (hdet : ∀ n M : ℕ, (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) M).det ≠ 0) {Δa Δb : ℝ}
    {F : ℕ → V} (hF : R.IsWard Δa Δb F) (p : ℕ → V) (hp : ∀ n, p n ∈ R.prim n)
    (hpo : ∀ n, ∀ y ∈ R.prim n, R.form y (F n - p n) = 0) (N : ℕ) :
    R.form (F N) (F N) = ∑ n ∈ Finset.range (N + 1), R.form (p n) (p n) *
      ∑ Y : Nat.Partition (N - n), ∑ Z : Nat.Partition (N - n),
        gammaY ((R.h0 : ℂ) + (n : ℂ)) (Δa : ℂ) (Δb : ℂ) Y.word *
          (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) (N - n))⁻¹ Y Z *
          gammaY ((R.h0 : ℂ) + (n : ℂ)) (Δa : ℂ) (Δb : ℂ) Z.word := by
  classical
  let γ : ∀ n : ℕ, Nat.Partition (N - n) → ℂ :=
    fun n Y => gammaY ((R.h0 : ℂ) + (n : ℂ)) (Δa : ℂ) (Δb : ℂ) Y.word
  let t : ∀ n : ℕ, Nat.Partition (N - n) → ℂ :=
    fun n => (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) (N - n))⁻¹.mulVec (γ n)
  let Ψ : ℕ → V := fun n => ∑ Y : Nat.Partition (N - n), t n Y • R.wordOp Y.word (p n)
  have ht : ∀ n : ℕ, (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) (N - n)).mulVec (t n) = γ n := by
    intro n
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet n _)),
      Matrix.one_mulVec]
  have hγ : ∀ n Y, (starRingEnd ℂ) (γ n Y) = γ n Y := by
    intro n Y
    show (starRingEnd ℂ) (gammaY _ _ _ _) = gammaY _ _ _ _
    rw [map_gammaY]
    simp [Complex.conj_ofReal]
  have hreal : ∀ n Y, (starRingEnd ℂ) (t n Y) = t n Y := by
    intro n Y
    have h4 : (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) (N - n)).mulVec
        ((starRingEnd ℂ) ∘ t n) = γ n := by
      funext Z
      have h5 := RingHom.map_mulVec (starRingEnd ℂ)
        (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) (N - n)) (t n) Z
      rw [conj_gram_real] at h5
      rw [← h5, ht, hγ]
    have h7 : (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) (N - n)).mulVec
        (((starRingEnd ℂ) ∘ t n) - t n) = 0 := by
      rw [Matrix.mulVec_sub, h4, ht, sub_self]
    have h8 := Matrix.eq_zero_of_mulVec_eq_zero (hdet n _) h7
    have h9 := congrFun h8 Y
    simpa [sub_eq_zero] using h9
  have hΨlev : ∀ n ∈ Finset.range (N + 1), Ψ n ∈ R.lev N := by
    intro n hn
    have hn' := Finset.mem_range.1 hn
    refine Submodule.sum_mem _ fun Y _ => Submodule.smul_mem _ _ ?_
    exact R.wordOp_mem_lev (R.mem_prim.mp (hp n)).1 _ _ (by rw [word_sum']; omega)
  -- the pairing of a generator with `F_N - ∑ Ψ_n`
  have key : ∀ n' : ℕ, n' ∈ Finset.range (N + 1) → ∀ P ∈ R.prim n', ∀ w : List ℕ, PosWord w →
      n' + w.sum = N → R.form (R.wordOp w P) (F N - ∑ n ∈ Finset.range (N + 1), Ψ n) = 0 := by
    intro n' hn' P hP w hw hN
    have hPk := (R.prim_isHW hP).1
    rw [form_sub_right, ward_pair hF hP w hw N hN, form_sum_right,
      Finset.sum_eq_single_of_mem n' hn']
    · have h1 : R.form (R.wordOp w P) (Ψ n') =
          (∑ Y : Nat.Partition (N - n'), t n' Y *
            gramWord (R.c : ℂ) ((R.h0 : ℂ) + (n' : ℂ)) w Y.word) * R.form P (p n') := by
        show R.form _ (∑ Y : Nat.Partition (N - n'), t n' Y • R.wordOp Y.word (p n')) = _
        rw [form_sum_right, Finset.sum_mul]
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [R.form_smul_right, form_wordOp_wordOp (R.prim_isHW (hp n')) hPk _ _ (posWord_word Y)]
        ring
      rw [h1, gamma_gram (R.c : ℂ) ((R.h0 : ℂ) + (n' : ℂ)) (Δa : ℂ) (Δb : ℂ) w hw (by omega)
        (t n') (ht n')]
      have h2 := hpo n' P hP
      rw [form_sub_right, sub_eq_zero] at h2
      rw [h2, sub_self]
    · intro n _ hne
      show R.form _ (∑ Y : Nat.Partition (N - n), t n Y • R.wordOp Y.word (p n)) = 0
      rw [form_sum_right]
      refine Finset.sum_eq_zero fun Y _ => ?_
      rw [R.form_smul_right, form_wordOp_wordOp (R.prim_isHW (hp n)) hPk _ _ (posWord_word Y),
        R.orth n' n P (p n) (Ne.symm hne) (R.mem_prim.mp hP).1 (R.mem_prim.mp (hp n)).1]
      ring
  -- `F_N = ∑ Ψ_n`
  have hD : F N - ∑ n ∈ Finset.range (N + 1), Ψ n = 0 := by
    apply R.form_def
    have hmem : F N - ∑ n ∈ Finset.range (N + 1), Ψ n ∈ R.lev N :=
      Submodule.sub_mem _ (hF.mem N) (Submodule.sum_mem _ hΨlev)
    have hle : (⨆ n ∈ Finset.range (N + 1), R.desc n N) ≤
        R.orthTo (F N - ∑ n ∈ Finset.range (N + 1), Ψ n) := by
      refine iSup₂_le fun n hn => Submodule.span_le.mpr ?_
      rintro v ⟨P, hP, w, hw, hN, rfl⟩
      exact key n hn P hP w hw hN
    exact hle (R.lev_le_sup N hmem)
  have hFN : F N = ∑ n ∈ Finset.range (N + 1), Ψ n := sub_eq_zero.mp hD
  calc R.form (F N) (F N) = R.form (∑ n ∈ Finset.range (N + 1), Ψ n) (F N) := by rw [← hFN]
    _ = ∑ n ∈ Finset.range (N + 1), R.form (Ψ n) (F N) := form_sum_left _ _ _ _
    _ = _ := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn' := Finset.mem_range.1 hn
      have h1 : R.form (Ψ n) (F N) =
          ∑ Y : Nat.Partition (N - n), t n Y * (γ n Y * R.form (p n) (p n)) := by
        show R.form (∑ Y : Nat.Partition (N - n), t n Y • R.wordOp Y.word (p n)) (F N) = _
        rw [form_sum_left]
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [form_smul_left, hreal, ward_pair hF (hp n) Y.word (posWord_word Y) N
          (by rw [word_sum']; omega)]
        have h2 := hpo n (p n) (hp n)
        rw [form_sub_right, sub_eq_zero] at h2
        rw [h2]
      rw [h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Y _ => ?_
      show (∑ Z, (gram (R.c : ℂ) ((R.h0 : ℂ) + (n : ℂ)) (N - n))⁻¹ Y Z * γ n Z) *
        (γ n Y * R.form (p n) (p n)) = _
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Z _ => ?_
      show _ = R.form (p n) (p n) * (γ n Y * _ * γ n Z)
      ring

/-- The coefficient `∑_{a,b} conj⟨P_a,F⟩ (G⁻¹)_{a,b} ⟨P_b,F⟩` in a basis `(P_a)` of a subspace
`W` is the squared norm of the orthogonal projection of `F` to `W`; the Gram matrix `G` is
invertible. -/
theorem coefG_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (W : Submodule ℂ V)
    (P : Module.Basis ι ℂ W) (F p : V) (hp : p ∈ W) (hpo : ∀ y ∈ W, R.form y (F - p) = 0) :
    (Matrix.of fun a b => R.form (P a : V) (P b : V)).det ≠ 0 ∧
    ∑ a, ∑ b, (starRingEnd ℂ) (R.form (P a : V) F) *
      (Matrix.of fun a b => R.form (P a : V) (P b : V))⁻¹ a b * R.form (P b : V) F =
      R.form p p := by
  have he : LinearIndependent ℂ (fun a => (P a : V)) :=
    P.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hG := R.gramF_det_ne_zero _ he
  refine ⟨hG, ?_⟩
  have hf : ∀ a, R.form (P a : V) F = R.form (P a : V) p := by
    intro a
    have h := hpo _ (P a).2
    rwa [form_sub_right, sub_eq_zero] at h
  have hpr : p = ∑ b, P.repr ⟨p, hp⟩ b • (P b : V) := by
    have h2 := congrArg W.subtype (P.sum_repr ⟨p, hp⟩)
    rw [map_sum] at h2
    simpa using h2.symm
  have hmul : (Matrix.of fun a b => R.form (P a : V) (P b : V)).mulVec
      (fun b => P.repr ⟨p, hp⟩ b) = fun a => R.form (P a : V) F := by
    funext a
    rw [hf a]
    conv_rhs => rw [hpr]
    rw [form_sum_right]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    exact Finset.sum_congr rfl fun b _ => by rw [R.form_smul_right, mul_comm]
  have hinv : (Matrix.of fun a b => R.form (P a : V) (P b : V))⁻¹.mulVec
      (fun a => R.form (P a : V) F) = fun b => P.repr ⟨p, hp⟩ b := by
    rw [← hmul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hG),
      Matrix.one_mulVec]
  calc ∑ a, ∑ b, (starRingEnd ℂ) (R.form (P a : V) F) *
        (Matrix.of fun a b => R.form (P a : V) (P b : V))⁻¹ a b * R.form (P b : V) F
      = ∑ a, (starRingEnd ℂ) (R.form (P a : V) F) * P.repr ⟨p, hp⟩ a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        have h1 := congrFun hinv a
        simp only [Matrix.mulVec, dotProduct] at h1
        rw [← h1, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a, R.form p (P.repr ⟨p, hp⟩ a • (P a : V)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [R.form_smul_right, hf a, ← R.form_conj, mul_comm]
    _ = R.form p p := by
        rw [← form_sum_right, ← hpr]

end UVir

end Virasoro.Sphere
