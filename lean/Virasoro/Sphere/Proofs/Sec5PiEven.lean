import Virasoro.Sphere.Proofs.Sec5PiOdd
import Virasoro.Sphere.Proofs.Sec2Block
import Virasoro.Proofs.SingularDegree
import Virasoro.Proofs.SingularPull

/-!
# Sphere paper Lemma 5.2 (ii): the singular three-point polynomials for even `k`

`sphere/paper.tex` l.1533–1538.  For even `k`, `h_{R^±_k,S^±_k}(b⋆) = λ + rs` and
`R^±_k S^±_k = ℓ^±_k - rs`; the image of `χ_{R^±_k,S^±_k}(b⋆)` under the homomorphism
`M(c⋆,λ+rs) → M(c⋆,λ)`, `v ↦ χ_{r,s}(b⋆)`, is `w^±_k`, and Lemma 4.2 gives
`π^±_k = P_{r,s} P_{R^±_k,S^±_k}`.  The `L_{-1}`-coefficient of a vector of level `N` is the
coefficient of `Δ_b^N` of its three-point scalar, so the image is normalized.
-/

namespace Virasoro.Sphere

open Verma Polynomial

/-- `γ_w(h;a,Δ_b)` as a polynomial in `Δ_b` has degree at most the length of `w`, with top
coefficient the product of the entries. -/
theorem gammaY_poly_deg (h a : ℂ) (w : List ℕ) :
    (gammaY (C h) (C a) (X : ℂ[X]) w).natDegree ≤ w.length ∧
      (gammaY (C h) (C a) (X : ℂ[X]) w).coeff w.length = (w.map fun y : ℕ => (y : ℂ)).prod := by
  induction w with
  | nil => simp [gammaY]
  | cons y w ih =>
    have e : (C h + ((w.sum : ℕ) : ℂ[X]) + (y : ℂ[X]) * X - C a) =
        C (y : ℂ) * X + C (h + (w.sum : ℕ) - a) := by
      simp only [map_add, map_sub, map_natCast]
      ring
    have h1 : (C (y : ℂ) * X + C (h + (w.sum : ℕ) - a)).natDegree ≤ 1 := natDegree_linear_le
    have h2 : (C (y : ℂ) * X + C (h + (w.sum : ℕ) - a)).coeff 1 = (y : ℂ) := by simp
    simp only [gammaY, e, List.length_cons, List.map_cons, List.prod_cons]
    refine ⟨?_, ?_⟩
    · rw [add_comm w.length 1]
      exact natDegree_mul_le_of_le h1 ih.1
    · rw [add_comm w.length 1, coeff_mul_add_eq_of_natDegree_le h1 ih.1, h2, ih.2]

/-- The three-point scalar of a vector of level `N`, as a polynomial in `Δ_b`, has degree at
most `N` and its coefficient of `Δ_b^N` is the `L_{-1}^N`-coefficient of the vector. -/
theorem scalar_poly_top (h a : ℂ) {N : ℕ} (q : Nat.Partition N → ℂ) :
    (∑ Y : Nat.Partition N, C (q Y) * gammaY (C h) (C a) (X : ℂ[X]) Y.word).natDegree ≤ N ∧
      (∑ Y : Nat.Partition N, C (q Y) * gammaY (C h) (C a) (X : ℂ[X]) Y.word).coeff N =
        q (onesPartition N) := by
  have hlen : ∀ Y : Nat.Partition N, Y.word.length ≤ N := by
    intro Y
    by_cases hY : Y = onesPartition N
    · rw [hY, word_onesPartition, List.length_replicate]
    · exact (word_length_lt Y hY).le
  refine ⟨natDegree_sum_le_of_forall_le _ _ fun Y _ =>
    (natDegree_C_mul_le _ _).trans ((gammaY_poly_deg h a Y.word).1.trans (hlen Y)), ?_⟩
  rw [finsetSum_coeff, Finset.sum_eq_single (onesPartition N)]
  · have h1 := (gammaY_poly_deg h a (onesPartition N).word).2
    rw [word_onesPartition] at h1
    simp only [List.length_replicate, List.map_replicate, List.prod_replicate, Nat.cast_one,
      one_pow] at h1
    rw [coeff_C_mul, word_onesPartition, h1, mul_one]
  · intro Y _ hY
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (gammaY_poly_deg h a Y.word).1 (word_length_lt Y hY)), mul_zero]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-- The push-forward of a normalized singular vector of `M(c,h+ℓ)` along the homomorphism
defined by a normalized singular vector of level `ℓ` of `M(c,h)`: three-point scalars
multiply. -/
theorem piScalar_push (hU : Cited_SingularUnique) {c h : ℂ} {ℓ m : ℕ}
    (y0 : Nat.Partition ℓ → ℂ) (hy01 : y0 (onesPartition ℓ) = 1)
    (hy0 : IsSingular (pbwCoord (c := c) (h := h) ℓ y0) ℓ) {P0 P1 : ℂ → ℂ → ℂ}
    (hP0 : ∀ Δa Δb : ℂ, ∑ Y, y0 Y * gammaY h Δa Δb Y.word = P0 Δa Δb)
    {h' : ℂ} (hh : h' = h + (ℓ : ℂ)) (y1 : Nat.Partition m → ℂ)
    (hy11 : y1 (onesPartition m) = 1)
    (hy1 : IsSingular (pbwCoord (c := c) (h := h') m y1) m)
    (hP1 : ∀ Δa Δb : ℂ, ∑ Y, y1 Y * gammaY h' Δa Δb Y.word = P1 Δa Δb)
    {n : ℕ} (hn : ℓ + m = n) (x : Nat.Partition n → ℂ) (hx1 : x (onesPartition n) = 1)
    (hx : IsSingular (pbwCoord (c := c) (h := h) n x) n) (Δa Δb : ℂ) :
    piScalar h x Δa Δb = P0 Δa Δb * P1 Δa Δb := by
  subst hh hn
  obtain ⟨j, hjhw, hjL, hjneg⟩ := exists_singularHom hy0.2.1 hy0.2.2
  have hw : j (pbwCoord (c := c) (h := h + (ℓ : ℂ)) m y1) =
      ∑ Z : Nat.Partition m, y1 Z • (VirEnv.negOp c Z.word • pbwCoord (c := c) (h := h) ℓ y0) := by
    rw [pbwCoord_apply, map_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [map_smul, hjneg]
  have hmem : j (pbwCoord (c := c) (h := h + (ℓ : ℂ)) m y1) ∈ level (c := c) (h := h) (ℓ + m) := by
    rw [hw]
    refine Submodule.sum_mem _ fun Z _ => Submodule.smul_mem _ _ ?_
    have := negOp_smul_mem_level (c := c) (h := h) (ℓ := ℓ) (v := pbwCoord ℓ y0) ⟨y0, rfl⟩ Z.word
    rwa [word_sum'] at this
  obtain ⟨z, hz⟩ := hmem
  have hstar : ∀ Δa Δb : ℂ, ∑ Y, z Y * gammaY h Δa Δb Y.word = P0 Δa Δb * P1 Δa Δb := by
    intro Δa Δb
    obtain ⟨⟨φ, hφ, -⟩, hγ⟩ := def_sphere_block ℂ c h Δa Δb
    have h1 : φ (pbwCoord (c := c) (h := h) (ℓ + m) z) = ∑ Y, z Y * gammaY h Δa Δb Y.word := by
      rw [pbwCoord_apply, map_sum]
      refine Finset.sum_congr rfl fun Y _ => ?_
      rw [map_smul, hγ φ hφ, smul_eq_mul]
    have h2 : φ (pbwCoord (c := c) (h := h) ℓ y0) = P0 Δa Δb := by
      rw [← hP0, pbwCoord_apply, map_sum]
      refine Finset.sum_congr rfl fun Y _ => ?_
      rw [map_smul, hγ φ hφ, smul_eq_mul]
    rw [← h1, hz, hw, map_sum, ← hP1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [map_smul, lem_3pt_factor c h Δa Δb φ hφ ℓ _ hy0.2.1 m Z, h2, smul_eq_mul]
    ring
  have hpoly : (∑ Y : Nat.Partition (ℓ + m), C (z Y) * gammaY (C h) (C 0) (X : ℂ[X]) Y.word) =
      (∑ Y : Nat.Partition ℓ, C (y0 Y) * gammaY (C h) (C 0) (X : ℂ[X]) Y.word) *
        ∑ Y : Nat.Partition m, C (y1 Y) * gammaY (C (h + (ℓ : ℂ))) (C 0) (X : ℂ[X]) Y.word := by
    refine Polynomial.funext fun t => ?_
    simp only [eval_finsetSum, eval_mul, eval_C, eval_gammaY_b]
    rw [hstar, hP0, hP1]
  have hz1 : z (onesPartition (ℓ + m)) = 1 := by
    rw [← (scalar_poly_top h 0 z).2, hpoly,
      coeff_mul_add_eq_of_natDegree_le (scalar_poly_top h 0 y0).1 (scalar_poly_top (h + (ℓ : ℂ)) 0 y1).1,
      (scalar_poly_top h 0 y0).2, (scalar_poly_top (h + (ℓ : ℂ)) 0 y1).2, hy01, hy11, mul_one]
  have hzs : IsSingular (pbwCoord (c := c) (h := h) (ℓ + m) z) (ℓ + m) := by
    refine ⟨fun h0 => ?_, ?_, fun k hk => ?_⟩
    · have := congrFun (pbwCoord_injective (ℓ + m) (h0.trans (map_zero _).symm))
        (onesPartition (ℓ + m))
      rw [hz1] at this
      exact one_ne_zero this
    · rw [hz, ← hjL, hy1.2.1, map_smul]
      congr 1
      push_cast
      ring
    · rw [hz, ← hjL, hy1.2.2 k hk, map_zero]
  rw [piScalar_eq_of_singular hU rfl rfl z hz1 hzs x hx1 hx, hstar]

/-- Lemma 5.2 (ii). -/
theorem pi_even (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    {k : ℕ} (ε : Bool) (hk1 : 1 ≤ k) (hk : k % 2 = 0)
    (x : Nat.Partition (ellOrb p p' r s ε k) → ℂ) (hx1 : x (onesPartition _) = 1)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellOrb p p' r s ε k) x)
      (ellOrb p p' r s ε k)) (Δa Δb : ℂ) :
    piScalar (kacH r s b) x Δa Δb =
      fusP r s b Δa Δb *
        (if ε then fusP (r + k / 2 * p) (k / 2 * p' - s) b Δa Δb
          else fusP (k / 2 * p - r) (k / 2 * p' + s) b Δa Δb) := by
  have hb0 := minimal_b_ne_zero hset
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hk0 : k ≠ 0 := by omega
  have hj : 1 ≤ k / 2 := by omega
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h1 : r < k / 2 * p := by
    have : p ≤ k / 2 * p := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h2 : s < k / 2 * p' := by
    have : p' ≤ k / 2 * p' := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨y0, hy01, hy0s, hy0v⟩ := exists_chi hH hF hb0 r s hr hs
  cases ε with
  | true =>
    obtain ⟨y1, hy11, hy1s, hy1v⟩ := exists_chi hH hF hb0 (r + k / 2 * p) (k / 2 * p' - s)
      (by omega) (by omega)
    have hh : kacH ((r + k / 2 * p : ℕ) : ℤ) ((k / 2 * p' - s : ℕ) : ℤ) b =
        kacH r s b + ((r * s : ℕ) : ℂ) := by
      rw [kacH_minimal hset', kacH_minimal hset']
      push_cast [Nat.cast_sub h2.le]
      field_simp
      ring
    have hn : r * s + (r + k / 2 * p) * (k / 2 * p' - s) = ellOrb p p' r s true k := by
      have e : ((r * s + (r + k / 2 * p) * (k / 2 * p' - s) : ℕ) : ℤ) =
          ((k / 2 : ℕ) : ℤ) * (((k / 2 : ℕ) : ℤ) * p * p' + ((p' : ℤ) * r - (p : ℤ) * s)) := by
        push_cast [Nat.cast_sub h2.le]
        ring
      simp only [ellOrb, ellPlus, if_neg hk0, if_pos hk, if_true]
      rw [← e, Int.toNat_natCast]
    rw [if_pos rfl]
    exact piScalar_push hU y0 hy01 hy0s hy0v hh y1 hy11 hy1s hy1v hn x hx1 hx Δa Δb
  | false =>
    obtain ⟨y1, hy11, hy1s, hy1v⟩ := exists_chi hH hF hb0 (k / 2 * p - r) (k / 2 * p' + s)
      (by omega) (by omega)
    have hh : kacH ((k / 2 * p - r : ℕ) : ℤ) ((k / 2 * p' + s : ℕ) : ℤ) b =
        kacH r s b + ((r * s : ℕ) : ℂ) := by
      rw [kacH_minimal hset', kacH_minimal hset']
      push_cast [Nat.cast_sub h1.le]
      field_simp
      ring
    have hn : r * s + (k / 2 * p - r) * (k / 2 * p' + s) = ellOrb p p' r s false k := by
      have e : ((r * s + (k / 2 * p - r) * (k / 2 * p' + s) : ℕ) : ℤ) =
          ((k / 2 : ℕ) : ℤ) * (((k / 2 : ℕ) : ℤ) * p * p' - ((p' : ℤ) * r - (p : ℤ) * s)) := by
        push_cast [Nat.cast_sub h1.le]
        ring
      simp only [ellOrb, ellMinus, if_neg hk0, if_pos hk]
      rw [← e, Int.toNat_natCast]
      simp
    rw [if_neg (by simp)]
    exact piScalar_push hU y0 hy01 hy0s hy0v hh y1 hy11 hy1s hy1v hn x hx1 hx Δa Δb

end Virasoro.Sphere
