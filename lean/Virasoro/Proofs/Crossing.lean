import Virasoro.Proofs.PBWBasis
import Virasoro.Proofs.Singular
import Virasoro.Proofs.TorusDegree
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The first crossing form on a singular submodule (paper Lemma 5.10)

Let `χ = P|h₀⟩` be singular of level `ℓ ≥ 1` in `M(c,h₀)`, with `P` fixed, and let
`χ_X = P|X⟩` in the Verma module over `K[X]` with internal weight `X`.  Then
`d/dh ⟨L_{-Y} χ_X, L_{-w} χ_X⟩ |_{h₀} = β_χ ⟨h₀+ℓ| L_Y L_{-w} |h₀+ℓ⟩`.
-/

namespace Virasoro

open Polynomial

section General

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

theorem negOp_nil_smul (v : Verma R c h) : VirEnv.negOp c [] • v = v := by
  simp [VirEnv.negOp]

theorem negOp_cons_smul (y : ℕ) (w : List ℕ) (v : Verma R c h) :
    VirEnv.negOp c (y :: w) • v = L (-(y : ℤ)) (VirEnv.negOp c w • v) := by
  have e : VirEnv.negOp c (y :: w) = VirEnv.L c (-(y : ℤ)) * VirEnv.negOp c w := by
    simp [VirEnv.negOp]
  rw [e, mul_smul]
  rfl

theorem neg_append (Y Z : List ℕ) :
    neg (c := c) (h := h) (Y ++ Z) = VirEnv.negOp c Y • neg Z := by
  induction Y with
  | nil => rw [List.nil_append, negOp_nil_smul]
  | cons y Y ih => rw [List.cons_append, neg_cons, ih, negOp_cons_smul]

/-- `L_0` on `L_{-w} v` for an `L_0`-eigenvector `v`. -/
theorem L_zero_negOp (w : List ℕ) {v : Verma R c h} {a : R} (hv : L 0 v = a • v) :
    L 0 (VirEnv.negOp c w • v) = (a + ((w.sum : ℕ) : R)) • (VirEnv.negOp c w • v) := by
  induction w with
  | nil => rw [negOp_nil_smul, hv, List.sum_nil, Nat.cast_zero, add_zero]
  | cons y w ih =>
    rw [negOp_cons_smul, L_L_ct, ih, map_smul, List.sum_cons, ct_symm, ct]
    have e : -(y : ℤ) + 0 = -(y : ℤ) := by ring
    rw [e]
    by_cases hy : -(y : ℤ) = 0
    · have hy0 : y = 0 := by omega
      subst hy0
      simp [centralTerm]
    · rw [if_neg (by omega), zero_smul, add_zero]
      push_cast
      module

end Verma

section BC

variable {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S) {c' h' : S} (hc : f c = c')
  (hh : f h = h')

theorem Verma.baseChange_negOp_smul (w : List ℕ) (v : Verma R c h) :
    Verma.baseChange f hc hh (VirEnv.negOp c w • v)
      = VirEnv.negOp c' w • Verma.baseChange f hc hh v := by
  induction w with
  | nil => rw [Verma.negOp_nil_smul, Verma.negOp_nil_smul]
  | cons y w ih =>
    rw [Verma.negOp_cons_smul, Verma.baseChange_L, ih, Verma.negOp_cons_smul]

end BC

end General

variable {K : Type*} [Field K] [CharZero K]

namespace Verma

/-- A singular vector of positive level lies in the radical of the Shapovalov form, and so does
every vector `L_{-Y} χ`. -/
theorem shap_singular (c h : K) {χ : Verma K c h} {ℓ : ℕ} (hχ : IsSingular χ ℓ) (hℓ : 1 ≤ ℓ)
    (Y : List ℕ) : ∀ v : Verma K c h, shap c h (VirEnv.negOp c Y • χ) v = 0 := by
  have hB := isShapovalov_shap (c := c) (h := h)
  induction Y with
  | nil =>
    intro v
    rw [negOp_nil_smul]
    refine induction_neg (P := fun v => shap c h χ v = 0) ?_ ?_ ?_ v
    · intro w hpw
      cases w with
      | nil =>
        rw [neg_nil]
        have h1 := hB.2 0 χ hw
        rw [neg_zero, hχ.2.1, L_hw_zero, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
          smul_eq_mul] at h1
        have h2 : ((ℓ : ℕ) : K) * shap c h χ hw = 0 := by linear_combination h1
        rcases mul_eq_zero.1 h2 with h3 | h3
        · exact absurd h3 (Nat.cast_ne_zero.2 (by omega))
        · exact h3
      | cons y w =>
        rw [neg_cons]
        have hy : 0 < y := hpw y List.mem_cons_self
        have h1 := hB.2 (y : ℤ) χ (neg w)
        rw [← h1, hχ.2.2 (y : ℤ) (by exact_mod_cast hy), map_zero, LinearMap.zero_apply]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
    · intro r a ha
      rw [map_smul, ha, smul_zero]
  | cons y Y ih =>
    intro v
    rw [negOp_cons_smul, hB.2, neg_neg]
    exact ih _

end Verma

section Core

variable (c h₀ : K) (ℓ : ℕ) (p : Nat.Partition ℓ → K)

/-- The derivative at `h₀` of a polynomial. -/
noncomputable def dAt (F : K[X]) : K := (derivative F).eval h₀

omit [CharZero K] in
theorem dAt_mul (a F : K[X]) :
    dAt h₀ (a * F) = (derivative a).eval h₀ * F.eval h₀ + a.eval h₀ * dAt h₀ F := by
  rw [dAt, derivative_mul, eval_add, eval_mul, eval_mul, dAt]

omit [CharZero K] in
theorem dAt_X_sub_C_mul (F : K[X]) : dAt h₀ ((X - C h₀) * F) = F.eval h₀ := by
  rw [dAt_mul, derivative_X_sub_C, eval_one, one_mul, eval_sub, eval_X, eval_C, sub_self,
    zero_mul, add_zero]

omit [CharZero K] in
theorem dAt_add (F G : K[X]) : dAt h₀ (F + G) = dAt h₀ F + dAt h₀ G := by
  rw [dAt, derivative_add, eval_add, dAt, dAt]

omit [CharZero K] in
theorem dAt_list_sum (l : List K[X]) : dAt h₀ l.sum = (l.map (dAt h₀)).sum := by
  induction l with
  | nil => simp [dAt]
  | cons a l ih => rw [List.sum_cons, dAt_add, ih, List.map_cons, List.sum_cons]

/-- The crossing identity on words: with `χ_X = P|X⟩`,
`d/dh ⟨L_{-Y} χ_X, L_{-w} χ_X⟩ |_{h₀} = β_χ ⟨h₀+ℓ| L_Y L_{-w} |h₀+ℓ⟩`. -/
theorem crossing_words (hℓ : 1 ≤ ℓ)
    (hχ : Verma.IsSingular (Verma.pbwCoord (c := c) (h := h₀) ℓ p) ℓ) :
    ∀ Y : List ℕ, PosWord Y → ∀ w : List ℕ, PosWord w →
      dAt h₀ (Verma.shap (C c) (X : K[X])
          (VirEnv.negOp (C c) Y • Verma.pbwCoord ℓ fun Z => C (p Z))
          (VirEnv.negOp (C c) w • Verma.pbwCoord ℓ fun Z => C (p Z)))
        = dAt h₀ (Verma.shap (C c) (X : K[X]) (Verma.pbwCoord ℓ fun Z => C (p Z))
            (Verma.pbwCoord ℓ fun Z => C (p Z))) * gramWord c (h₀ + (ℓ : K)) Y w := by
  set χX : Verma K[X] (C c) X := Verma.pbwCoord ℓ fun Z => C (p Z) with hχX
  set χ : Verma K c h₀ := Verma.pbwCoord ℓ p with hχdef
  have hc : (evalRingHom h₀) (C c) = c := by simp
  have hh : (evalRingHom h₀) (X : K[X]) = h₀ := by simp
  set ev := Verma.baseChange (evalRingHom h₀) hc hh with hev
  have hBX := Verma.isShapovalov_shap (c := C c) (h := (X : K[X]))
  have hB := Verma.isShapovalov_shap (c := c) (h := h₀)
  have hevχ : ev χX = χ := by
    rw [hev, hχX, Verma.baseChange_pbwCoord]
    simp only [coe_evalRingHom, eval_C]
    rfl
  have hBev : ∀ u v, Verma.shap c h₀ (ev u) (ev v) = (Verma.shap (C c) X u v).eval h₀ :=
    fun u v => Verma.shap_baseChange (evalRingHom h₀) hc hh u v
  have hevneg : ∀ Y : List ℕ, ev (VirEnv.negOp (C c) Y • χX) = VirEnv.negOp c Y • χ := by
    intro Y
    rw [hev, Verma.baseChange_negOp_smul, ← hev, hevχ]
  have hradL : ∀ (Y : List ℕ) (u : Verma K[X] (C c) X),
      (Verma.shap (C c) X (VirEnv.negOp (C c) Y • χX) u).eval h₀ = 0 := by
    intro Y u
    rw [← hBev, hevneg]
    exact Verma.shap_singular c h₀ hχ hℓ Y _
  have hradR : ∀ (Y : List ℕ) (u : Verma K[X] (C c) X),
      (Verma.shap (C c) X u (VirEnv.negOp (C c) Y • χX)).eval h₀ = 0 := by
    intro Y u
    rw [hBX.symm]
    exact hradL Y u
  have hker : ∀ u : Verma K[X] (C c) X, ev u = 0 → ∃ ψ, u = (X - C h₀) • ψ := by
    intro u hu
    refine Verma.baseChange_eq_zero (evalRingHom h₀) hc hh (π := X - C h₀) ?_ u hu
    intro a ha
    have hroot : (X - C h₀) ∣ a := dvd_iff_isRoot.2 ha
    obtain ⟨b, hb⟩ := hroot
    exact ⟨b, hb⟩
  have hLk : ∀ k : ℤ, 0 < k → ∃ ψ, Verma.L k χX = (X - C h₀) • ψ := by
    intro k hk
    refine hker _ ?_
    rw [hev, Verma.baseChange_L, ← hev, hevχ]
    exact hχ.2.2 k hk
  obtain ⟨j, -, hj2, hj3⟩ := Verma.exists_singularHom hχ.2.1 hχ.2.2
  have hact : ∀ (y : ℕ) (w : List ℕ), actWord c (h₀ + (ℓ : K)) (y : ℤ) w
      = mapSt (evalRingHom h₀) (actWord (C c) (X + C (ℓ : K)) (y : ℤ) w) := by
    intro y w
    rw [← actWord_map]
    simp
  have hstar : ∀ (y : ℕ) (w : List ℕ), ∃ ρ : Verma K[X] (C c) X,
      Verma.L (y : ℤ) (VirEnv.negOp (C c) w • χX)
        = ((actWord (C c) (X + C (ℓ : K)) (y : ℤ) w).map fun t =>
            t.2 • (VirEnv.negOp (C c) t.1 • χX)).sum + (X - C h₀) • ρ := by
    intro y w
    have hz : ev (Verma.L (y : ℤ) (VirEnv.negOp (C c) w • χX)
        - ((actWord (C c) (X + C (ℓ : K)) (y : ℤ) w).map fun t =>
            t.2 • (VirEnv.negOp (C c) t.1 • χX)).sum) = 0 := by
      rw [map_sub, hev, Verma.baseChange_L, ← hev, hevneg, map_list_sum, List.map_map,
        ← hj3, ← hj2, Verma.L_neg_actWord, hact, St.toVerma, mapSt, List.map_map, map_list_sum,
        List.map_map, sub_eq_zero]
      congr 1
      refine List.map_congr_left fun t _ => ?_
      simp only [Function.comp_apply, map_smul, LinearMap.map_smulₛₗ, hj3, hevneg,
        coe_evalRingHom]
    obtain ⟨ρ, hρ⟩ := hker _ hz
    exact ⟨ρ, by rw [← hρ]; abel⟩
  intro Y
  induction Y with
  | nil =>
    intro _ w hw
    rw [Verma.negOp_nil_smul]
    cases w with
    | nil =>
      rw [Verma.negOp_nil_smul]
      have : gramWord c (h₀ + (ℓ : K)) [] [] = 1 := by simp [gramWord, vac]
      rw [this, mul_one]
    | cons m w =>
      have hm : 0 < m := hw m List.mem_cons_self
      obtain ⟨ψ, hψ⟩ := hLk (m : ℤ) (by exact_mod_cast hm)
      have e : Verma.shap (C c) X χX (VirEnv.negOp (C c) (m :: w) • χX)
          = (X - C h₀) * Verma.shap (C c) X ψ (VirEnv.negOp (C c) w • χX) := by
        have e0 : Verma.shap (C c) X ((X - C h₀) • ψ) = (X - C h₀) • Verma.shap (C c) X ψ :=
          (Verma.shap (C c) (X : K[X])).map_smul (X - C h₀) ψ
        rw [Verma.negOp_cons_smul, ← hBX.2, hψ, e0, LinearMap.smul_apply, smul_eq_mul]
      rw [e, dAt_X_sub_C_mul, hradR]
      have : gramWord c (h₀ + (ℓ : K)) [] (m :: w) = 0 := by simp [gramWord, vac]
      rw [this, mul_zero]
  | cons y Y ih =>
    intro hY w hw
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    obtain ⟨ρ, hρ⟩ := hstar y w
    have e : Verma.shap (C c) X (VirEnv.negOp (C c) (y :: Y) • χX)
          (VirEnv.negOp (C c) w • χX)
        = ((actWord (C c) (X + C (ℓ : K)) (y : ℤ) w).map fun t =>
            t.2 * Verma.shap (C c) X (VirEnv.negOp (C c) Y • χX)
              (VirEnv.negOp (C c) t.1 • χX)).sum
          + (X - C h₀) * Verma.shap (C c) X (VirEnv.negOp (C c) Y • χX) ρ := by
      have e0 := (Verma.shap (C c) (X : K[X]) (VirEnv.negOp (C c) Y • χX)).map_smul
        (X - C h₀) ρ
      rw [Verma.negOp_cons_smul, hBX.2, neg_neg, hρ, map_add, map_list_sum, List.map_map,
        e0, smul_eq_mul]
      congr 2
      refine List.map_congr_left fun t _ => ?_
      rw [Function.comp_apply]
      exact (Verma.shap (C c) (X : K[X]) (VirEnv.negOp (C c) Y • χX)).map_smul t.2 _
    rw [e, dAt_add, dAt_X_sub_C_mul, hradL, add_zero, dAt_list_sum, List.map_map,
      gramWord_cons c (h₀ + (ℓ : K)) y Y w hw, hact, mapSt, List.map_map,
      ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp_apply, coe_evalRingHom]
    rw [dAt_mul, hradL, mul_zero, zero_add, ih hY' t.1 (posSt_actWord _ _ hw _ t ht)]
    ring

/-- The pairing of `L_{-Y} χ_X` and `L_{-w} χ_X` in coordinates. -/
theorem shap_negOp_pbwCoord (Y w : List ℕ) (hw : PosWord w) (q : Nat.Partition ℓ → K[X]) :
    Verma.shap (C c) (X : K[X]) (VirEnv.negOp (C c) Y • Verma.pbwCoord ℓ q)
        (VirEnv.negOp (C c) w • Verma.pbwCoord ℓ q)
      = ∑ Z : Nat.Partition ℓ, ∑ Z' : Nat.Partition ℓ,
          q Z * q Z' * gramWord (C c) (X : K[X]) (Y ++ Z.word) (w ++ Z'.word) := by
  have hBX := Verma.isShapovalov_shap (c := C c) (h := (X : K[X]))
  have e : ∀ Y : List ℕ, VirEnv.negOp (C c) Y • Verma.pbwCoord (c := C c) (h := (X : K[X])) ℓ q
      = ∑ Z : Nat.Partition ℓ, q Z • Verma.neg (Y ++ Z.word) := by
    intro Y
    rw [Verma.pbwCoord_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [Verma.neg_append]
    exact (smul_comm (q Z) (VirEnv.negOp (C c) Y) (Verma.neg Z.word)).symm
  rw [e Y, e w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Z _ => Finset.sum_congr rfl fun Z' _ => ?_
  have hpos : PosWord (w ++ Z'.word) := by
    intro z hz
    rw [List.mem_append] at hz
    rcases hz with hz | hz
    · exact hw z hz
    · exact Verma.posWord_word Z' z hz
  rw [hBX.gramWord _ _ hpos]
  ring

/-- Lemma 5.10 for a singular vector of positive level: for `χ = P|h₀⟩` singular of level
`ℓ ≥ 1` with `P` fixed, and partitions `Y, Y'` of `m`,
`d/dh ⟨h| ω(P) L_Y L_{-Y'} P |h⟩ |_{h=h₀} = β_χ G_m(c,h₀+ℓ)_{Y,Y'}`. -/
theorem singular_crossing (hℓ : 1 ≤ ℓ)
    (hχ : Verma.IsSingular (Verma.pbwCoord (c := c) (h := h₀) ℓ p) ℓ) (m : ℕ)
    (Y Y' : Nat.Partition m) :
    (derivative (∑ Z : Nat.Partition ℓ, ∑ Z' : Nat.Partition ℓ,
        C (p Z) * C (p Z') *
          gramWord (C c) (X : K[X]) (Y.word ++ Z.word) (Y'.word ++ Z'.word))).eval h₀
      = crossScalar c h₀ p * gram c (h₀ + (ℓ : K)) m Y Y' := by
  have h1 := crossing_words c h₀ ℓ p hℓ hχ Y.word (Verma.posWord_word Y) Y'.word
    (Verma.posWord_word Y')
  rw [shap_negOp_pbwCoord c ℓ Y.word Y'.word (Verma.posWord_word Y') fun Z => C (p Z)] at h1
  have h2 : Verma.shap (C c) (X : K[X]) (Verma.pbwCoord ℓ fun Z => C (p Z))
      (Verma.pbwCoord ℓ fun Z => C (p Z))
      = gramForm (C c) (X : K[X]) ℓ (fun Y => C (p Y)) (fun Y => C (p Y)) := by
    have h3 := shap_negOp_pbwCoord c ℓ [] [] (fun z hz => by simp at hz) fun Z => C (p Z)
    rw [Verma.negOp_nil_smul] at h3
    rw [h3, gramForm, dotProduct]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Z' _ => ?_
    simp only [List.nil_append, gram, Matrix.of_apply]
    ring
  rw [h2] at h1
  exact h1

end Core

/-- For `χ = P|h₀⟩` singular of level `ℓ ≥ 1` with `P` fixed, and partitions `Y, Y'` of `m`:
`d/dh ⟨h| ω(P) L_Y L_{-Y'} P |h⟩ |_{h=h₀} = β_χ G_m(c,h₀+ℓ)_{Y,Y'}`.

Paper label: lem:singular-crossing -/
theorem lem_singular_crossing : Stmt_lem_singular_crossing :=
  fun c h₀ ℓ p hℓ hχ m Y Y' => singular_crossing c h₀ ℓ p hℓ hχ m Y Y'

example : Stmt_lem_singular_crossing := lem_singular_crossing

end Virasoro
