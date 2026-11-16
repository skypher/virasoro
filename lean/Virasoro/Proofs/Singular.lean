import Virasoro.Proofs.DefMatrices
import Virasoro.Proofs.Shapovalov
import Virasoro.Statements.Sec5a

/-!
# Singular vectors and the torus form on a singular submodule (paper Lemma 5.9)

A vector `χ` with `L_0 χ = h' χ` and `L_n χ = 0` (`n > 0`) defines a homomorphism
`M(c,h') → M(c,h)`, `x|h'⟩ ↦ x χ`.  A bilinear form obeying the Ward identity is determined by
its value on the highest-weight vector, which gives the factorization of the pulled-back torus
form.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

/-- The Ward identity of a primary field of weight `d`, without normalization. -/
def IsWardPairing (d : R) (T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R) : Prop :=
  ∀ (n : ℤ) (u v : Verma R c h),
    T (L (-n) u) v - T u (L n v) = T (L 0 u) v - T u (L 0 v) + (n : R) * d * T u v

variable {d : R} {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R}

theorem ward_hw_neg (hT : IsWardPairing d T) (w : List ℕ) (hw : PosWord w) :
    T Verma.hw (neg w) = T Verma.hw Verma.hw * phi d w := by
  induction w with
  | nil => rw [neg_nil, phi, mul_one]
  | cons m w ih =>
    have hm : 0 < m := hw m List.mem_cons_self
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have e := hT (-(m : ℤ)) Verma.hw (neg w)
    rw [neg_neg, L_hw_pos (by omega), L_hw_zero, L_zero_neg, map_zero, LinearMap.zero_apply,
      map_smul, map_smul, LinearMap.smul_apply, ← neg_cons, ih hw'] at e
    rw [phi]
    simp only [smul_eq_mul, Int.cast_neg, Int.cast_natCast] at e
    linear_combination -e

/-- A bilinear form obeying the Ward identity is its highest-weight value times the
normal-ordering expression `torusWord`. -/
theorem ward_torusWord (hT : IsWardPairing d T) : ∀ Y : List ℕ, PosWord Y →
    ∀ w : List ℕ, PosWord w → T (neg Y) (neg w) = T Verma.hw Verma.hw * torusWord c h d Y w := by
  intro Y
  induction Y with
  | nil =>
    intro _ w hw
    rw [neg_nil, ward_hw_neg hT w hw, torusWord]
  | cons y Y ih =>
    intro hY w hw
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    have e := hT (y : ℤ) (neg Y) (neg w)
    rw [← neg_cons, L_neg_actWord w (y : ℤ), L_zero_neg, L_zero_neg, map_smul, map_smul,
      LinearMap.smul_apply, primary_toVerma, ih hY' w hw] at e
    have e2 : ((actWord c h (y : ℤ) w).map fun t => t.2 * T (neg Y) (neg t.1))
        = (actWord c h (y : ℤ) w).map fun t =>
            T Verma.hw Verma.hw * (t.2 * torusWord c h d Y t.1) := by
      refine List.map_congr_left fun t ht => ?_
      rw [ih hY' t.1 (posSt_actWord c h hw (y : ℤ) t ht)]
      ring
    rw [e2, List.sum_map_mul_left] at e
    rw [torusWord]
    simp only [smul_eq_mul, Int.cast_natCast] at e
    linear_combination e

/-- The homomorphism `M(c,h') → M(c,h)` defined by a vector `χ` with `L_0 χ = h' χ` and
`L_n χ = 0` for `n > 0`. -/
theorem exists_singularHom {χ : Verma R c h} {h' : R} (h0 : L 0 χ = h' • χ)
    (hpos : ∀ n : ℤ, 0 < n → L n χ = 0) :
    ∃ j : Verma R c h' →ₗ[R] Verma R c h, j Verma.hw = χ ∧
      (∀ (n : ℤ) (v : Verma R c h'), j (L n v) = L n (j v)) ∧
      ∀ w : List ℕ, j (neg w) = VirEnv.negOp c w • χ := by
  let g : VirEnv R c →ₗ[R] Verma R c h :=
    { toFun := fun x => x • χ
      map_add' := fun x y => add_smul x y χ
      map_smul' := fun r x => smul_assoc r x χ }
  have hg : ∀ x, g x = x • χ := fun _ => rfl
  have hker : (hwIdeal R c h').restrictScalars R ≤ LinearMap.ker g := by
    intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    rw [LinearMap.mem_ker, hg]
    refine Submodule.span_induction (p := fun x _ => x • χ = 0) ?_ ?_ ?_ ?_ hx
    · rintro x (⟨n, hn, rfl⟩ | rfl)
      · exact hpos n hn
      · rw [sub_smul, algebraMap_smul]
        exact sub_eq_zero.2 h0
    · exact zero_smul _ _
    · intro x y _ _ hx hy
      rw [add_smul, hx, hy, add_zero]
    · intro a x _ hx
      rw [smul_eq_mul, mul_smul, hx, smul_zero]
  let j : Verma R c h' →ₗ[R] Verma R c h :=
    (Submodule.liftQ ((hwIdeal R c h').restrictScalars R) g hker) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv R (hwIdeal R c h')).symm.toLinearMap
  have hj : ∀ x : VirEnv R c, j (Verma.mk x) = x • χ := by
    intro x
    show (Submodule.liftQ ((hwIdeal R c h').restrictScalars R) g hker)
      ((Submodule.Quotient.restrictScalarsEquiv R (hwIdeal R c h')).symm
        (Submodule.Quotient.mk x)) = _
    rw [Submodule.Quotient.restrictScalarsEquiv_symm_mk]
    rfl
  refine ⟨j, ?_, ?_, ?_⟩
  · rw [hw_eq, hj, one_smul]
  · intro n v
    induction v using Submodule.Quotient.induction_on with
    | H x =>
      rw [L_mk]
      show j (Verma.mk _) = L n (j (Verma.mk x))
      rw [hj, hj, mul_smul]
      rfl
  · intro w
    rw [neg_eq, hj]

end Verma

/-- For a singular vector `χ` of level `ℓ` in `M(c,h)` and partitions `Y, Y'` of `m`:
`⟨χ| L_Y V_d(1) L_{-Y'} |χ⟩ = ⟨χ|V_d(1)|χ⟩ ρ_m(c,h+ℓ,d)_{Y,Y'}`.

Paper label: lem:singular-factorization -/
theorem lem_singular_factorization : Stmt_lem_singular_factorization := by
  intro c h d T hT χ ℓ hχ m Y Y'
  obtain ⟨j, hj1, hj2, hj3⟩ := Verma.exists_singularHom hχ.2.1 hχ.2.2
  have hW : Verma.IsWardPairing d (T.compl₁₂ j j) := by
    intro n u v
    simp only [LinearMap.compl₁₂_apply, hj2]
    exact hT.2 n (j u) (j v)
  have := Verma.ward_torusWord hW Y.word (word_pos Y) Y'.word (word_pos Y')
  simp only [LinearMap.compl₁₂_apply, hj1, hj3] at this
  rw [this]
  rfl

example : Stmt_lem_singular_factorization := lem_singular_factorization

end Virasoro
