import Virasoro.Sphere.Statements.Sec2
import Virasoro.Sphere.Statements.Sec4
import Virasoro.Proofs.PairingVac
import Virasoro.Proofs.JantzenLevel
import Virasoro.Proofs.LevelComp
import Virasoro.Proofs.PBWBasis
import Virasoro.Proofs.Crossing

/-!
# Definition 2.1 and Lemma 4.2 of `sphere/paper.tex`: the three-point functional

The functional `φ(u) = ⟨u|Φ_b(1)|Δ_a⟩` with `φ(v_Δ) = 1` and
`φ(L_{-n}u) = φ(L_0u) + (nΔ_b - Δ_a)φ(u)` is constructed from the freeness of the Verma
module over `U(Vir_-)`: the functionals `p ↦ φ(p(L_0)u)` on polynomials `p` form a
representation of `Vir_-`, with `L_{-n}` acting by the transpose of
`p ↦ (X - Δ_a + nΔ_b) p(X + n)`.  Its values on the vectors `L_{-Z}w`, `w` homogeneous, follow
from the defining relation by induction on the word `Z`; this gives the values `γ_Y`,
uniqueness, and Lemma 4.2.
-/

namespace Virasoro

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R} (Δa Δb : R)

namespace Verma

variable (c h)

/-- The map `u ↦ (p ↦ ⟨p(L_0)u|Φ_b(1)|Δ_a⟩)`. -/
noncomputable def ThreeMap : Verma R c h →ₗ[R] (R[X] →ₗ[R] R) :=
  Classical.choose (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (aOp Δa Δb m) : Module.End R (R[X] →ₗ[R] R)))
    (fun m n _ _ => aDual_comm (h := Δa) Δb m n) (leval h))

variable {c h}

theorem ThreeMap_hw (p : R[X]) : ThreeMap c h Δa Δb hw p = p.eval h := by
  have := (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (aOp Δa Δb m) : Module.End R (R[X] →ₗ[R] R)))
    (fun m n _ _ => aDual_comm (h := Δa) Δb m n) (leval h))).1
  rw [ThreeMap, this]
  rfl

theorem ThreeMap_neg {m : ℤ} (hm : 0 < m) (v : Verma R c h) (p : R[X]) :
    ThreeMap c h Δa Δb (L (-m) v) p = ThreeMap c h Δa Δb v (aOp Δa Δb m p) := by
  have := (Classical.choose_spec (exists_negHom (c := c) (h := h)
    (fun m : ℤ => (LinearMap.lcomp R R (aOp Δa Δb m) : Module.End R (R[X] →ₗ[R] R)))
    (fun m n _ _ => aDual_comm (h := Δa) Δb m n) (leval h))).2 m hm v
  rw [ThreeMap, this]
  rfl

/-- `⟨p(L_0) L_0 u|Φ_b(1)|Δ_a⟩ = ⟨(Xp)(L_0) u|Φ_b(1)|Δ_a⟩`. -/
theorem ThreeMap_L_zero (v : Verma R c h) : ∀ p : R[X],
    ThreeMap c h Δa Δb (L 0 v) p = ThreeMap c h Δa Δb v (X * p) := by
  refine induction_L (P := fun v => ∀ p : R[X],
    ThreeMap c h Δa Δb (L 0 v) p = ThreeMap c h Δa Δb v (X * p)) ?_ ?_ ?_ ?_ v
  · intro p
    rw [L_hw_zero, map_smul, LinearMap.smul_apply, ThreeMap_hw, ThreeMap_hw, eval_mul, eval_X,
      smul_eq_mul]
  · intro u v hu hv p
    simp only [map_add, LinearMap.add_apply, hu, hv]
  · intro r v hv p
    simp only [map_smul, LinearMap.smul_apply, hv]
  · intro m hm v hv p
    have e : L 0 (L (-m) v) = L (-m) (L 0 v) + (m : R) • L (-m) v := by
      have := L_L_zero (c := c) (h := h) (-m) v
      rw [this]
      push_cast
      module
    rw [e, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, ThreeMap_neg Δa Δb hm,
      ThreeMap_neg Δa Δb hm, ThreeMap_neg Δa Δb hm, hv, aOp_X_mul, map_add, map_smul]

variable (c h)

/-- The functional `φ(u) = ⟨u|Φ_b(1)|Δ_a⟩`. -/
noncomputable def threePt : Verma R c h →ₗ[R] R :=
  (LinearMap.applyₗ (1 : R[X])) ∘ₗ ThreeMap c h Δa Δb

variable {c h}

theorem threePt_apply (v : Verma R c h) : threePt c h Δa Δb v = ThreeMap c h Δa Δb v 1 := rfl

theorem threePt_hw : threePt c h Δa Δb (hw : Verma R c h) = 1 := by
  rw [threePt_apply, ThreeMap_hw, eval_one]

/-- `φ(L_{-m} u) = φ(L_0 u) + (m Δ_b - Δ_a) φ(u)` for `m > 0`. -/
theorem threePt_neg {m : ℤ} (hm : 0 < m) (v : Verma R c h) :
    threePt c h Δa Δb (L (-m) v) =
      threePt c h Δa Δb (L 0 v) + ((m : R) * Δb - Δa) * threePt c h Δa Δb v := by
  rw [threePt_apply, threePt_apply, threePt_apply, ThreeMap_neg Δa Δb hm, ThreeMap_L_zero,
    aOp_apply, taylor_one, map_one, mul_one, mul_one]
  have e : (X - C Δa + C ((m : R) * Δb) : R[X]) = X + ((m : R) * Δb - Δa) • (1 : R[X]) := by
    rw [smul_eq_C_mul, mul_one, map_sub]
    ring
  rw [e, map_add, map_smul, smul_eq_mul]

end Verma

namespace Sphere

open Verma

variable {Δa Δb}

theorem isThreePoint_threePt (c h Δa Δb : R) : IsThreePoint Δa Δb (threePt c h Δa Δb) := by
  refine ⟨threePt_hw Δa Δb, fun n hn u => ?_⟩
  have := threePt_neg Δa Δb (m := (n : ℤ)) (by exact_mod_cast hn) u
  rw [this]
  push_cast
  rfl

/-- The values of a three-point functional on `L_{-Z}w` for `w` of level `ℓ`. -/
theorem threePoint_negOp {φ : Verma R c h →ₗ[R] R} (hφ : IsThreePoint Δa Δb φ) {ℓ : ℕ}
    {v : Verma R c h} (hv : v ∈ level ℓ) : ∀ Z : List ℕ, PosWord Z →
      φ (VirEnv.negOp c Z • v) = gammaY (h + (ℓ : R)) Δa Δb Z * φ v := by
  intro Z
  induction Z with
  | nil =>
    intro _
    rw [negOp_nil_smul, gammaY, one_mul]
  | cons y Z ih =>
    intro hZ
    have hy : 1 ≤ y := hZ y (List.mem_cons_self)
    have hZ' : PosWord Z := fun z hz => hZ z (List.mem_cons_of_mem _ hz)
    rw [negOp_cons_smul, hφ.2 y hy, L_zero_of_mem_level (negOp_smul_mem_level hv Z), map_smul,
      smul_eq_mul, ih hZ', gammaY]
    push_cast
    ring

theorem hw_mem_level_zero : (hw : Verma R c h) ∈ level 0 := by
  refine mem_level_of_L_zero ?_
  rw [L_hw_zero, Nat.cast_zero, add_zero]

/-- Well-posedness of Definition 2.1.

Paper label: def:sphere-block -/
theorem def_sphere_block : Stmt_def_sphere_block := by
  intro R _ _ c h Δa Δb
  have hval : ∀ φ : Verma R c h →ₗ[R] R, IsThreePoint Δa Δb φ →
      ∀ (N : ℕ) (Y : Nat.Partition N), φ (Verma.neg Y.word) = gammaY h Δa Δb Y.word := by
    intro φ hφ N Y
    have := threePoint_negOp hφ hw_mem_level_zero Y.word (posWord_word Y)
    rw [hφ.1, mul_one, Nat.cast_zero, add_zero] at this
    exact this
  refine ⟨⟨threePt c h Δa Δb, isThreePoint_threePt c h Δa Δb, fun ψ hψ => ?_⟩, hval⟩
  refine LinearMap.ext_on_range span_neg_word_eq_top fun Y => ?_
  rw [hval ψ hψ Y.1 Y.2, hval _ (isThreePoint_threePt c h Δa Δb) Y.1 Y.2]

example : Stmt_def_sphere_block := def_sphere_block

/-- Lemma 4.2.

Paper label: lem:3pt-factor -/
theorem lem_3pt_factor : Stmt_lem_3pt_factor := by
  intro c h Δa Δb φ hφ ℓ w hw M Z
  exact threePoint_negOp hφ (mem_level_of_L_zero hw) Z.word (posWord_word Z)

example : Stmt_lem_3pt_factor := lem_3pt_factor

end Sphere

end Virasoro
