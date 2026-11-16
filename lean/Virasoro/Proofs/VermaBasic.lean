import Virasoro.NormalOrder
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Basic identities in the Verma module

The modes act on classes by left multiplication, the highest-weight vector satisfies
`L_n |h⟩ = 0` (`n > 0`) and `L_0 |h⟩ = h |h⟩`, and the Virasoro relation holds on every vector.
-/

namespace Virasoro

open Submodule

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

/-- The class of an element of the enveloping algebra. -/
noncomputable abbrev mk (x : VirEnv R c) : Verma R c h := Submodule.Quotient.mk x

theorem L_mk (n : ℤ) (x : VirEnv R c) :
    L n (mk (h := h) x) = mk (VirEnv.L c n * x) := rfl

theorem smul_mk (r : R) (x : VirEnv R c) : r • mk (h := h) x = mk (r • x) := rfl

theorem env_smul_mk (y x : VirEnv R c) : y • mk (h := h) x = mk (y * x) := rfl

theorem hw_eq : (hw : Verma R c h) = mk 1 := rfl

theorem neg_eq (w : List ℕ) : neg (c := c) (h := h) w = mk (VirEnv.negOp c w) := by
  rw [neg, hw_eq, env_smul_mk, mul_one]

theorem neg_nil : neg (c := c) (h := h) [] = hw := by
  rw [neg_eq, hw_eq]
  simp [VirEnv.negOp]

theorem neg_cons (y : ℕ) (w : List ℕ) :
    neg (c := c) (h := h) (y :: w) = L (-(y : ℤ)) (neg w) := by
  rw [neg_eq, neg_eq, L_mk]
  simp [VirEnv.negOp]

/-- `L_n |h⟩ = 0` for `n > 0`. -/
theorem L_hw_pos {n : ℤ} (hn : 0 < n) : L n (hw : Verma R c h) = 0 := by
  rw [hw_eq, L_mk, mul_one]
  exact (Submodule.Quotient.mk_eq_zero _).2
    (Submodule.subset_span (Or.inl ⟨n, hn, rfl⟩))

/-- `L_0 |h⟩ = h |h⟩`. -/
theorem L_hw_zero : L 0 (hw : Verma R c h) = h • hw := by
  rw [hw_eq, L_mk, mul_one, smul_mk]
  rw [Submodule.Quotient.eq]
  have : VirEnv.L c 0 - h • (1 : VirEnv R c) = VirEnv.L c 0 - algebraMap R (VirEnv R c) h := by
    rw [Algebra.algebraMap_eq_smul_one]
  rw [this]
  exact Submodule.subset_span (Or.inr rfl)

/-- The Virasoro relation on the Verma module. -/
theorem L_L (m n : ℤ) (v : Verma R c h) :
    L m (L n v) = L n (L m v) + ((m - n : ℤ) : R) • L (m + n) v +
      (if m + n = 0 then centralTerm c m • v else 0) := by
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    rw [L_mk, L_mk, L_mk, L_mk, L_mk, ← mul_assoc, VirEnv.L_mul_L, add_mul, add_mul, mul_assoc]
    split_ifs with h0
    · rw [smul_mk, smul_mk, smul_mul_assoc, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      rfl
    · rw [zero_mul, add_zero, add_zero, smul_mk, smul_mul_assoc]
      rfl

end Verma

end Virasoro
