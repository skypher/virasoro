import Virasoro.Proofs.P2Sec12Box
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The two-step box formula and the Gamma potential (paper.tex l.2716–2749)

The common intersection of the two boxes of (9.4) is cancelled in two steps (equation (12.2),
l.2716–2724): first `b'` is shifted by `m`, then `a` by `k`.  The rows and columns that are
exchanged are the four strips below.  Iterating `Γ(z+1) = zΓ(z)` (l.2725–2743) turns the strip
products into the Gamma potential `Ψ` of (9.5).
-/

namespace Virasoro

open Polynomial

/-- The rows added in the first step: `[1-R,R] × [S+1,S+m]`. -/
noncomputable def stripN1 (R S : ℤ) (m : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (1 - R) R ×ˢ Finset.Icc (S + 1) (S + m)

/-- The rows removed in the first step: `[1-R,R] × [1-S,m-S]`. -/
noncomputable def stripD1 (R S : ℤ) (m : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (1 - R) R ×ˢ Finset.Icc (-S + 1) (-S + m)

/-- The columns added in the second step: `[R+1,R+k] × [1-S+m,S+m]`. -/
noncomputable def stripN2 (R S : ℤ) (k m : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (R + 1) (R + k) ×ˢ Finset.Icc (1 - S + m) (S + m)

/-- The columns removed in the second step: `[1-R,k-R] × [1-S+m,S+m]`. -/
noncomputable def stripD2 (R S : ℤ) (k m : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-R + 1) (-R + k) ×ˢ Finset.Icc (1 - S + m) (S + m)

section TwoStep

variable {α M : Type*} [CommMonoid M]

theorem prod_union_eq [DecidableEq α] {A A' s s' : Finset α} (f : α → M)
    (h : A ∪ s = A' ∪ s') (d1 : Disjoint A s) (d2 : Disjoint A' s') :
    (∏ x ∈ A, f x) * ∏ x ∈ s, f x = (∏ x ∈ A', f x) * ∏ x ∈ s', f x := by
  rw [← Finset.prod_union d1, ← Finset.prod_union d2, h]

/-- The two-step cancellation (12.2), cross-multiplied (l.2716–2724). -/
theorem two_step_box {R S k m : ℕ} (hkR : k < R) (hmS : m < S) (f : ℤ × ℤ → M) :
    (∏ y ∈ (boxShift R S k m).erase (0, 0), f y) *
        ((∏ y ∈ stripD1 R S m, f y) * ∏ y ∈ stripD2 R S k m, f y) =
      (∏ y ∈ (boxSet R S).erase (0, 0), f y) *
        ((∏ y ∈ stripN1 R S m, f y) * ∏ y ∈ stripN2 R S k m, f y) := by
  have s1 : (∏ y ∈ (boxSet R S).erase (0, 0), f y) * ∏ y ∈ stripN1 R S m, f y =
      (∏ y ∈ (Finset.Icc (1 - (R : ℤ)) R ×ˢ Finset.Icc (1 - (S : ℤ) + m) (S + m)).erase (0, 0),
        f y) * ∏ y ∈ stripD1 R S m, f y := by
    refine prod_union_eq f ?_ ?_ ?_
    · ext x
      simp only [boxSet, stripN1, stripD1, Finset.mem_union, Finset.mem_erase,
        Finset.mem_product, Finset.mem_Icc, ne_eq, Prod.ext_iff]
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [boxSet, stripN1, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, ne_eq,
        Prod.ext_iff] at hx hx'
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [stripD1, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, ne_eq,
        Prod.ext_iff] at hx hx'
      omega
  have s2 : (∏ y ∈ (Finset.Icc (1 - (R : ℤ)) R ×ˢ
        Finset.Icc (1 - (S : ℤ) + m) (S + m)).erase (0, 0), f y) * ∏ y ∈ stripN2 R S k m, f y =
      (∏ y ∈ (boxShift R S k m).erase (0, 0), f y) * ∏ y ∈ stripD2 R S k m, f y := by
    refine prod_union_eq f ?_ ?_ ?_
    · ext x
      simp only [boxShift, stripN2, stripD2, Finset.mem_union, Finset.mem_erase,
        Finset.mem_product, Finset.mem_Icc, ne_eq, Prod.ext_iff]
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [stripN2, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, ne_eq,
        Prod.ext_iff] at hx hx'
      omega
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [boxShift, stripD2, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, ne_eq,
        Prod.ext_iff] at hx hx'
      omega
  rw [mul_comm (∏ y ∈ stripD1 R S m, f y), ← mul_assoc, ← s2, mul_right_comm, ← s1, mul_assoc]

theorem prod_Icc_shift (f : ℤ → M) (c : ℤ) (n : ℕ) :
    ∏ j ∈ Finset.Icc 1 n, f (c + (j : ℤ)) = ∏ x ∈ Finset.Icc (c + 1) (c + n), f x := by
  refine Finset.prod_nbij' (fun j : ℕ => c + (j : ℤ)) (fun x : ℤ => (x - c).toNat) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  · intro j _
    show (c + (j : ℤ) - c).toNat = j
    omega
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    show c + ((x - c).toNat : ℤ) = x
    omega
  · intro j _
    rfl

end TwoStep

/-- The value `a t + b'` of a linear factor. -/
noncomputable def linV (t : ℂ) (y : ℤ × ℤ) : ℂ := (y.1 : ℂ) * t + (y.2 : ℂ)

/-- Iteration of `Γ(z+1) = zΓ(z)` for the reciprocal Gamma function (l.2731–2733). -/
theorem recGamma_Icc (z : ℂ) (u : ℤ) : ∀ v : ℤ, u - 1 ≤ v →
    (∏ a ∈ Finset.Icc u v, (z + (a : ℂ))) * (Complex.Gamma (z + v + 1))⁻¹ =
      (Complex.Gamma (z + u))⁻¹ := by
  refine Int.leInduction ?_ ?_
  · have hI : Finset.Icc u (u - 1) = ∅ := Finset.Icc_eq_empty (by omega)
    have e : z + ((u - 1 : ℤ) : ℂ) + 1 = z + u := by push_cast; ring
    rw [hI, Finset.prod_empty, one_mul, e]
  · intro v hv ih
    have hI : Finset.Icc u (v + 1) = insert (v + 1) (Finset.Icc u v) := by
      ext a
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have e : z + ((v + 1 : ℤ) : ℂ) + 1 = z + v + 1 + 1 := by push_cast; ring
    rw [hI, Finset.prod_insert (by simp), ← ih, e,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z + v + 1)]
    push_cast
    ring

/-- A row of the box: `∏_{a=1-R}^{R} (at + c) · 1/Γ(c/t + R + 1) = t^{2R}/Γ(c/t + 1 - R)`. -/
theorem row_gamma {t : ℂ} (ht : t ≠ 0) (R : ℕ) (c : ℤ) :
    (∏ a ∈ Finset.Icc (1 - (R : ℤ)) R, linV t (a, c)) *
        (Complex.Gamma ((c : ℂ) / t + R + 1))⁻¹ =
      t ^ (2 * R) * (Complex.Gamma ((c : ℂ) / t + 1 - R))⁻¹ := by
  have h := recGamma_Icc ((c : ℂ) / t) (1 - (R : ℤ)) R (by omega)
  have hcard : (Finset.Icc (1 - (R : ℤ)) R).card = 2 * R := by
    rw [Int.card_Icc]; omega
  have hprod : ∏ a ∈ Finset.Icc (1 - (R : ℤ)) R, linV t (a, c) =
      t ^ (2 * R) * ∏ a ∈ Finset.Icc (1 - (R : ℤ)) R, ((c : ℂ) / t + (a : ℂ)) := by
    rw [← hcard, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp only [linV]
    field_simp
    ring
  have e1 : (c : ℂ) / t + ((R : ℤ) : ℂ) + 1 = (c : ℂ) / t + R + 1 := by push_cast; ring
  have e2 : (c : ℂ) / t + ((1 - (R : ℤ) : ℤ) : ℂ) = (c : ℂ) / t + 1 - R := by push_cast; ring
  rw [e1, e2] at h
  rw [hprod, mul_assoc, h]

/-- A column of the shifted box:
`∏_{b'=1-S+m}^{S+m} (at + b') · 1/Γ(at + S + m + 1) = 1/Γ(at + 1 - S + m)`. -/
theorem col_gamma (t : ℂ) (S m : ℕ) (a : ℤ) :
    (∏ b' ∈ Finset.Icc (1 - (S : ℤ) + m) (S + m), linV t (a, b')) *
        (Complex.Gamma ((a : ℂ) * t + S + m + 1))⁻¹ =
      (Complex.Gamma ((a : ℂ) * t + 1 - S + m))⁻¹ := by
  have h := recGamma_Icc ((a : ℂ) * t) (1 - (S : ℤ) + m) (S + m) (by omega)
  have e1 : (a : ℂ) * t + (((S : ℤ) + m : ℤ) : ℂ) + 1 = (a : ℂ) * t + S + m + 1 := by
    push_cast; ring
  have e2 : (a : ℂ) * t + ((1 - (S : ℤ) + m : ℤ) : ℂ) = (a : ℂ) * t + 1 - S + m := by
    push_cast; ring
  rw [e1, e2] at h
  exact h

theorem rowStrip {t : ℂ} (ht : t ≠ 0) (R : ℕ) (I : Finset ℤ) :
    (∏ y ∈ Finset.Icc (1 - (R : ℤ)) R ×ˢ I, linV t y) *
        ∏ x ∈ I, (Complex.Gamma ((x : ℂ) / t + R + 1))⁻¹ =
      (t ^ (2 * R)) ^ I.card * ∏ x ∈ I, (Complex.Gamma ((x : ℂ) / t + 1 - R))⁻¹ := by
  rw [Finset.prod_product_right, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun x _ => row_gamma ht R x, Finset.prod_mul_distrib,
    Finset.prod_const]

theorem colStrip (t : ℂ) (S m : ℕ) (J : Finset ℤ) (z₁ z₂ : ℤ → ℂ)
    (h1 : ∀ a : ℤ, z₁ a = (a : ℂ) * t + S + m + 1)
    (h2 : ∀ a : ℤ, z₂ a = (a : ℂ) * t + 1 - S + m) :
    (∏ y ∈ J ×ˢ Finset.Icc (1 - (S : ℤ) + m) (S + m), linV t y) *
        ∏ a ∈ J, (Complex.Gamma (z₁ a))⁻¹ =
      ∏ a ∈ J, (Complex.Gamma (z₂ a))⁻¹ := by
  rw [Finset.prod_product, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [h1, h2]
  exact col_gamma t S m a

/-- The Gamma potential (9.5) at `ϖ = (Rb + S'b⁻¹)/2`, with its factors indexed by the rows
`S'+j`, `-S'+j` and the columns `R+i`, `-R+i`. -/
theorem PsiPot_strip {b : ℂ} (hb : b ≠ 0) (R k m : ℕ) (Sp Sm : ℤ) (hS : Sm = -Sp) :
    PsiPot k m (((R : ℂ) * b + (Sp : ℂ) * b⁻¹) / 2) b =
      ((∏ x ∈ Finset.Icc (Sp + 1) (Sp + m), (Complex.Gamma ((x : ℂ) / b ^ 2 + R + 1))⁻¹) *
          ∏ x ∈ Finset.Icc (Sm + 1) (Sm + m), (Complex.Gamma ((x : ℂ) / b ^ 2 + 1 - R))⁻¹) *
        ((∏ a ∈ Finset.Icc ((R : ℤ) + 1) (R + k),
            (Complex.Gamma ((a : ℂ) * b ^ 2 + Sp + m + 1))⁻¹) *
          ∏ a ∈ Finset.Icc (-(R : ℤ) + 1) (-R + k),
            (Complex.Gamma ((a : ℂ) * b ^ 2 + 1 + Sm + m))⁻¹) := by
  subst hS
  rw [← prod_Icc_shift (fun x : ℤ => (Complex.Gamma ((x : ℂ) / b ^ 2 + R + 1))⁻¹) Sp m,
    ← prod_Icc_shift (fun x : ℤ => (Complex.Gamma ((x : ℂ) / b ^ 2 + 1 - R))⁻¹) (-Sp) m,
    ← prod_Icc_shift (fun a : ℤ => (Complex.Gamma ((a : ℂ) * b ^ 2 + Sp + m + 1))⁻¹) R k,
    ← prod_Icc_shift (fun a : ℤ => (Complex.Gamma ((a : ℂ) * b ^ 2 + 1 + (-Sp : ℤ) + m))⁻¹)
      (-R) k,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, PsiPot]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    have eA : 1 + 2 * (((R : ℂ) * b + (Sp : ℂ) * b⁻¹) / 2) / b + (j : ℂ) / b ^ 2 =
        ((Sp + (j : ℤ) : ℤ) : ℂ) / b ^ 2 + R + 1 := by
      push_cast; field_simp; ring
    have eB : 1 - 2 * (((R : ℂ) * b + (Sp : ℂ) * b⁻¹) / 2) / b + (j : ℂ) / b ^ 2 =
        ((-Sp + (j : ℤ) : ℤ) : ℂ) / b ^ 2 + 1 - R := by
      push_cast; field_simp; ring
    rw [mul_inv, eA, eB]
  · refine Finset.prod_congr rfl fun i _ => ?_
    have eA : 1 + 2 * (((R : ℂ) * b + (Sp : ℂ) * b⁻¹) / 2) * b + (i : ℂ) * b ^ 2 + m =
        (((R : ℤ) + (i : ℤ) : ℤ) : ℂ) * b ^ 2 + Sp + m + 1 := by
      push_cast; field_simp; ring
    have eB : 1 - 2 * (((R : ℂ) * b + (Sp : ℂ) * b⁻¹) / 2) * b + (i : ℂ) * b ^ 2 + m =
        ((-(R : ℤ) + (i : ℤ) : ℤ) : ℂ) * b ^ 2 + 1 + (-Sp : ℤ) + m := by
      push_cast; field_simp; ring
    rw [mul_inv, eA, eB]

/-- The strip products against the Gamma potential (l.2725–2749):
`Num₁ Num₂ Ψ(ϖ_{R,S}) = Den₁ Den₂ Ψ(ϖ_{R,-S})`. -/
theorem psi_box_core {b : ℂ} (hb : b ≠ 0) (R S k m : ℕ) :
    ((∏ y ∈ stripN1 R S m, linV (b ^ 2) y) * ∏ y ∈ stripN2 R S k m, linV (b ^ 2) y) *
        PsiPot k m (((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2) b =
      ((∏ y ∈ stripD1 R S m, linV (b ^ 2) y) * ∏ y ∈ stripD2 R S k m, linV (b ^ 2) y) *
        PsiPot k m (((R : ℂ) * b - (S : ℂ) * b⁻¹) / 2) b := by
  have ht : b ^ 2 ≠ 0 := pow_ne_zero _ hb
  have hin := PsiPot_strip hb R k m (S : ℤ) (-(S : ℤ)) rfl
  have hout := PsiPot_strip hb R k m (-(S : ℤ)) (S : ℤ) (neg_neg _).symm
  have e1 : ((R : ℂ) * b + (((S : ℤ) : ℤ) : ℂ) * b⁻¹) / 2 = ((R : ℂ) * b + (S : ℂ) * b⁻¹) / 2 := by
    push_cast; ring
  have e2 : ((R : ℂ) * b + ((-(S : ℤ) : ℤ) : ℂ) * b⁻¹) / 2 =
      ((R : ℂ) * b - (S : ℂ) * b⁻¹) / 2 := by
    push_cast; ring
  rw [e1] at hin
  rw [e2] at hout
  have hA := rowStrip ht R (Finset.Icc ((S : ℤ) + 1) (S + m))
  have hB := rowStrip ht R (Finset.Icc (-(S : ℤ) + 1) (-S + m))
  have hC := colStrip (b ^ 2) S m (Finset.Icc ((R : ℤ) + 1) (R + k))
    (fun a => (a : ℂ) * b ^ 2 + ((S : ℤ) : ℂ) + m + 1)
    (fun a => (a : ℂ) * b ^ 2 + ((-(S : ℤ) : ℤ) : ℂ) + m + 1)
    (fun a => by push_cast; ring) (fun a => by push_cast; ring)
  have hD := colStrip (b ^ 2) S m (Finset.Icc (-(R : ℤ) + 1) (-R + k))
    (fun a => (a : ℂ) * b ^ 2 + 1 + ((S : ℤ) : ℂ) + m)
    (fun a => (a : ℂ) * b ^ 2 + 1 + ((-(S : ℤ) : ℤ) : ℂ) + m)
    (fun a => by push_cast; ring) (fun a => by push_cast; ring)
  have hc1 : (Finset.Icc ((S : ℤ) + 1) (S + m)).card = m := by rw [Int.card_Icc]; omega
  have hc2 : (Finset.Icc (-(S : ℤ) + 1) (-S + m)).card = m := by rw [Int.card_Icc]; omega
  rw [hc1] at hA
  rw [hc2] at hB
  rw [hin, hout]
  simp only [stripN1, stripN2, stripD1, stripD2]
  beta_reduce at hC hD
  linear_combination
    ((∏ y ∈ Finset.Icc ((R : ℤ) + 1) (R + k) ×ˢ Finset.Icc (1 - (S : ℤ) + m) (S + m),
          linV (b ^ 2) y) *
        (∏ a ∈ Finset.Icc ((R : ℤ) + 1) (R + k),
          (Complex.Gamma ((a : ℂ) * b ^ 2 + ((S : ℤ) : ℂ) + m + 1))⁻¹) *
        (∏ x ∈ Finset.Icc (-(S : ℤ) + 1) (-S + m),
          (Complex.Gamma ((x : ℂ) / b ^ 2 + 1 - R))⁻¹) *
        (∏ a ∈ Finset.Icc (-(R : ℤ) + 1) (-R + k),
          (Complex.Gamma ((a : ℂ) * b ^ 2 + 1 + ((-(S : ℤ) : ℤ) : ℂ) + m))⁻¹)) * hA
    - ((∏ y ∈ Finset.Icc (-(R : ℤ) + 1) (-R + k) ×ˢ Finset.Icc (1 - (S : ℤ) + m) (S + m),
          linV (b ^ 2) y) *
        (∏ a ∈ Finset.Icc (-(R : ℤ) + 1) (-R + k),
          (Complex.Gamma ((a : ℂ) * b ^ 2 + 1 + ((S : ℤ) : ℂ) + m))⁻¹) *
        (∏ x ∈ Finset.Icc ((S : ℤ) + 1) (S + m),
          (Complex.Gamma ((x : ℂ) / b ^ 2 + 1 - R))⁻¹) *
        (∏ a ∈ Finset.Icc ((R : ℤ) + 1) (R + k),
          (Complex.Gamma ((a : ℂ) * b ^ 2 + ((-(S : ℤ) : ℤ) : ℂ) + m + 1))⁻¹)) * hB
    + ((b ^ 2) ^ (2 * R)) ^ m *
        (∏ x ∈ Finset.Icc ((S : ℤ) + 1) (S + m),
          (Complex.Gamma ((x : ℂ) / b ^ 2 + 1 - R))⁻¹) *
        (∏ x ∈ Finset.Icc (-(S : ℤ) + 1) (-S + m),
          (Complex.Gamma ((x : ℂ) / b ^ 2 + 1 - R))⁻¹) *
        (∏ a ∈ Finset.Icc (-(R : ℤ) + 1) (-R + k),
          (Complex.Gamma ((a : ℂ) * b ^ 2 + 1 + ((-(S : ℤ) : ℤ) : ℂ) + m))⁻¹) * hC
    - ((b ^ 2) ^ (2 * R)) ^ m *
        (∏ x ∈ Finset.Icc (-(S : ℤ) + 1) (-S + m),
          (Complex.Gamma ((x : ℂ) / b ^ 2 + 1 - R))⁻¹) *
        (∏ x ∈ Finset.Icc ((S : ℤ) + 1) (S + m),
          (Complex.Gamma ((x : ℂ) / b ^ 2 + 1 - R))⁻¹) *
        (∏ a ∈ Finset.Icc ((R : ℤ) + 1) (R + k),
          (Complex.Gamma ((a : ℂ) * b ^ 2 + ((-(S : ℤ) : ℤ) : ℂ) + m + 1))⁻¹) * hD

end Virasoro
