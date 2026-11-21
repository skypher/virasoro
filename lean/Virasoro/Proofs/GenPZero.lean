import Virasoro.Proofs.Specialize
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The fusion polynomial at external weight `d = 0` (proof of Lemma 6.5, paper.tex l.1073–1083)

Write `φ(x,y) = x b + y b⁻¹` and `B = [1-r,r] × [1-s,s]`.  At `d = 0` the factors of `𝒫_{r,s}`
are `¼ φ(1-k,1∓l) φ(1+k,1±l)`, and over the odd `k, l` and both signs these products run once
over `φ(p,q)`, `(p,q) ∈ B`.  The factor with `(k,±l) = (1,1)` equals `-d`.  Comparison with
`𝒜_{r,s}`, whose product runs over `B ∖ {(0,0),(r,s)}`, gives
`∂_d ℛ_{r,s}|_{d=0} = -φ(r,s)/(2φ(1,1))`.

Consumer: `lem_d_derivatives_of_cited` in `Virasoro/Proofs/Sec6DDeriv.lean`.
-/

namespace Virasoro

open Polynomial

section Reindex

variable {M : Type*} [CommMonoid M]

theorem oddsBelow_eq (n : ℕ) : oddsBelow n = (Finset.range n).image fun i => 2 * i + 1 := by
  ext k
  simp only [oddsBelow, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨k / 2, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    omega

theorem prod_oddsBelow (n : ℕ) (F : ℕ → M) :
    ∏ k ∈ oddsBelow n, F k = ∏ i ∈ Finset.range n, F (2 * i + 1) := by
  rw [oddsBelow_eq, Finset.prod_image]
  intro x _ y _ h
  have h' : 2 * x + 1 = 2 * y + 1 := h
  omega

/-- The interval `[1-r, r]` is `{-i, i+1 : 0 ≤ i < r}`. -/
theorem prod_Icc_symm (G : ℤ → M) (r : ℕ) :
    ∏ p ∈ Finset.Icc (1 - (r : ℤ)) r, G p =
      ∏ i ∈ Finset.range r, G (-(i : ℤ)) * G ((i : ℤ) + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have e : Finset.Icc (1 - ((r + 1 : ℕ) : ℤ)) ((r + 1 : ℕ) : ℤ) =
        insert (-(r : ℤ)) (insert ((r : ℤ) + 1) (Finset.Icc (1 - (r : ℤ)) r)) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    have h1 : -(r : ℤ) ∉ insert ((r : ℤ) + 1) (Finset.Icc (1 - (r : ℤ)) r) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    have h2 : (r : ℤ) + 1 ∉ Finset.Icc (1 - (r : ℤ)) r := by
      simp only [Finset.mem_Icc]
      omega
    rw [e, Finset.prod_insert h1, Finset.prod_insert h2, ih, Finset.prod_range_succ, ← mul_assoc,
      mul_comm]

/-- The box `B = [1-r,r] × [1-s,s]` in the four quadrants. -/
theorem prod_box (g : ℤ × ℤ → M) (r s : ℕ) :
    ∏ pq ∈ Finset.Icc (1 - (r : ℤ)) r ×ˢ Finset.Icc (1 - (s : ℤ)) s, g pq =
      ∏ ij ∈ Finset.range r ×ˢ Finset.range s,
        (g (-(ij.1 : ℤ), -(ij.2 : ℤ)) * g ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)) *
          (g (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * g ((ij.1 : ℤ) + 1, -(ij.2 : ℤ))) := by
  rw [Finset.prod_product, Finset.prod_product,
    prod_Icc_symm (fun p => ∏ q ∈ Finset.Icc (1 - (s : ℤ)) s, g (p, q))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [prod_Icc_symm (fun q => g (-(i : ℤ), q)), prod_Icc_symm (fun q => g ((i : ℤ) + 1, q)),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm (g ((i : ℤ) + 1, -(j : ℤ))), mul_mul_mul_comm]

end Reindex

variable {𝔽 : Type} [Field 𝔽]

/-- `φ(p,q) = p b + q b⁻¹`. -/
def phiL (b : 𝔽) (pq : ℤ × ℤ) : 𝔽 := (pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹

variable [CharZero 𝔽]

/-- The factor of `(i,j)` at `d = 0`: `φ(-i,-j) φ(i+1,j+1) φ(-i,j+1) φ(i+1,-j)`. -/
def tfun (b : 𝔽) (ij : ℕ × ℕ) : 𝔽 :=
  (phiL b (-(ij.1 : ℤ), -(ij.2 : ℤ)) * phiL b ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)) *
    (phiL b (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * phiL b ((ij.1 : ℤ) + 1, -(ij.2 : ℤ)))

theorem genPpoly_eq (r s : ℕ) (b : 𝔽) :
    genPpoly r s b = ∏ ij ∈ Finset.range r ×ˢ Finset.range s,
      (C (phiL b (-(ij.1 : ℤ), -(ij.2 : ℤ)) * phiL b ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)) - X) *
        (C (phiL b (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * phiL b ((ij.1 : ℤ) + 1, -(ij.2 : ℤ))) - X) := by
  rw [genPpoly, prod_oddsBelow, Finset.prod_product]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [prod_oddsBelow]
  refine Finset.prod_congr rfl fun j _ => ?_
  have e1 : ((b + b⁻¹) ^ 2 - (((2 * i + 1 : ℕ) : 𝔽) * b + ((2 * j + 1 : ℕ) : 𝔽) * b⁻¹) ^ 2) / 4 =
      phiL b (-(i : ℤ), -(j : ℤ)) * phiL b ((i : ℤ) + 1, (j : ℤ) + 1) := by
    simp only [phiL]
    push_cast
    ring
  have e2 : ((b + b⁻¹) ^ 2 - (((2 * i + 1 : ℕ) : 𝔽) * b - ((2 * j + 1 : ℕ) : 𝔽) * b⁻¹) ^ 2) / 4 =
      phiL b (-(i : ℤ), (j : ℤ) + 1) * phiL b ((i : ℤ) + 1, -(j : ℤ)) := by
    simp only [phiL]
    push_cast
    ring
  rw [e1, e2]

/-- `𝒫_{r,s}` vanishes at `d = 0`, and its `d`-derivative there is
`-φ(0,1) φ(1,0) ∏_{(i,j) ≠ (0,0)} φ(-i,-j) φ(i+1,j+1) φ(-i,j+1) φ(i+1,-j)`. -/
theorem genPpoly_coeff (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (b : 𝔽) :
    (genPpoly r s b).coeff 0 = 0 ∧
    (genPpoly r s b).coeff 1 = -((phiL b (0, 1) * phiL b (1, 0)) *
      ∏ ij ∈ (Finset.range r ×ˢ Finset.range s).erase (0, 0), tfun b ij) := by
  have hmem : ((0 : ℕ), (0 : ℕ)) ∈ Finset.range r ×ˢ Finset.range s := by
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨hr, hs⟩
  have h00 : phiL b (0, 0) = 0 := by simp [phiL]
  have hfac : genPpoly r s b = X * (-((C (phiL b (0, 1) * phiL b (1, 0)) - X) *
      ∏ ij ∈ (Finset.range r ×ˢ Finset.range s).erase (0, 0),
        (C (phiL b (-(ij.1 : ℤ), -(ij.2 : ℤ)) * phiL b ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)) - X) *
          (C (phiL b (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * phiL b ((ij.1 : ℤ) + 1, -(ij.2 : ℤ))) - X))) := by
    rw [genPpoly_eq, ← Finset.mul_prod_erase _ _ hmem]
    simp only [Nat.cast_zero, neg_zero, zero_add, h00, zero_mul, map_zero, zero_sub]
    ring
  rw [hfac]
  refine ⟨by simp, ?_⟩
  rw [coeff_X_mul, coeff_neg, coeff_zero_eq_eval_zero, eval_mul, eval_prod]
  simp only [eval_sub, eval_C, eval_X, sub_zero, eval_mul, tfun]

/-- `φ` away from `(0,0)`, and `1` at `(0,0)`. -/
noncomputable def gOne (b : 𝔽) (pq : ℤ × ℤ) : 𝔽 := if pq = (0, 0) then 1 else phiL b pq

omit [CharZero 𝔽] in
theorem gOne_of_ne (b : 𝔽) {pq : ℤ × ℤ} (h : pq ≠ (0, 0)) : gOne b pq = phiL b pq := if_neg h

/-- `φ(1,1) φ(0,1) φ(1,0) ∏_{(i,j) ≠ (0,0)} (…) = φ(r,s) ∏_{B ∖ {(0,0),(r,s)}} φ`: both sides are
the product of `φ` over `B ∖ {(0,0)}`. -/
theorem box_identity (r s : ℕ) (hr : 0 < r) (hs : 0 < s) (b : 𝔽) :
    phiL b (1, 1) * ((phiL b (0, 1) * phiL b (1, 0)) *
        ∏ ij ∈ (Finset.range r ×ˢ Finset.range s).erase (0, 0), tfun b ij) =
      phiL b ((r : ℤ), (s : ℤ)) * ∏ pq ∈ genAIndex r s, phiL b pq := by
  classical
  obtain ⟨Bx, hBx⟩ : ∃ Bx : Finset (ℤ × ℤ),
      Bx = Finset.Icc (1 - (r : ℤ)) r ×ˢ Finset.Icc (1 - (s : ℤ)) s := ⟨_, rfl⟩
  have hidx : genAIndex r s = (Bx.erase (0, 0)).erase ((r : ℤ), (s : ℤ)) := by
    ext pq
    simp only [genAIndex, Finset.mem_filter, Finset.mem_erase, hBx]
    tauto
  have hrs : ((r : ℤ), (s : ℤ)) ∈ Bx.erase (0, 0) := by
    simp only [hBx, Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, ne_eq, Prod.mk.injEq]
    omega
  rw [hidx, Finset.mul_prod_erase _ _ hrs]
  have hg : ∏ pq ∈ Bx.erase (0, 0), phiL b pq = ∏ pq ∈ Bx, gOne b pq := by
    have hpe := Finset.prod_erase Bx (f := gOne b) (a := ((0 : ℤ), (0 : ℤ))) (by simp [gOne])
    rw [← hpe]
    exact Finset.prod_congr rfl fun pq hpq => (gOne_of_ne b (Finset.ne_of_mem_erase hpq)).symm
  have hmem : ((0 : ℕ), (0 : ℕ)) ∈ Finset.range r ×ˢ Finset.range s := by
    simp only [Finset.mem_product, Finset.mem_range]
    exact ⟨hr, hs⟩
  have hsplit := Finset.mul_prod_erase (Finset.range r ×ˢ Finset.range s)
    (fun ij : ℕ × ℕ =>
      (gOne b (-(ij.1 : ℤ), -(ij.2 : ℤ)) * gOne b ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)) *
        (gOne b (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * gOne b ((ij.1 : ℤ) + 1, -(ij.2 : ℤ)))) hmem
  rw [hg, hBx, prod_box, ← hsplit]
  have h0 : (gOne b (-((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ)) *
        gOne b (((0 : ℕ) : ℤ) + 1, ((0 : ℕ) : ℤ) + 1)) *
      (gOne b (-((0 : ℕ) : ℤ), ((0 : ℕ) : ℤ) + 1) * gOne b (((0 : ℕ) : ℤ) + 1, -((0 : ℕ) : ℤ))) =
      phiL b (1, 1) * (phiL b (0, 1) * phiL b (1, 0)) := by
    simp [gOne]
  have hrest : ∏ ij ∈ (Finset.range r ×ˢ Finset.range s).erase (0, 0), tfun b ij =
      ∏ ij ∈ (Finset.range r ×ˢ Finset.range s).erase (0, 0),
        (gOne b (-(ij.1 : ℤ), -(ij.2 : ℤ)) * gOne b ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)) *
          (gOne b (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * gOne b ((ij.1 : ℤ) + 1, -(ij.2 : ℤ))) := by
    refine Finset.prod_congr rfl fun ij hij => ?_
    have hne : ij ≠ (0, 0) := Finset.ne_of_mem_erase hij
    have hne' : ¬ (ij.1 = 0 ∧ ij.2 = 0) := fun h => hne (Prod.ext h.1 h.2)
    have c1 : ((-(ij.1 : ℤ), -(ij.2 : ℤ)) : ℤ × ℤ) ≠ (0, 0) := by
      rw [ne_eq, Prod.mk.injEq]
      omega
    have c2 : (((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1) : ℤ × ℤ) ≠ (0, 0) := by
      rw [ne_eq, Prod.mk.injEq]
      omega
    have c3 : ((-(ij.1 : ℤ), (ij.2 : ℤ) + 1) : ℤ × ℤ) ≠ (0, 0) := by
      rw [ne_eq, Prod.mk.injEq]
      omega
    have c4 : (((ij.1 : ℤ) + 1, -(ij.2 : ℤ)) : ℤ × ℤ) ≠ (0, 0) := by
      rw [ne_eq, Prod.mk.injEq]
      omega
    rw [gOne_of_ne b c1, gOne_of_ne b c2, gOne_of_ne b c3, gOne_of_ne b c4, tfun]
  rw [hrest, ← mul_assoc]
  exact congrArg (· * _) h0.symm

/-- `𝒜_{r,s}(b) ∂_d 𝒫_{r,s}(b,d)|_{d=0} = -(r b² + s)/(2(b² + 1))`. -/
theorem genA_mul_coeff_one (r s : ℕ) (hr : 0 < r) (hs : 0 < s) {b : 𝔽} (hb : b ≠ 0)
    (hb1 : b ^ 2 + 1 ≠ 0)
    (hA : (2 * ∏ pq ∈ genAIndex r s, ((pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹)) ≠ 0) :
    genA r s b * (genPpoly r s b).coeff 1 =
      -(((r : 𝔽) * b ^ 2 + (s : 𝔽)) / (2 * (b ^ 2 + 1))) := by
  have hPi : ∏ pq ∈ genAIndex r s, phiL b pq ≠ 0 := fun h0 => hA (by
    have : ∏ pq ∈ genAIndex r s, ((pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹) = 0 := h0
    rw [this, mul_zero])
  have h11 : phiL b (1, 1) ≠ 0 := by
    have : phiL b (1, 1) = (b ^ 2 + 1) / b := by
      simp only [phiL]
      field_simp
      push_cast
      ring
    rw [this]
    exact div_ne_zero hb1 hb
  have hbox := box_identity r s hr hs b
  have hgenA : genA r s b = 2⁻¹ * (∏ pq ∈ genAIndex r s, phiL b pq)⁻¹ := by
    rw [genA, Finset.prod_inv_distrib]
    rfl
  have hrs : phiL b ((r : ℤ), (s : ℤ)) = ((r : 𝔽) * b ^ 2 + (s : 𝔽)) / b := by
    simp only [phiL]
    field_simp
    push_cast
    ring
  have h11' : phiL b (1, 1) = (b ^ 2 + 1) / b := by
    simp only [phiL]
    field_simp
    push_cast
    ring
  rw [(genPpoly_coeff r s hr hs b).2, hgenA]
  have hT : (phiL b (0, 1) * phiL b (1, 0)) *
      ∏ ij ∈ (Finset.range r ×ˢ Finset.range s).erase (0, 0), tfun b ij =
      phiL b ((r : ℤ), (s : ℤ)) * (∏ pq ∈ genAIndex r s, phiL b pq) / phiL b (1, 1) := by
    rw [← hbox]
    field_simp
  rw [hT, hrs, h11']
  field_simp

end Virasoro
