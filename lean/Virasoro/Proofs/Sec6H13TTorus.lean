import Virasoro.Proofs.Sec6H13TGram
import Virasoro.Proofs.Sec6H13ChainWard
import Virasoro.Proofs.Sec6H13ChainSl2

/-!
# Proposition 6.8(ii): the entries of `ρ̃` at partitions `(1^a, μ)` (paper.tex l.1333–1352)

`⟨Δ|L_1^{a_r} L_{μ_r} V_d(1) L_{−μ_0} L_{−1}^{a_0}|Δ⟩` as a finite sum: move `L_{−1}^{a_r}` (in the
bra vector) past `L_{−μ_r}`, through the field (`ward_pow`); move the `L_1` past `L_{−μ_0}`; the
`L_1` hitting `L_{−1}^{a_0}|Δ⟩` give `L1_pow_Lm1_pow`; move `L_{−1}` past `ad(L_1)^{p_2}(L_{−μ_0})`,
back through the field (the Ward identity of the flipped pairing); the remaining `L_1` act on the
bra vector.  The local bracket is
`⟨Δ| ad(L_1)^s (−ad L_{−1})^{p_1}(L_{−μ_r})^† V_d(1) (−ad L_{−1})^q ad(L_1)^{p_2}(L_{−μ_0})|Δ⟩`.
-/

namespace Virasoro.H13C

open Verma Finset

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h d : R}

/-! ### `L_0`-homogeneous elements of the enveloping algebra -/

/-- `[L_0, x] = D x`. -/
def Homog (c : R) (D : ℤ) (x : VirEnv R c) : Prop :=
  VirEnv.L c 0 * x = x * VirEnv.L c 0 + (D : R) • x

theorem homog_L (n : ℤ) : Homog c (-n) (VirEnv.L c n) := by
  unfold Homog
  rw [VirEnv.L_mul_L]
  by_cases hn : n = 0
  · subst hn
    simp [centralTerm]
  · rw [if_neg (by omega), add_zero, zero_add]
    congr 2
    push_cast
    ring

theorem Homog.mul {D D' : ℤ} {x y : VirEnv R c} (hx : Homog c D x) (hy : Homog c D' y) :
    Homog c (D + D') (x * y) := by
  unfold Homog at *
  rw [← mul_assoc, hx, add_mul, mul_assoc, hy, mul_add, ← mul_assoc, smul_mul_assoc,
    mul_smul_comm]
  push_cast
  rw [add_smul]
  abel

theorem Homog.sub {D : ℤ} {x y : VirEnv R c} (hx : Homog c D x) (hy : Homog c D y) :
    Homog c D (x - y) := by
  unfold Homog at *
  rw [mul_sub, hx, hy, sub_mul, smul_sub]
  abel

theorem homog_one : Homog c 0 (1 : VirEnv R c) := by
  unfold Homog
  simp

theorem homog_pow {D : ℤ} {x : VirEnv R c} (hx : Homog c D x) (n : ℕ) :
    Homog c (n * D) (x ^ n) := by
  induction n with
  | zero => simpa using homog_one
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hx
    convert this using 2
    push_cast
    ring

theorem homog_negOp (μ : List ℕ) : Homog c (μ.sum : ℤ) (VirEnv.negOp c μ) := by
  induction μ with
  | nil => simpa [VirEnv.negOp] using homog_one
  | cons y μ ih =>
    have e : VirEnv.negOp c (y :: μ) = VirEnv.L c (-(y : ℤ)) * VirEnv.negOp c μ := by
      simp [VirEnv.negOp]
    rw [e]
    have := (homog_L (c := c) (-(y : ℤ))).mul ih
    convert this using 2
    rw [List.sum_cons]
    push_cast
    ring

theorem homog_adp {D : ℤ} {X : VirEnv R c} (hX : Homog c D X) (p : ℕ) :
    Homog c (D - p) (adp (VirEnv.L c 1) p X) := by
  induction p with
  | zero => simpa [adp_zero] using hX
  | succ p ih =>
    rw [adp_succ]
    have h1 := (homog_L (c := c) 1).mul ih
    have h2 := ih.mul (homog_L (c := c) 1)
    have e1 : (-(1 : ℤ)) + (D - p) = D - ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : (D - p) + (-(1 : ℤ)) = D - ((p + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1] at h1
    rw [e2] at h2
    exact h1.sub h2

theorem homog_nadp {D : ℤ} {X : VirEnv R c} (hX : Homog c D X) (q : ℕ) :
    Homog c (D + q) (nadp (VirEnv.L c (-1)) q X) := by
  induction q with
  | zero => simpa [nadp] using hX
  | succ q ih =>
    rw [nadp_succ]
    have h1 := ih.mul (homog_L (c := c) (-1))
    have h2 := (homog_L (c := c) (-1)).mul ih
    have e1 : (D + q) + -(-1 : ℤ) = D + ((q + 1 : ℕ) : ℤ) := by push_cast; ring
    have e2 : -(-1 : ℤ) + (D + q) = D + ((q + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1] at h1
    rw [e2] at h2
    exact h1.sub h2

/-- A homogeneous element applied to `|Δ⟩` is an `L_0`-eigenvector. -/
theorem L0_homog_hw {D : ℤ} {x : VirEnv R c} (hx : Homog c D x) :
    L 0 (x • (hw : Verma R c h)) = (h + (D : R)) • (x • (hw : Verma R c h)) := by
  have e : L 0 (x • (hw : Verma R c h)) = (VirEnv.L c 0 * x) • (hw : Verma R c h) := by
    rw [mul_smul]
    rfl
  rw [e, hx, add_smul, mul_smul, smul_assoc]
  have e2 : VirEnv.L c 0 • (hw : Verma R c h) = h • hw := L_hw_zero
  rw [e2, smul_comm x h hw]
  generalize x • (hw : Verma R c h) = v
  module

/-! ### The flipped pairing and the adjoint Ward identity -/

theorem isPrimaryPairing_flip {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R}
    (hT : IsPrimaryPairing d T) : IsPrimaryPairing d T.flip := by
  refine ⟨hT.1, fun n u v => ?_⟩
  simp only [LinearMap.flip_apply]
  have e := hT.2 (-n) v u
  rw [neg_neg] at e
  push_cast at e
  linear_combination -e

theorem L_pow_apply (n : ℤ) (a : ℕ) (v : Verma R c h) :
    (L n ^ a) v = (VirEnv.L c n ^ a) • v := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, ih, pow_succ', mul_smul]
    rfl

/-- `⟨u|V_d(1) L_{−1}^a|y⟩ = ∑_m C(a,m) ∏_{i<m}(d + h_y − h_u + a − 1 − i) ⟨L_{−1}^{a−m}u|V_d(1)|y⟩`
(the contravariant adjoint of `ward_pow`, paper.tex l.1344). -/
theorem ward_pow_adj {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hT : IsPrimaryPairing d T)
    {y : Verma R c h} {hy : R} (h1 : L 0 y = hy • y) (a : ℕ) (u : Verma R c h) (hu : R)
    (h2 : L 0 u = hu • u) :
    T u ((L (-1) ^ a) y) = ∑ m ∈ range (a + 1),
      (a.choose m : R) * (∏ i ∈ range m, (d + hy - hu + (a : R) - 1 - (i : R))) *
        T ((L 1 ^ (a - m)) u) y := by
  have := ward_pow (isPrimaryPairing_flip hT) h1 a u hu h2
  simpa only [LinearMap.flip_apply] using this

/-! ### `L_1^s` on `X|Δ⟩` -/

theorem L1_pow_smul_hw (X : VirEnv R c) (s : ℕ) :
    (VirEnv.L c 1 ^ s * X) • (hw : Verma R c h) = adp (VirEnv.L c 1) s X • (hw : Verma R c h) := by
  rw [pow_mul_eq_sum_ad, sum_smul]
  rw [sum_eq_single s]
  · rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, one_smul]
  · intro p hp hps
    have hp' : p < s := by have := mem_range.1 hp; omega
    obtain ⟨j, hj⟩ : ∃ j, s - p = j + 1 := ⟨s - p - 1, by omega⟩
    rw [hj, smul_assoc, mul_smul, pow_succ, mul_smul]
    have : VirEnv.L c 1 • (hw : Verma R c h) = 0 := L_hw_pos one_pos
    rw [this, smul_zero, smul_zero, smul_zero]
  · intro hs
    exact absurd (mem_range.2 (Nat.lt_succ_self s)) hs

/-! ### The four steps -/

theorem neg_append_ones_eq (μ : List ℕ) (a : ℕ) :
    neg (c := c) (h := h) (μ ++ List.replicate a 1) = VirEnv.negOp c μ • vb c h a := by
  rw [neg, negOp_append_ones, mul_smul]
  rfl

/-- `X L_{−1}^b|Δ⟩ = ∑_q C(b,q) L_{−1}^{b−q} (−ad L_{−1})^q(X)|Δ⟩`. -/
theorem smul_vb_expand (X : VirEnv R c) (b : ℕ) :
    X • vb c h b = ∑ q ∈ range (b + 1),
      (b.choose q : R) • (L (-1) ^ (b - q)) (nadp (VirEnv.L c (-1)) q X • (hw : Verma R c h)) := by
  rw [vb, ← mul_smul, mul_pow_eq_sum_nad, sum_smul]
  refine sum_congr rfl fun q _ => ?_
  rw [smul_assoc, ← Nat.cast_smul_eq_nsmul R, L_pow_apply, mul_smul]

/-- `L_1^r L_{−μ₀} L_{−1}^{a₀}|Δ⟩ = ∑_{p₂} C(r,p₂) a₀^{\underline k} ∏(2Δ + s)
ad(L_1)^{p₂}(L_{−μ₀}) L_{−1}^{a₀−k}|Δ⟩`, `k = r − p₂`. -/
theorem L1_pow_negOp_vb (μ : List ℕ) (a r : ℕ) :
    (L 1 ^ r) (VirEnv.negOp c μ • vb c h a) = ∑ p ∈ range (r + 1), (r.choose p : R) •
      (((a.descFactorial (r - p) : ℕ) : R) * ∏ s ∈ Ico (a - (r - p)) a, (2 * h + (s : R))) •
        (adp (VirEnv.L c 1) p (VirEnv.negOp c μ) • vb c h (a - (r - p))) := by
  rw [L_pow_apply, ← mul_smul, pow_mul_eq_sum_ad, sum_smul]
  refine sum_congr rfl fun p _ => ?_
  rw [smul_assoc, ← Nat.cast_smul_eq_nsmul R, mul_smul, L1_pow_Lm1_pow,
    smul_comm (adp (VirEnv.L c 1) p (VirEnv.negOp c μ))
      ((((a.descFactorial (r - p)) : ℕ) : R) * ∏ s ∈ Ico (a - (r - p)) a, (2 * h + (s : R)))]

/-- The local bracket of the `ρ̃` entry. -/
noncomputable def torBr (T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R) (μr μ0 : List ℕ)
    (p1 s p2 q : ℕ) : R :=
  T (adp (VirEnv.L c 1) s (nadp (VirEnv.L c (-1)) p1 (VirEnv.negOp c μr)) • (hw : Verma R c h))
    (nadp (VirEnv.L c (-1)) q (adp (VirEnv.L c 1) p2 (VirEnv.negOp c μ0)) • (hw : Verma R c h))

/-- `⟨Δ|L_1^{a_r} L_{μ_r} V_d(1) L_{−μ₀} L_{−1}^{a₀}|Δ⟩` (paper.tex l.1333–1352), as it comes out of
the steps: `n = a_r − p₁`, `r̃ = n − m_L`, `k = r̃ − p₂`, `b = a₀ − k`, `n' = b − q`, `s = n' − m'`. -/
theorem torus_ones {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hT : IsPrimaryPairing d T)
    (μr μ0 : List ℕ) (ar a0 : ℕ) :
    T (neg (μr ++ List.replicate ar 1)) (neg (μ0 ++ List.replicate a0 1)) =
      ∑ p1 ∈ range (ar + 1), (ar.choose p1 : R) *
        ∑ mL ∈ range (ar - p1 + 1), ((ar - p1).choose mL : R) *
          (∏ u ∈ range mL, (d + (h + (((μr.sum : ℤ) + p1 : ℤ) : R)) -
            (h + ((μ0.sum + a0 : ℕ) : R)) + ((ar - p1 : ℕ) : R) - 1 - (u : R))) *
          ∑ p2 ∈ range (ar - p1 - mL + 1), ((ar - p1 - mL).choose p2 : R) *
            ((((a0.descFactorial (ar - p1 - mL - p2)) : ℕ) : R) *
              ∏ s ∈ Ico (a0 - (ar - p1 - mL - p2)) a0, (2 * h + (s : R))) *
            ∑ q ∈ range (a0 - (ar - p1 - mL - p2) + 1),
              ((a0 - (ar - p1 - mL - p2)).choose q : R) *
              ∑ m' ∈ range (a0 - (ar - p1 - mL - p2) - q + 1),
                ((a0 - (ar - p1 - mL - p2) - q).choose m' : R) *
                (∏ i ∈ range m', (d + (h + ((((μ0.sum : ℤ) - p2) + q : ℤ) : R)) -
                  (h + (((μr.sum : ℤ) + p1 : ℤ) : R)) +
                  ((a0 - (ar - p1 - mL - p2) - q : ℕ) : R) - 1 - (i : R))) *
                torBr T μr μ0 p1 (a0 - (ar - p1 - mL - p2) - q - m') p2 q := by
  have hW : L 0 (neg (c := c) (h := h) (μ0 ++ List.replicate a0 1)) =
      (h + ((μ0.sum + a0 : ℕ) : R)) • neg (μ0 ++ List.replicate a0 1) := by
    rw [L_zero_neg, List.sum_append, List.sum_replicate, smul_eq_mul, mul_one]
  rw [neg_append_ones_eq μr ar, smul_vb_expand, map_sum, LinearMap.sum_apply]
  refine sum_congr rfl fun p1 _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  have hu : L 0 (nadp (VirEnv.L c (-1)) p1 (VirEnv.negOp c μr) • (hw : Verma R c h)) =
      (h + (((μr.sum : ℤ) + p1 : ℤ) : R)) •
        (nadp (VirEnv.L c (-1)) p1 (VirEnv.negOp c μr) • (hw : Verma R c h)) :=
    L0_homog_hw (homog_nadp (homog_negOp μr) p1)
  rw [ward_pow hT hu (ar - p1) _ _ hW]
  refine sum_congr rfl fun mL _ => ?_
  congr 1
  rw [neg_append_ones_eq μ0 a0, L1_pow_negOp_vb, map_sum]
  refine sum_congr rfl fun p2 _ => ?_
  have key : T (nadp (VirEnv.L c (-1)) p1 (VirEnv.negOp c μr) • (hw : Verma R c h))
      (adp (VirEnv.L c 1) p2 (VirEnv.negOp c μ0) • vb c h (a0 - (ar - p1 - mL - p2))) =
      ∑ q ∈ range (a0 - (ar - p1 - mL - p2) + 1),
        ((a0 - (ar - p1 - mL - p2)).choose q : R) *
        ∑ m' ∈ range (a0 - (ar - p1 - mL - p2) - q + 1),
          ((a0 - (ar - p1 - mL - p2) - q).choose m' : R) *
          (∏ i ∈ range m', (d + (h + ((((μ0.sum : ℤ) - p2) + q : ℤ) : R)) -
            (h + (((μr.sum : ℤ) + p1 : ℤ) : R)) +
            ((a0 - (ar - p1 - mL - p2) - q : ℕ) : R) - 1 - (i : R))) *
          torBr T μr μ0 p1 (a0 - (ar - p1 - mL - p2) - q - m') p2 q := by
    rw [smul_vb_expand, map_sum]
    refine sum_congr rfl fun q _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    have hy : L 0 (nadp (VirEnv.L c (-1)) q (adp (VirEnv.L c 1) p2 (VirEnv.negOp c μ0)) •
        (hw : Verma R c h)) = (h + ((((μ0.sum : ℤ) - p2) + q : ℤ) : R)) •
          (nadp (VirEnv.L c (-1)) q (adp (VirEnv.L c 1) p2 (VirEnv.negOp c μ0)) •
            (hw : Verma R c h)) :=
      L0_homog_hw (homog_nadp (homog_adp (homog_negOp μ0) p2) q)
    rw [ward_pow_adj hT hy _ _ _ hu]
    refine sum_congr rfl fun m' _ => ?_
    congr 1
    rw [torBr, L_pow_apply, ← mul_smul, L1_pow_smul_hw]
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, key]
  ring

end Virasoro.H13C
