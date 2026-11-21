import Virasoro.Sphere.Proofs.Sec4Imported
import Virasoro.Sphere.Statements.Sec5
import Virasoro.Proofs.Specialize
import Virasoro.Proofs.Sec3

/-!
# Sphere paper Lemma 5.2 (i): the singular three-point polynomials for odd `k`

`sphere/paper.tex` l.1526–1533.  By Proposition 4.3 the vector `χ_{R,S}(b)` is regular at `b⋆`
with `L_{-1}^{RS}`-coefficient `1` and three-point scalar `P_{R,S}(b⋆,Δ_a,Δ_b)`; its value at
`b⋆` is singular.  The singular space at each level is one-dimensional (Iohara–Koga
Proposition 5.1), so for odd `k`, where `h_{R^±_k,S^±_k}(b⋆) = λ` and `R^±_k S^±_k = ℓ^±_k`,
`w^±_k = χ_{R^±_k,S^±_k}(b⋆)`.
-/

namespace Virasoro.Sphere

open Verma

/-- The value `χ_{R,S}(b⋆)` of the normalized singular vector of Proposition 4.3. -/
theorem exists_chi (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial) {b : ℂ}
    (hb : b ≠ 0) (R S : ℕ) (hR : 0 < R) (hS : 0 < S) :
    ∃ y : Nat.Partition (R * S) → ℂ, y (onesPartition (R * S)) = 1 ∧
      IsSingular (pbwCoord (c := kacC b) (h := kacH R S b) (R * S) y) (R * S) ∧
      ∀ Δa Δb : ℂ, ∑ Y, y Y * gammaY (kacH R S b) Δa Δb Y.word = fusP R S b Δa Δb := by
  obtain ⟨q, ⟨hq1, hqs⟩, -, -, -, hreg⟩ := prop_imported_of_cited hH hF R S hR hS
  obtain ⟨hr, hval⟩ := hreg b hb
  have h1 : RatFunc.eval (algebraMap ℚ ℂ) b (q (onesPartition (R * S))) = 1 := by
    rw [hq1, RatFunc.eval_one]
  refine ⟨fun Y => RatFunc.eval (algebraMap ℚ ℂ) b (q Y), h1, ?_, hval⟩
  exact (specialize_singular (evTo_kacC hb) (evTo_kacH hb R S) q hr hqs
    ⟨_, by rw [h1]; exact one_ne_zero⟩).1

/-- A normalized singular vector of level `n` in `M(c,h)` has the three-point scalar of any
other normalized singular vector of that level. -/
theorem piScalar_eq_of_singular (hU : Cited_SingularUnique) {c h h' : ℂ} {n n' : ℕ}
    (hh : h' = h) (hn : n' = n) (y : Nat.Partition n' → ℂ) (hy1 : y (onesPartition n') = 1)
    (hy : IsSingular (pbwCoord (c := c) (h := h') n' y) n')
    (x : Nat.Partition n → ℂ) (hx1 : x (onesPartition n) = 1)
    (hx : IsSingular (pbwCoord (c := c) (h := h) n x) n) (Δa Δb : ℂ) :
    piScalar h x Δa Δb = ∑ Y, y Y * gammaY h' Δa Δb Y.word := by
  subst hh hn
  obtain ⟨a, ha⟩ := hU c h' n' _ _ hy hx
  rw [← map_smul] at ha
  have hxy := pbwCoord_injective n' ha
  have ha1 : a = 1 := by
    have := congrFun hxy (onesPartition n')
    rw [Pi.smul_apply, hx1, hy1, smul_eq_mul, mul_one] at this
    exact this.symm
  rw [hxy, ha1, one_smul]
  simp [piScalar]

theorem minimal_b_ne_zero {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) : b ≠ 0 := by
  obtain ⟨hp, hp', -, -, -, -, -, -, hb⟩ := hset
  intro h0
  rw [h0] at hb
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : (0 : ℂ) = -(p' : ℂ) / p := by simpa using hb
  field_simp at this
  exact hp'0 (by linear_combination this)

theorem kacH_minimal {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) (R S : ℤ) :
    kacH R S b = (((p' : ℂ) * R - p * S) ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p') := by
  obtain ⟨hp, hp', hcop, -, -, -, -, -, hb⟩ := hset
  exact (prop_minimal_collisions p p' (by omega) (by omega) hcop b hb).2.1 R S

/-- Lemma 5.2 (i). -/
theorem pi_odd (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    {k : ℕ} (ε : Bool) (hk : k % 2 = 1)
    (x : Nat.Partition (ellOrb p p' r s ε k) → ℂ) (hx1 : x (onesPartition _) = 1)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellOrb p p' r s ε k) x)
      (ellOrb p p' r s ε k)) (Δa Δb : ℂ) :
    piScalar (kacH r s b) x Δa Δb =
      (if ε then fusP (r + k / 2 * p) (s + k / 2 * p') b Δa Δb
        else fusP ((k / 2 + 1) * p - r) ((k / 2 + 1) * p' - s) b Δa Δb) := by
  have hb0 := minimal_b_ne_zero hset
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hk0 : k ≠ 0 := by omega
  have hk2 : ¬ k % 2 = 0 := by omega
  cases ε with
  | true =>
    obtain ⟨y, hy1, hys, hyv⟩ := exists_chi hH hF hb0 (r + k / 2 * p) (s + k / 2 * p')
      (by omega) (by omega)
    have hh : kacH ((r + k / 2 * p : ℕ) : ℤ) ((s + k / 2 * p' : ℕ) : ℤ) b = kacH r s b := by
      rw [kacH_minimal hset', kacH_minimal hset']
      push_cast
      ring
    have hn : (r + k / 2 * p) * (s + k / 2 * p') = ellOrb p p' r s true k := by
      simp [ellOrb, ellPlus, hk0, hk2]
    rw [if_pos rfl, piScalar_eq_of_singular hU hh hn y hy1 hys x hx1 hx, hyv]
  | false =>
    have h1 : r ≤ (k / 2 + 1) * p := by
      have : p ≤ (k / 2 + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have h2 : s ≤ (k / 2 + 1) * p' := by
      have : p' ≤ (k / 2 + 1) * p' := Nat.le_mul_of_pos_left _ (by omega)
      omega
    obtain ⟨y, hy1, hys, hyv⟩ := exists_chi hH hF hb0 ((k / 2 + 1) * p - r)
      ((k / 2 + 1) * p' - s) (by have : p ≤ (k / 2 + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
                                 omega)
      (by have : p' ≤ (k / 2 + 1) * p' := Nat.le_mul_of_pos_left _ (by omega)
          omega)
    have hh : kacH (((k / 2 + 1) * p - r : ℕ) : ℤ) (((k / 2 + 1) * p' - s : ℕ) : ℤ) b =
        kacH r s b := by
      rw [kacH_minimal hset', kacH_minimal hset']
      push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
      ring
    have hn : ((k / 2 + 1) * p - r) * ((k / 2 + 1) * p' - s) = ellOrb p p' r s false k := by
      simp [ellOrb, ellMinus, hk0, hk2]
    rw [if_neg (by simp), piScalar_eq_of_singular hU hh hn y hy1 hys x hx1 hx, hyv]

end Virasoro.Sphere
