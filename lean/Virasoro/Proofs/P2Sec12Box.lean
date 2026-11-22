import Virasoro.Statements.Sec12
import Virasoro.Proofs.P2Sec10OrbitArith

/-!
# The reduced box ratio at a minimal-model charge (paper Proposition 12.1(i), l.2757–2787)
-/

namespace Virasoro

open Polynomial

/-- For `R ≡ r` or `p-r (mod p)` and `1 ≤ i ≤ k < min(r,p-r)`: `p ∤ R + i` and `p ∤ i - R`
(l.2788–2800). -/
theorem not_dvd_shift {p r R k : ℕ} (hr0 : 0 < r) (hr : r < p)
    (h : ∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r)) (hk : k < min r (p - r)) (i : ℤ)
    (hi1 : 1 ≤ i) (hik : i ≤ k) : ¬ (p : ℤ) ∣ (R : ℤ) + i ∧ ¬ (p : ℤ) ∣ i - R := by
  rw [lt_min_iff] at hk
  have key : ∀ (x a y : ℤ), x = a * p + y → 0 < y → y < p → ¬ (p : ℤ) ∣ x := by
    intro x a y hx h1 h2 hd
    rw [hx] at hd
    have h3 := (dvd_add_right (Dvd.intro_left a rfl)).1 hd
    have h4 := Int.eq_zero_of_abs_lt_dvd h3 (abs_lt.2 ⟨by linarith, h2⟩)
    omega
  have cr : ((p - r : ℕ) : ℤ) = p - r := Nat.cast_sub hr.le
  obtain ⟨a, rfl | rfl⟩ := h
  · exact ⟨key _ a (r + i) (by push_cast; ring) (by omega) (by omega),
      key _ (-a - 1) (p - r + i) (by push_cast; ring) (by omega) (by omega)⟩
  · exact ⟨key _ a (p - r + i) (by push_cast [cr]; ring) (by omega) (by omega),
      key _ (-a - 1) (r + i) (by push_cast [cr]; ring) (by omega) (by omega)⟩

/-- Every factor `pb' - p'a` on the symmetric difference of the two boxes is nonzero
(l.2785–2800). -/
theorem symdiff_factor_ne {p p' r s R S k m : ℕ} (hcop : Nat.Coprime p p') (hr0 : 0 < r)
    (hr : r < p) (hs0 : 0 < s) (hs : s < p')
    (hcR : ∃ a : ℕ, R = a * p + r ∨ R = a * p + (p - r))
    (hcS : ∃ a : ℕ, S = a * p' + s ∨ S = a * p' + (p' - s))
    (hk : k < min r (p - r)) (hm : m < min s (p' - s)) (x : ℤ × ℤ)
    (hx : x ∈ (boxShift R S k m \ boxSet R S) ∪ (boxSet R S \ boxShift R S k m)) :
    (p : ℤ) * x.2 - (p' : ℤ) * x.1 ≠ 0 := by
  intro h0
  have hd := coprime_two_dvd hcop (x := x.1) (y := x.2) (by linarith)
  simp only [Finset.mem_union, Finset.mem_sdiff, boxSet, boxShift, Finset.mem_product,
    Finset.mem_Icc] at hx
  rcases hx with ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hn⟩ | ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, hn⟩
  · by_cases hc : (R : ℤ) < x.1
    · apply (not_dvd_shift hr0 hr hcR hk (x.1 - R) (by omega) (by omega)).1
      have e : (R : ℤ) + (x.1 - R) = x.1 := by ring
      rw [e]; exact hd.1
    · have hS' : (S : ℤ) < x.2 := by
        by_contra hc'
        exact hn ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
      apply (not_dvd_shift hs0 hs hcS hm (x.2 - S) (by omega) (by omega)).1
      have e : (S : ℤ) + (x.2 - S) = x.2 := by ring
      rw [e]; exact hd.2
  · by_cases hc : x.1 < 1 - (R : ℤ) + k
    · apply (not_dvd_shift hr0 hr hcR hk (x.1 + R) (by omega) (by omega)).2
      have e : x.1 + (R : ℤ) - R = x.1 := by ring
      rw [e]; exact hd.1
    · have hS' : x.2 < 1 - (S : ℤ) + m := by
        by_contra hc'
        exact hn ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
      apply (not_dvd_shift hs0 hs hcS hm (x.2 + S) (by omega) (by omega)).2
      have e : x.2 + (S : ℤ) - S = x.2 := by ring
      rw [e]; exact hd.2

theorem prod_erase_split {α M : Type*} [DecidableEq α] [CommMonoid M] (A B : Finset α) (z : α)
    (hz : z ∈ B) (f : α → M) :
    ∏ x ∈ A.erase z, f x = (∏ x ∈ A \ B, f x) * ∏ x ∈ (A ∩ B).erase z, f x := by
  rw [← Finset.prod_union]
  · congr 1
    ext x
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hB : x ∈ B
      · exact Or.inr ⟨h1, h2, hB⟩
      · exact Or.inl ⟨h2, hB⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨fun h => h2 (h ▸ hz), h1⟩
      · exact ⟨h1, h2⟩
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_inter] at hx hx'
    exact hx.2 hx'.2.2

/-- The linear factor `a t + b'` of the box formula (9.4). -/
noncomputable def linP (y : ℤ × ℤ) : ℚ[X] := C (y.1 : ℚ) * X + C (y.2 : ℚ)

theorem linP_ne_zero {y : ℤ × ℤ} (hy : y ≠ (0, 0)) : linP y ≠ 0 := by
  intro h
  have h1 : (linP y).coeff 1 = (y.1 : ℚ) := by
    rw [linP, coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C_ne_zero one_ne_zero, add_zero]
  have h0 : (linP y).coeff 0 = (y.2 : ℚ) := by
    rw [linP, coeff_add, coeff_C_mul, coeff_X_zero, mul_zero, zero_add, coeff_C_zero]
  rw [h, coeff_zero] at h1 h0
  exact hy (Prod.ext (by exact_mod_cast h1.symm) (by exact_mod_cast h0.symm))

theorem linP_eval {p p' : ℕ} (hp : 0 < p) (y : ℤ × ℤ) :
    (linP y).eval (-(p' : ℚ) / p) = (((p : ℤ) * y.2 - (p' : ℤ) * y.1 : ℤ) : ℚ) / p := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  simp only [linP, eval_add, eval_mul, eval_C, eval_X]
  push_cast
  field_simp
  ring

/-- The numerator of (9.4) after the shift `(a,b') ↦ (a+k,b'+m)`. -/
theorem boxNumPoly_shift (R S : ℤ) (k m : ℕ) :
    boxNumPoly R S k m = ∏ y ∈ (boxShift R S k m).erase (0, 0), linP y := by
  unfold boxNumPoly
  refine Finset.prod_nbij' (fun x => (x.1 + k, x.2 + m)) (fun y => (y.1 - k, y.2 - m))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_erase, boxSet, boxShift, Finset.mem_product, Finset.mem_Icc, ne_eq,
      Prod.ext_iff] at hx ⊢
    omega
  · intro y hy
    simp only [Finset.mem_erase, boxSet, boxShift, Finset.mem_product, Finset.mem_Icc, ne_eq,
      Prod.ext_iff] at hy ⊢
    omega
  · intro x _
    simp
  · intro y _
    simp
  · intro x _
    rfl

/-- Evaluation of a quotient of polynomials whose denominator does not vanish at the point. -/
theorem ratFunc_eval_div {K : Type*} [Field K] (N D : K[X]) (t : K) (hD : D.eval t ≠ 0) :
    (RatFunc.denom (algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D)).eval t ≠ 0 ∧
      RatFunc.eval (RingHom.id K) t
          (algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D) =
        N.eval t / D.eval t := by
  set x := algebraMap K[X] (RatFunc K) N / algebraMap K[X] (RatFunc K) D with hx
  have hd : (RatFunc.denom x).eval t ≠ 0 := by
    obtain ⟨q, hq⟩ := RatFunc.denom_div_dvd N D
    intro h0
    apply hD
    rw [hq, eval_mul, h0, zero_mul]
  have hD0 : D ≠ 0 := by
    rintro rfl
    simp at hD
  have hcross : RatFunc.num x * D = N * RatFunc.denom x := by
    have h1 := RatFunc.num_div_denom x
    rw [hx] at h1
    rw [← hx, div_eq_div_iff ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).2
        (RatFunc.denom_ne_zero x))
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective K)).2 hD0)] at h1
    apply RatFunc.algebraMap_injective K
    rw [map_mul, map_mul]
    exact h1
  refine ⟨hd, ?_⟩
  rw [RatFunc.eval, Polynomial.eval₂_id, Polynomial.eval₂_id, div_eq_div_iff hd hD, ← eval_mul,
    ← eval_mul, hcross]

theorem card_boxShift_sdiff (R S : ℤ) (k m : ℕ) :
    (boxShift R S k m \ boxSet R S).card = (boxSet R S \ boxShift R S k m).card := by
  have hc : (boxShift R S k m).card = (boxSet R S).card := by
    simp only [boxShift, boxSet, Finset.card_product, Int.card_Icc]
    congr 2 <;> ring
  have h1 := Finset.card_sdiff_add_card_inter (boxShift R S k m) (boxSet R S)
  have h2 := Finset.card_sdiff_add_card_inter (boxSet R S) (boxShift R S k m)
  rw [Finset.inter_comm] at h2
  omega

/-- The numerator of (9.4): the factors of `B₁ ∖ B₀` times the common factors. -/
theorem boxNumPoly_split {R S k m : ℕ} (hkR : k < R) (hmS : m < S) :
    boxNumPoly R S k m = (∏ y ∈ boxShift R S k m \ boxSet R S, linP y) *
      ∏ y ∈ (boxSet R S ∩ boxShift R S k m).erase (0, 0), linP y := by
  have h0B0 : ((0 : ℤ), (0 : ℤ)) ∈ boxSet R S := by
    simp only [boxSet, Finset.mem_product, Finset.mem_Icc]; omega
  rw [boxNumPoly_shift, prod_erase_split _ (boxSet R S) _ h0B0, Finset.inter_comm]

/-- The denominator of (9.4): the factors of `B₀ ∖ B₁` times the common factors. -/
theorem boxDenPoly_split {R S k m : ℕ} (hkR : k < R) (hmS : m < S) :
    boxDenPoly R S = (∏ y ∈ boxSet R S \ boxShift R S k m, linP y) *
      ∏ y ∈ (boxSet R S ∩ boxShift R S k m).erase (0, 0), linP y := by
  have h0B1 : ((0 : ℤ), (0 : ℤ)) ∈ boxShift R S k m := by
    simp only [boxShift, Finset.mem_product, Finset.mem_Icc]; omega
  rw [← prod_erase_split _ (boxShift R S k m) _ h0B1]
  rfl

theorem boxCommon_ne_zero (R S : ℤ) (k m : ℕ) :
    (∏ y ∈ (boxSet R S ∩ boxShift R S k m).erase (0, 0), linP y) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun y hy => linP_ne_zero (Finset.ne_of_mem_erase hy)

/-- `cMM` is the quotient of the values at `t = -p'/p` of the factors of `B₁ ∖ B₀` and of
`B₀ ∖ B₁`: the powers of `p⁻¹` cancel because `|B₁ ∖ B₀| = |B₀ ∖ B₁|` (l.2800–2803). -/
theorem cMM_eval {p p' : ℕ} (R S : ℤ) (k m : ℕ) (hp : 0 < p)
    (hne : ∀ x ∈ (boxShift R S k m \ boxSet R S) ∪ (boxSet R S \ boxShift R S k m),
      (p : ℤ) * x.2 - (p' : ℤ) * x.1 ≠ 0) :
    (∏ y ∈ boxSet R S \ boxShift R S k m, linP y).eval (-(p' : ℚ) / p) ≠ 0 ∧
      cMM p p' R S k m =
        (∏ y ∈ boxShift R S k m \ boxSet R S, linP y).eval (-(p' : ℚ) / p) /
          (∏ y ∈ boxSet R S \ boxShift R S k m, linP y).eval (-(p' : ℚ) / p) ∧
      cMM p p' R S k m ≠ 0 := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hevN : (∏ y ∈ boxShift R S k m \ boxSet R S, linP y).eval (-(p' : ℚ) / p) =
      ((∏ x ∈ boxShift R S k m \ boxSet R S, ((p : ℤ) * x.2 - (p' : ℤ) * x.1) : ℤ) : ℚ) /
        (p : ℚ) ^ (boxShift R S k m \ boxSet R S).card := by
    rw [eval_prod, Finset.prod_congr rfl fun y _ => linP_eval (p' := p') hp y,
      Finset.prod_div_distrib, Finset.prod_const, Int.cast_prod]
  have hevD : (∏ y ∈ boxSet R S \ boxShift R S k m, linP y).eval (-(p' : ℚ) / p) =
      ((∏ x ∈ boxSet R S \ boxShift R S k m, ((p : ℤ) * x.2 - (p' : ℤ) * x.1) : ℤ) : ℚ) /
        (p : ℚ) ^ (boxShift R S k m \ boxSet R S).card := by
    rw [eval_prod, Finset.prod_congr rfl fun y _ => linP_eval (p' := p') hp y,
      Finset.prod_div_distrib, Finset.prod_const, Int.cast_prod, card_boxShift_sdiff]
  have hPN : ((∏ x ∈ boxShift R S k m \ boxSet R S, ((p : ℤ) * x.2 - (p' : ℤ) * x.1) : ℤ) : ℚ)
      ≠ 0 := by
    rw [Int.cast_ne_zero, Finset.prod_ne_zero_iff]
    exact fun x hx => hne x (Finset.mem_union_left _ hx)
  have hPD : ((∏ x ∈ boxSet R S \ boxShift R S k m, ((p : ℤ) * x.2 - (p' : ℤ) * x.1) : ℤ) : ℚ)
      ≠ 0 := by
    rw [Int.cast_ne_zero, Finset.prod_ne_zero_iff]
    exact fun x hx => hne x (Finset.mem_union_right _ hx)
  refine ⟨?_, ?_, div_ne_zero hPN hPD⟩
  · rw [hevD]
    exact div_ne_zero hPD (pow_ne_zero _ hpq)
  · rw [hevN, hevD, div_div_div_cancel_right₀ (pow_ne_zero _ hpq)]
    rfl

/-- The value (12.1) of the box ratio at `t = -p'/p` (l.2800–2803). -/
theorem box_ratio_value {p p' R S k m : ℕ} (hp : 0 < p) (hkR : k < R) (hmS : m < S)
    (hne : ∀ x ∈ (boxShift R S k m \ boxSet R S) ∪ (boxSet R S \ boxShift R S k m),
      (p : ℤ) * x.2 - (p' : ℤ) * x.1 ≠ 0) :
    (boxRatio R S k m).denom.eval (-(p' : ℚ) / p) ≠ 0 ∧
      RatFunc.eval (RingHom.id ℚ) (-(p' : ℚ) / p) (boxRatio R S k m) = cMM p p' R S k m ∧
      cMM p p' R S k m ≠ 0 := by
  have hratio : boxRatio R S k m =
      algebraMap ℚ[X] (RatFunc ℚ) (∏ y ∈ boxShift R S k m \ boxSet R S, linP y) /
        algebraMap ℚ[X] (RatFunc ℚ) (∏ y ∈ boxSet R S \ boxShift R S k m, linP y) := by
    rw [boxRatio, boxNumPoly_split hkR hmS, boxDenPoly_split hkR hmS, map_mul, map_mul,
      mul_div_mul_right _ _
        ((map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).2 (boxCommon_ne_zero _ _ _ _))]
  obtain ⟨hDne, hc, hc0⟩ := cMM_eval (R : ℤ) (S : ℤ) k m hp hne
  obtain ⟨h1, h2⟩ := ratFunc_eval_div _ _ _ hDne
  rw [hratio]
  exact ⟨h1, by rw [h2, hc], hc0⟩

end Virasoro
