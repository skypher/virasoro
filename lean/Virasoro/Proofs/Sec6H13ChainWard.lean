import Virasoro.Proofs.Sec6H13ChainDeg

/-!
# Proposition 6.8(ii): the first `𝔰𝔩₂` identity for the primary field (paper.tex l.1337–1341)

`⟨v|L_1^{a'} V_d(1)|W⟩ = ∑_{m_L} C(a',m_L) ∏_{u<m_L}(d + h_v − h_W + a' − 1 − u)
⟨v|V_d(1) L_1^{a'−m_L}|W⟩` for `L_0`-eigenvectors `v`, `W`, by induction on the exponent.
In the pairing `T(u,w) = ⟨u|V_d(1)|w⟩` of `IsPrimaryPairing`, the left side is
`T(L_{−1}^{a'} v, W)`.
-/

namespace Virasoro.H13C

open Verma Finset

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h d : R}

theorem L0_Lm1 {u : Verma R c h} {hu : R} (h1 : L 0 u = hu • u) :
    L 0 (L (-1) u) = (hu + 1) • L (-1) u := by
  rw [L_L, h1, if_neg (by decide), add_zero, map_smul]
  have e : L (0 + -1) u = L (-1) u := rfl
  rw [e]
  push_cast
  module

theorem L0_L1 {W : Verma R c h} {hW : R} (h2 : L 0 W = hW • W) :
    L 0 (L 1 W) = (hW - 1) • L 1 W := by
  rw [L_L, h2, if_neg (by decide), add_zero, map_smul]
  have e : L (0 + 1) W = L 1 W := rfl
  rw [e]
  push_cast
  module

theorem L0_Lm1_pow {v : Verma R c h} {hv : R} (h1 : L 0 v = hv • v) (a : ℕ) :
    L 0 ((L (-1) ^ a) v) = (hv + (a : R)) • (L (-1) ^ a) v := by
  induction a with
  | zero =>
    rw [pow_zero, Module.End.one_apply, h1, Nat.cast_zero, add_zero]
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, L0_Lm1 ih]
    push_cast
    rw [add_assoc]

/-- The Ward identity for `L_{−1}` on `L_0`-eigenvectors. -/
theorem ward_one {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hT : IsPrimaryPairing d T)
    {u W : Verma R c h} {hu hW : R} (h1 : L 0 u = hu • u) (h2 : L 0 W = hW • W) :
    T (L (-1) u) W = T u (L 1 W) + (d + hu - hW) * T u W := by
  have h3 := hT.2 1 u W
  have e1 : T (hu • u) W = hu * T u W := by rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  have e2 : T u (hW • W) = hW * T u W := by rw [map_smul, smul_eq_mul]
  rw [h1, h2, e1, e2] at h3
  push_cast at h3
  linear_combination h3

/-- `⟨v|L_1^a V_d(1)|W⟩ = ∑_m C(a,m) ∏_{u<m}(d + h_v − h_W + a − 1 − u) ⟨v|V_d(1) L_1^{a−m}|W⟩`
(paper.tex l.1337–1341). -/
theorem ward_pow {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hT : IsPrimaryPairing d T)
    {v : Verma R c h} {hv : R} (h1 : L 0 v = hv • v) (a : ℕ) :
    ∀ (W : Verma R c h) (hW : R), L 0 W = hW • W →
      T ((L (-1) ^ a) v) W = ∑ m ∈ range (a + 1),
        (a.choose m : R) * (∏ u ∈ range m, (d + hv - hW + (a : R) - 1 - (u : R))) *
          T v ((L 1 ^ (a - m)) W) := by
  induction a with
  | zero =>
    intro W hW _
    simp
  | succ a ih =>
    intro W hW h2
    have hstep : T ((L (-1) ^ (a + 1)) v) W =
        T ((L (-1) ^ a) v) (L 1 W) + (d + (hv + (a : R)) - hW) * T ((L (-1) ^ a) v) W := by
      rw [pow_succ', Module.End.mul_apply]
      exact ward_one hT (L0_Lm1_pow h1 a) h2
    rw [hstep, ih (L 1 W) (hW - 1) (L0_L1 h2), ih W hW h2]
    obtain ⟨x, hx⟩ : ∃ x : R, x = d + hv - hW + (a : R) := ⟨_, rfl⟩
    obtain ⟨P, hP⟩ : ∃ P : ℕ → R, ∀ m, P m = ∏ u ∈ range m, (x - (u : R)) := ⟨_, fun _ => rfl⟩
    obtain ⟨g, hg⟩ : ∃ g : ℕ → R, ∀ m, g m = T v ((L 1 ^ (a + 1 - m)) W) := ⟨_, fun _ => rfl⟩
    have hS1 : ∑ m ∈ range (a + 1), (a.choose m : R) *
        (∏ u ∈ range m, (d + hv - (hW - 1) + (a : R) - 1 - (u : R))) *
          T v ((L 1 ^ (a - m)) (L 1 W)) = ∑ m ∈ range (a + 1), (a.choose m : R) * P m * g m := by
      refine sum_congr rfl fun m hm => ?_
      have hm' : m ≤ a := Nat.lt_succ_iff.1 (mem_range.1 hm)
      have e : (L 1 ^ (a - m)) (L 1 W) = (L 1 ^ (a + 1 - m)) W := by
        rw [Nat.succ_sub hm', pow_succ, Module.End.mul_apply]
      rw [hP, hg, e]
      congr 2
      exact prod_congr rfl fun u _ => by rw [hx]; ring
    have hS2 : (d + (hv + (a : R)) - hW) * ∑ m ∈ range (a + 1), (a.choose m : R) *
        (∏ u ∈ range m, (d + hv - hW + (a : R) - 1 - (u : R))) * T v ((L 1 ^ (a - m)) W) =
        ∑ m ∈ range (a + 1), (a.choose m : R) * P (m + 1) * g (m + 1) := by
      rw [mul_sum]
      refine sum_congr rfl fun m _ => ?_
      have e : a + 1 - (m + 1) = a - m := Nat.add_sub_add_right a 1 m
      have e2 : P (m + 1) = x * ∏ u ∈ range m, (d + hv - hW + (a : R) - 1 - (u : R)) := by
        rw [hP, prod_range_succ', Nat.cast_zero, sub_zero, mul_comm]
        congr 1
        exact prod_congr rfl fun u _ => by rw [hx]; push_cast; ring
      rw [hg, e, e2, hx]
      ring
    have hT3 : ∑ m ∈ range (a + 1 + 1), ((a + 1).choose m : R) *
        (∏ u ∈ range m, (d + hv - hW + ((a + 1 : ℕ) : R) - 1 - (u : R))) *
          T v ((L 1 ^ (a + 1 - m)) W) =
        ∑ m ∈ range (a + 1 + 1), ((a + 1).choose m : R) * P m * g m := by
      refine sum_congr rfl fun m _ => ?_
      rw [hP, hg]
      congr 2
      exact prod_congr rfl fun u _ => by rw [hx]; push_cast; ring
    have hA : ∑ m ∈ range (a + 1), (a.choose m : R) * P m * g m =
        ∑ m ∈ range (a + 1), (a.choose (m + 1) : R) * P (m + 1) * g (m + 1) + P 0 * g 0 := by
      rw [sum_range_succ', sum_range_succ _ a, Nat.choose_succ_self, Nat.cast_zero, zero_mul,
        zero_mul, add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    have hC : ∑ m ∈ range (a + 1), ((a + 1).choose (m + 1) : R) * P (m + 1) * g (m + 1) =
        ∑ m ∈ range (a + 1), (a.choose m : R) * P (m + 1) * g (m + 1) +
          ∑ m ∈ range (a + 1), (a.choose (m + 1) : R) * P (m + 1) * g (m + 1) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun m _ => ?_
      rw [Nat.choose_succ_succ, Nat.cast_add]
      ring
    rw [hS1, hS2, hT3, sum_range_succ' _ (a + 1), hC, hA, Nat.choose_zero_right, Nat.cast_one,
      one_mul]
    ring

end Virasoro.H13C
