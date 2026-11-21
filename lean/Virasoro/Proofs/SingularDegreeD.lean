import Virasoro.Proofs.Naturality
import Virasoro.Proofs.PBWIndep
import Virasoro.Proofs.PBWBridge
import Virasoro.Statements.Sec5c

/-!
# Degree in the external weight of the torus matrix entries (second half of Lemma 5.7)

Over `𝔽[X]` with external weight `d = X`: the entry `⟨h|L_Y V_d(1) L_{-w}|h⟩` has degree at most
`ℓ(Y) + ℓ(w)` in `d`, and its coefficient of `d^{ℓ(Y)+ℓ(w)}` is `∏ y_i ∏ w_j`.  Each Ward
commutator contributes a factor of degree one in `d` with leading coefficient the mode index;
every other step removes a mode without producing a factor `d`.
-/

namespace Virasoro

open Polynomial

section Length

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- A nonnegative mode does not increase the length of a word; a negative mode adds one letter. -/
theorem actWord_length (c h : R) : ∀ (w : List ℕ) (k : ℤ), ∀ t ∈ actWord c h k w,
    t.1.length ≤ w.length + (if k < 0 then 1 else 0)
  | [], k => by
    intro t ht
    unfold actWord at ht
    split_ifs at ht with h1 h2 <;> simp_all
  | y :: w, k => by
    intro t ht
    unfold actWord at ht
    split_ifs at ht with h1 h2 h3
    · simp_all
    · simp_all
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at ht
      rcases ht with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | rfl
      · have := actWord_length c h w k u hu
        simp only [h1, if_false, add_zero] at this
        simp only [h1, if_false, add_zero, List.length_cons]
        omega
      · have := actWord_length c h w (k - y) u hu
        simp only [h1, if_false, add_zero, List.length_cons]
        split_ifs at this <;> omega
      · exact (Nat.le_succ _).trans (Nat.le_add_right _ _)
    · simp only [List.mem_append, List.mem_map, List.not_mem_nil, or_false] at ht
      rcases ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · have := actWord_length c h w k u hu
        simp only [h1, if_false, add_zero] at this
        simp only [h1, if_false, add_zero, List.length_cons]
        omega
      · have := actWord_length c h w (k - y) u hu
        simp only [h1, if_false, add_zero, List.length_cons]
        split_ifs at this <;> omega

end Length

section Degree

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽] (c₀ h₀ : 𝔽)

/-- The word product `∏ w_j` as an element of `𝔽`. -/
def wprod (w : List ℕ) : 𝔽 := ((w.prod : ℕ) : 𝔽)

theorem lin_mul_bound {q p : 𝔽[X]} {n : ℕ} (hq : q.natDegree ≤ 1) (hp : p.natDegree ≤ n) :
    (q * p).natDegree ≤ n + 1 ∧ (q * p).coeff (n + 1) = q.coeff 1 * p.coeff n := by
  refine ⟨(natDegree_mul_le).trans (by omega), ?_⟩
  rw [add_comm n 1]
  exact coeff_mul_add_eq_of_natDegree_le hq hp

theorem natDegree_linear (a : 𝔽) (m : ℕ) :
    (C a + (m : 𝔽[X]) * X).natDegree ≤ 1 ∧ (C a + (m : 𝔽[X]) * X).coeff 1 = (m : 𝔽) := by
  constructor
  · refine natDegree_add_le_of_degree_le (by simp) ?_
    rw [← C_eq_natCast]
    exact (natDegree_C_mul_le _ _).trans natDegree_X_le
  · rw [← C_eq_natCast]
    simp

/-- `⟨h|V_d(1) L_{-w}|h⟩` has degree at most `ℓ(w)` in `d` with top coefficient `∏ w_j`. -/
theorem phi_degree_d : ∀ w : List ℕ,
    (phi (X : 𝔽[X]) w).natDegree ≤ w.length ∧ (phi (X : 𝔽[X]) w).coeff w.length = wprod w
  | [] => by simp [phi, wprod]
  | m :: w => by
    obtain ⟨h1, h2⟩ := phi_degree_d w
    have hq := natDegree_linear (((w.sum : ℕ) : 𝔽)) m
    have := lin_mul_bound hq.1 h1
    rw [phi, ← C_eq_natCast (w.sum)]
    refine ⟨by simpa using this.1, ?_⟩
    rw [List.length_cons, this.2, hq.2, h2]
    simp [wprod, Nat.cast_mul]

/-- `⟨h|L_Y V_d(1) L_{-w}|h⟩` has degree at most `ℓ(Y) + ℓ(w)` in `d`, with coefficient
`∏ y_i ∏ w_j` of `d^{ℓ(Y)+ℓ(w)}`. -/
theorem torusWord_degree_d : ∀ (Y w : List ℕ),
    (torusWord (C c₀) (C h₀) (X : 𝔽[X]) Y w).natDegree ≤ Y.length + w.length ∧
    (torusWord (C c₀) (C h₀) (X : 𝔽[X]) Y w).coeff (Y.length + w.length) = wprod Y * wprod w
  | [], w => by
    obtain ⟨h1, h2⟩ := phi_degree_d (𝔽 := 𝔽) w
    simp only [torusWord, List.length_nil, zero_add]
    exact ⟨h1, by rw [h2]; simp [wprod]⟩
  | y :: Y, w => by
    obtain ⟨h1, h2⟩ := torusWord_degree_d Y w
    have hS : ((actWord (C c₀ : 𝔽[X]) (C h₀) (y : ℤ) w).map fun t =>
        t.2 * torusWord (C c₀) (C h₀) (X : 𝔽[X]) Y t.1).sum.natDegree ≤ Y.length + w.length := by
      refine natDegree_list_sum_le_of fun p hp => ?_
      rw [List.mem_map] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      have hlen := actWord_length (C c₀ : 𝔽[X]) (C h₀) w (y : ℤ) t ht
      have hneg : ¬ ((y : ℤ) < 0) := by omega
      simp only [hneg, if_false, add_zero] at hlen
      rw [actWord_map (C : 𝔽 →+* 𝔽[X])] at ht
      simp only [mapSt, List.mem_map] at ht
      obtain ⟨u, _, hu⟩ := ht
      have ht2 : t.2 = C u.2 := by rw [← hu]
      rw [ht2]
      refine (natDegree_C_mul_le _ _).trans ?_
      exact (torusWord_degree_d Y t.1).1.trans (by omega)
    have hq : (((Y.sum : ℕ) : 𝔽[X]) - ((w.sum : ℕ) : 𝔽[X]) + (y : 𝔽[X]) * X) =
        C (((Y.sum : ℕ) : 𝔽) - ((w.sum : ℕ) : 𝔽)) + (y : 𝔽[X]) * X := by
      simp only [map_sub, map_natCast]
    have hlin := natDegree_linear (((Y.sum : ℕ) : 𝔽) - ((w.sum : ℕ) : 𝔽)) y
    have hmul := lin_mul_bound hlin.1 h1
    rw [torusWord, hq]
    have hlen : (y :: Y).length + w.length = Y.length + w.length + 1 := by
      simp only [List.length_cons]; omega
    rw [hlen]
    refine ⟨natDegree_add_le_of_degree_le (hS.trans (by omega)) hmul.1, ?_⟩
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt (by omega), zero_add, hmul.2, hlin.2, h2]
    simp only [wprod, List.prod_cons, Nat.cast_mul]
    ring

end Degree

end Virasoro
