import Virasoro.Sphere.Proofs.Sec5PiEven
import Virasoro.Sphere.Proofs.Sec5PiZeros

/-!
# Sphere paper Lemma 5.2 (`lem:pi-factorization`)

`sphere/paper.tex` l.1499–1548.  Parts (i), (ii) are `pi_odd`, `pi_even`.  For (iii), in both
parities `R^±_k p' + S^±_k p = m^±_k`, and for even `k` the factor `P_{r,s}` has its zeros on
hyperplanes with `|c| ≤ n₁ - p' - p ≤ m^±_k - p' - p`.
-/

namespace Virasoro.Sphere

open Verma

theorem zeros_of_fus {p p' : ℕ} {b : ℂ} (hp : 0 < p) (hp' : 0 < p')
    (hb : b ^ 2 = -(p' : ℂ) / p) {R S : ℕ} (hR : 0 < R) (hS : 0 < S) (aa ab π Q : ℂ) (M : ℤ)
    (hM : (R : ℤ) * p' + S * p - p' - p = M)
    (hπ : π = Q * fusP R S b (wtOf p p' aa) (wtOf p p' ab))
    (hQ : Q = 0 → ∃ c₀ : ℤ, |c₀| ≤ M ∧ (aa + ab = (c₀ : ℂ) ∨ aa - ab = (c₀ : ℂ))) :
    (π = 0 → ∃ c₀ : ℤ, |c₀| ≤ M ∧ (aa + ab = (c₀ : ℂ) ∨ aa - ab = (c₀ : ℂ))) ∧
      ((aa - ab = (M : ℂ) ∨ aa - ab = -(M : ℂ)) → π = 0) := by
  subst hM
  refine ⟨fun h0 => ?_, fun h => ?_⟩
  · rw [hπ] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact hQ h
    · exact fusP_zero_bound hp hp' hb hR hS aa ab h
  · rw [hπ, fusP_zero_of_extremal hp hp' hb hR hS aa ab h, mul_zero]

/-- Lemma 5.2 of the sphere paper, from Proposition 4.3 (through its cited inputs) and the
cited uniqueness of singular vectors.

Paper label: lem:pi-factorization -/
theorem lem_pi_factorization_of_cited (hH : Cited_HJSNormalizations)
    (hF : Cited_SphereFusionPolynomial) (hU : Cited_SingularUnique) :
    Stmt_lem_pi_factorization := by
  intro p p' r s b hset k ε hk x hx1 hx
  refine ⟨fun ho Δa Δb => pi_odd hH hF hU hset ε ho x hx1 hx Δa Δb,
    fun he Δa Δb => pi_even hH hF hU hset ε hk he x hx1 hx Δa Δb, ?_⟩
  intro aa ab
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hp0 : 0 < p := by omega
  have hp'0 : 0 < p' := by omega
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
  have hp'z : (0 : ℤ) < p' := by exact_mod_cast hp'0
  show (piScalar (kacH r s b) x (wtOf p p' aa) (wtOf p p' ab) = 0 →
      ∃ c₀ : ℤ, |c₀| ≤ nOrb p p' r s ε k - p' - p ∧
        (aa + ab = (c₀ : ℂ) ∨ aa - ab = (c₀ : ℂ))) ∧
    ((aa - ab = ((nOrb p p' r s ε k - p' - p : ℤ) : ℂ) ∨
        aa - ab = -((nOrb p p' r s ε k - p' - p : ℤ) : ℂ)) →
      piScalar (kacH r s b) x (wtOf p p' aa) (wtOf p p' ab) = 0)
  have hpj : p ≤ (k / 2 + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
  have hpj' : p' ≤ (k / 2 + 1) * p' := Nat.le_mul_of_pos_left _ (by omega)
  rcases Nat.mod_two_eq_zero_or_one k with he | ho
  · have hkj : (k : ℤ) = 2 * ((k / 2 : ℕ) : ℤ) := by omega
    have hj : 1 ≤ k / 2 := by omega
    have h1 : r < k / 2 * p := by
      have : p ≤ k / 2 * p := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have h2 : s < k / 2 * p' := by
      have : p' ≤ k / 2 * p' := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have h1z : (r : ℤ) < ((k / 2 : ℕ) : ℤ) * p := by exact_mod_cast h1
    have h2z : (s : ℤ) < ((k / 2 : ℕ) : ℤ) * p' := by exact_mod_cast h2
    cases ε with
    | true =>
      have e : nOrb p p' r s true k = (k : ℤ) * p * p' + ((p' : ℤ) * r - p * s) := by
        simp [nOrb, he]
      have q1 : (0 : ℤ) ≤ (((k / 2 : ℕ) : ℤ) * p' - s) * p :=
        mul_nonneg (by linarith) hpz.le
      refine zeros_of_fus hp0 hp'0 hb (R := r + k / 2 * p) (S := k / 2 * p' - s) (by omega)
        (by omega) aa ab _ (fusP r s b (wtOf p p' aa) (wtOf p p' ab)) _ ?_ ?_ ?_
      · rw [e, hkj]
        push_cast [Nat.cast_sub h2.le]
        ring
      · rw [pi_even hH hF hU hset' true hk he x hx1 hx, if_pos rfl]
      · intro h0
        obtain ⟨c₀, hc, hor⟩ := fusP_zero_bound hp0 hp'0 hb hr hs aa ab h0
        refine ⟨c₀, le_trans hc ?_, hor⟩
        rw [e, hkj]
        nlinarith [q1]
    | false =>
      have e : nOrb p p' r s false k = (k : ℤ) * p * p' - ((p' : ℤ) * r - p * s) := by
        simp [nOrb, he]
      have q1 : (0 : ℤ) ≤ (((k / 2 : ℕ) : ℤ) * p - r) * p' :=
        mul_nonneg (by linarith) hp'z.le
      refine zeros_of_fus hp0 hp'0 hb (R := k / 2 * p - r) (S := k / 2 * p' + s) (by omega)
        (by omega) aa ab _ (fusP r s b (wtOf p p' aa) (wtOf p p' ab)) _ ?_ ?_ ?_
      · rw [e, hkj]
        push_cast [Nat.cast_sub h1.le]
        ring
      · rw [pi_even hH hF hU hset' false hk he x hx1 hx, if_neg (by simp)]
      · intro h0
        obtain ⟨c₀, hc, hor⟩ := fusP_zero_bound hp0 hp'0 hb hr hs aa ab h0
        refine ⟨c₀, le_trans hc ?_, hor⟩
        rw [e, hkj]
        nlinarith [q1]
  · have hkj : (k : ℤ) = 2 * ((k / 2 : ℕ) : ℤ) + 1 := by omega
    have ho' : ¬ k % 2 = 0 := by omega
    cases ε with
    | true =>
      have e : nOrb p p' r s true k = ((k : ℤ) - 1) * p * p' + ((p' : ℤ) * r + p * s) := by
        simp [nOrb, ho]
      refine zeros_of_fus hp0 hp'0 hb (R := r + k / 2 * p) (S := s + k / 2 * p') (by omega)
        (by omega) aa ab _ 1 _ ?_ ?_ fun h0 => absurd h0 one_ne_zero
      · rw [e, hkj]
        push_cast
        ring
      · rw [pi_odd hH hF hU hset' true ho x hx1 hx, if_pos rfl, one_mul]
    | false =>
      have e : nOrb p p' r s false k = ((k : ℤ) + 1) * p * p' - ((p' : ℤ) * r + p * s) := by
        simp [nOrb, ho]
      refine zeros_of_fus hp0 hp'0 hb (R := (k / 2 + 1) * p - r) (S := (k / 2 + 1) * p' - s)
        (by omega) (by omega) aa ab _ 1 _ ?_ ?_ fun h0 => absurd h0 one_ne_zero
      · rw [e, hkj]
        push_cast [Nat.cast_sub (show r ≤ (k / 2 + 1) * p by omega),
          Nat.cast_sub (show s ≤ (k / 2 + 1) * p' by omega)]
        ring
      · rw [pi_odd hH hF hU hset' false ho x hx1 hx, if_neg (by simp), one_mul]

example (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) : Stmt_lem_pi_factorization :=
  lem_pi_factorization_of_cited hH hF hU

end Virasoro.Sphere
