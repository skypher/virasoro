import Virasoro.Proofs.Sec6TTCase1

/-!
# Proposition 6.9: the Taylor coefficients of `τ^±_k` at a root (paper.tex l.1466–1472)

`τ^±_k` is a product of one or two `𝒫_{R,S}`.  At a root `z` of total multiplicity `e`,
`τ = (d − z)^e Q` with `Q(z) = (−1)^e ∏ (d_x − z)` over the factors with `d_x ≠ z`; at `z = 0`
(`d_{p'−p} = 0`) the multiplicity is `k` (Proposition 6.7) and `[d^k]τ = Q(0)`.
-/

namespace Virasoro

namespace TT

open Polynomial Finset

/-- The factors `(R, S)` of `τ^ε_k` (paper.tex l.1437–1440). -/
def facs (p p' r s : ℕ) (ε : Bool) (k : ℕ) : List (ℕ × ℕ) :=
  if k % 2 = 1 then
    [if ε then (r + k / 2 * p, s + k / 2 * p') else ((k / 2 + 1) * p - r, (k / 2 + 1) * p' - s)]
  else [(r + (k / 2 - 1) * p, s + (k / 2 - 1) * p'),
    if ε then ((k - 1) * p + r, p' - s) else (p - r, (k - 1) * p' + s)]

/-- `∏_{(R,S) ∈ L} 𝒫_{R,S}`. -/
noncomputable def prodPQ (p p' : ℕ) (L : List (ℕ × ℕ)) : ℚ[X] :=
  (L.map fun RS => PQ p p' RS.1 RS.2).prod

theorem tauQ_eq_facs (p p' r s : ℕ) (ε : Bool) (k : ℕ) :
    tauQ p p' r s ε k = prodPQ p p' (facs p p' r s ε k) := by
  unfold tauQ facs prodPQ
  split_ifs <;> simp

/-- The number of factors `d_x − d` of `𝒫_{R,S}` with `d_x = z`. -/
def cnt (p p' : ℕ) (z : ℚ) (RS : ℕ × ℕ) : ℕ :=
  ((idx RS.1 RS.2).filter (fun i => dQ p p' (xv p p' i) = z)).card

/-- `∏ (d_x − z)` over the factors of `𝒫_{R,S}` with `d_x ≠ z`. -/
def cof (p p' : ℕ) (z : ℚ) (RS : ℕ × ℕ) : ℚ :=
  ∏ i ∈ (idx RS.1 RS.2).filter (fun i => ¬ dQ p p' (xv p p' i) = z), (dQ p p' (xv p p' i) - z)

/-- The cofactor polynomial of `𝒫_{R,S}` at `z`. -/
noncomputable def cofP (p p' : ℕ) (z : ℚ) (RS : ℕ × ℕ) : ℚ[X] :=
  C ((-1) ^ cnt p p' z RS) *
    ∏ i ∈ (idx RS.1 RS.2).filter (fun i => ¬ dQ p p' (xv p p' i) = z), (C (dQ p p' (xv p p' i)) - X)

theorem splitAt_cofP (p p' : ℕ) (z : ℚ) (RS : ℕ × ℕ) :
    SplitAt z (PQ p p' RS.1 RS.2) (cnt p p' z RS) (cofP p p' z RS) :=
  splitAt_PQ p p' z RS.1 RS.2

theorem eval_cofP (p p' : ℕ) (z : ℚ) (RS : ℕ × ℕ) :
    (cofP p p' z RS).eval z = (-1) ^ cnt p p' z RS * cof p p' z RS := by
  unfold cofP cof
  rw [eval_cofactor]

theorem splitAt_prodPQ (p p' : ℕ) (z : ℚ) (L : List (ℕ × ℕ)) :
    SplitAt z (prodPQ p p' L) (L.map (cnt p p' z)).sum (L.map (cofP p p' z)).prod := by
  induction L with
  | nil =>
    refine ⟨by simp [prodPQ], by simp⟩
  | cons RS L ih =>
    have h := (splitAt_cofP p p' z RS).mul ih
    simpa [prodPQ, List.map_cons, List.prod_cons, List.sum_cons] using h

theorem eval_cofP_prod (p p' : ℕ) (z : ℚ) (L : List (ℕ × ℕ)) :
    ((L.map (cofP p p' z)).prod).eval z =
      (-1) ^ (L.map (cnt p p' z)).sum * (L.map (cof p p' z)).prod := by
  induction L with
  | nil => simp
  | cons RS L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, eval_mul, ih, eval_cofP, pow_add]
    ring

/-- The lowest coefficient of a polynomial split at `0`. -/
theorem coeff_split0 {P Q : ℚ[X]} {e : ℕ} (h : SplitAt 0 P e Q) : P.coeff e = Q.eval 0 := by
  rw [h.1, map_zero, sub_zero, coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    coeff_zero_eq_eval_zero]

theorem split0_eq {P Q : ℚ[X]} {e k : ℕ} (h : SplitAt 0 P e Q) (hc0 : ∀ n < k, P.coeff n = 0)
    (hck : P.coeff k ≠ 0) : e = k := by
  rcases lt_trichotomy e k with hlt | heq | hgt
  · exact absurd ((coeff_split0 h).symm.trans (hc0 e hlt)) h.2
  · exact heq
  · exfalso
    apply hck
    rw [h.1, map_zero, sub_zero, coeff_X_pow_mul', if_neg (by omega)]

/-! ### Valuations of products -/

theorem padicValRat_prod {ℓ : ℕ} [Fact ℓ.Prime] {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) : padicValRat ℓ (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat ℓ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha, padicValRat.mul (hf a (mem_insert_self a s))
      (prod_ne_zero_iff.2 fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

theorem padicValRat_list_prod {ℓ : ℕ} [Fact ℓ.Prime] (L : List ℚ) (hL : ∀ x ∈ L, x ≠ 0) :
    padicValRat ℓ L.prod = (L.map (padicValRat ℓ)).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons, padicValRat.mul (hL x (by simp))
      (List.prod_ne_zero fun h => hL 0 (by simp [h]) rfl), ih fun y hy => hL y (by simp [hy])]

theorem cof_ne_zero (p p' : ℕ) (z : ℚ) (RS : ℕ × ℕ) : cof p p' z RS ≠ 0 := by
  unfold cof
  exact prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (mem_filter.1 hi).2

/-- `v_ℓ(4pp') = v_ℓ(p')` for an odd prime `ℓ ∤ p`. -/
theorem val_4pp {ℓ p p' : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hp : 0 < p) (hp' : 0 < p')
    (hℓp : ¬ ℓ ∣ p) :
    padicValRat ℓ (4 * (p : ℚ) * p') = (padicValNat ℓ p' : ℤ) := by
  have h4 : padicValRat ℓ (4 : ℚ) = 0 := by
    rw [show (4 : ℚ) = ((4 : ℕ) : ℚ) by norm_num, padicValRat.of_nat]
    have : ¬ ℓ ∣ 4 := by
      intro h
      have h2 : ℓ ∣ 2 ^ 2 := by norm_num; exact h
      exact hℓ2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1
        ((Fact.out : ℓ.Prime).dvd_of_dvd_pow h2))
    exact_mod_cast padicValNat.eq_zero_of_not_dvd this
  have hpv : padicValRat ℓ (p : ℚ) = 0 := by
    rw [padicValRat.of_nat]
    exact_mod_cast padicValNat.eq_zero_of_not_dvd hℓp
  rw [padicValRat.mul (by positivity) (by positivity), padicValRat.mul (by norm_num) (by positivity),
    h4, hpv, padicValRat.of_nat]
  ring

/-- `v_ℓ(d_x − d_y) = v_ℓ(x² − y²) − v_ℓ(p')`. -/
theorem val_dQ_sub {ℓ p p' : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hp : 0 < p) (hp' : 0 < p')
    (hℓp : ¬ ℓ ∣ p) {x y : ℤ} (hxy : x ^ 2 ≠ y ^ 2) :
    padicValRat ℓ (dQ p p' x - dQ p p' y) =
      (padicValInt ℓ (x ^ 2 - y ^ 2) : ℤ) - (padicValNat ℓ p' : ℤ) := by
  rw [dQ_sub hp hp', padicValRat.div (by exact_mod_cast sub_ne_zero.2 hxy) (by positivity),
    padicValRat.of_int, val_4pp hℓ2 hp hp' hℓp]

end TT

end Virasoro
