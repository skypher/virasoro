import Virasoro.Proofs.P2Sec9Main
import Virasoro.Proofs.RegEvalK

/-!
# Corollary 9.4 (collision-free truncated recursion): the three obstructions
(paper.tex l.3123–3152)

For `d(b) = h_{1,2m+1}(b)`, `0 ≤ m < min(s,p'-s)`, and active labels `(R,S)` with `1 ≤ S ≤ m`
(so `2S ≤ 2m < p'`): (1) no factor `ab + b'b⁻¹` of the denominator of `𝒜_{R,S}` vanishes at
`b⋆`; (2) no two active poles collide; (3) no shifted weight `h_{R₁,-S₁}(b⋆)` hits an active
pole.  The dual case `d(b) = h_{2k+1,1}(b)` is the same statement for `(p',p,b⋆⁻¹)`
(`p ↔ p'` duality, l.3124).  The recursion identity at `b⋆` (l.3153–3157) is the sub-statement
`Stmt_sub_truncated_recursion`.
-/

namespace Virasoro

open Polynomial

section Arith

variable {p p' : ℕ} {b : ℂ}

/-- Obstruction 1 (l.3131–3136): at `t⋆ = -p'/p`, `ab + b'b⁻¹ = 0` requires `p' ∣ b'`. -/
theorem lin_ne_minimal (hp : 0 < p) (hp' : 0 < p') (hcop : Nat.Coprime p p')
    (hb : b ^ 2 = -(p' : ℂ) / p) (a c : ℤ) (hc : |c| < p') (h : a ≠ 0 ∨ c ≠ 0) :
    (a : ℂ) * b + (c : ℂ) * b⁻¹ ≠ 0 := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  intro h0
  have h1 : (a : ℂ) * b ^ 2 + c = 0 := by
    have e : (a : ℂ) * b ^ 2 + c = ((a : ℂ) * b + (c : ℂ) * b⁻¹) * b := by
      rw [add_mul, mul_assoc, mul_assoc, inv_mul_cancel₀ hb0]
      ring
    rw [e, h0, zero_mul]
  rw [hb] at h1
  have h2 : (c : ℂ) * p = a * p' := by
    field_simp at h1
    linear_combination h1
  have h3 : c * (p : ℤ) = a * p' := by exact_mod_cast h2
  have hcp : IsCoprime (p' : ℤ) (p : ℤ) := (Nat.isCoprime_iff_coprime.2 hcop).symm
  have hd : (p' : ℤ) ∣ c := hcp.dvd_of_dvd_mul_right ⟨a, by rw [h3]; ring⟩
  have hc0 : c = 0 := Int.eq_zero_of_abs_lt_dvd hd hc
  rw [hc0, zero_mul] at h3
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 h3.symm with h | h
    · exact h
    · exact absurd h (by exact_mod_cast hp'.ne')
  rcases h with h | h
  · exact h ha0
  · exact h hc0

/-- Obstruction 2 (l.3137–3142): no primary collisions among labels with `2S < p'`. -/
theorem no_primary_collision (hp : 0 < p) (hp' : 0 < p') (hcop : Nat.Coprime p p')
    (hb : b ^ 2 = -(p' : ℂ) / p) {R₁ S₁ R₂ S₂ : ℕ} (hR₁ : 0 < R₁) (hS₁ : 0 < S₁) (hR₂ : 0 < R₂)
    (hS₂ : 0 < S₂) (h1 : 2 * S₁ < p') (h2 : 2 * S₂ < p')
    (h : kacH (R₁ : ℤ) (S₁ : ℤ) b = kacH (R₂ : ℤ) (S₂ : ℤ) b) : R₁ = R₂ ∧ S₁ = S₂ := by
  have hcp : IsCoprime (p' : ℤ) (p : ℤ) := (Nat.isCoprime_iff_coprime.2 hcop).symm
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpz' : (p' : ℤ) ≠ 0 := by exact_mod_cast hp'.ne'
  rcases (kacH_eq_iff hp hp' hb _ _ _ _).1 h with e | e
  · have hd : (p' : ℤ) ∣ (S₁ : ℤ) - S₂ :=
      hcp.dvd_of_dvd_mul_left ⟨(R₁ : ℤ) - R₂, by linear_combination -e⟩
    have hS : (S₁ : ℤ) - S₂ = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨by omega, by omega⟩)
    have hR : (p' : ℤ) * ((R₁ : ℤ) - R₂) = 0 := by linear_combination e + (p : ℤ) * hS
    rcases mul_eq_zero.1 hR with h0 | h0
    · exact absurd h0 hpz'
    · exact ⟨by omega, by omega⟩
  · have hd : (p' : ℤ) ∣ (S₁ : ℤ) + S₂ :=
      hcp.dvd_of_dvd_mul_left ⟨(R₁ : ℤ) + R₂, by linear_combination -e⟩
    have hS : (S₁ : ℤ) + S₂ = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨by omega, by omega⟩)
    omega

/-- Obstruction 3 (l.3143–3150): no secondary collisions among labels with `2S < p'`. -/
theorem no_secondary_collision (hp : 0 < p) (hp' : 0 < p') (hcop : Nat.Coprime p p')
    (hb : b ^ 2 = -(p' : ℂ) / p) {R₁ S₁ R₂ S₂ : ℕ} (hR₁ : 0 < R₁) (hS₁ : 0 < S₁) (hR₂ : 0 < R₂)
    (hS₂ : 0 < S₂) (h1 : 2 * S₁ < p') (h2 : 2 * S₂ < p') :
    kacH (R₁ : ℤ) (-(S₁ : ℤ)) b ≠ kacH (R₂ : ℤ) (S₂ : ℤ) b := by
  have hcp : IsCoprime (p' : ℤ) (p : ℤ) := (Nat.isCoprime_iff_coprime.2 hcop).symm
  have hpz' : (p' : ℤ) ≠ 0 := by exact_mod_cast hp'.ne'
  intro h
  rcases (kacH_eq_iff hp hp' hb _ _ _ _).1 h with e | e
  · have hd : (p' : ℤ) ∣ (S₁ : ℤ) + S₂ :=
      hcp.dvd_of_dvd_mul_left ⟨(R₂ : ℤ) - R₁, by linear_combination e⟩
    have hS : (S₁ : ℤ) + S₂ = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨by omega, by omega⟩)
    omega
  · have hd : (p' : ℤ) ∣ (S₂ : ℤ) - S₁ :=
      hcp.dvd_of_dvd_mul_left ⟨(R₁ : ℤ) + R₂, by linear_combination -e⟩
    have hS : (S₂ : ℤ) - S₁ = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.2 ⟨by omega, by omega⟩)
    have hR : (p' : ℤ) * ((R₁ : ℤ) + R₂) = 0 := by linear_combination e + (p : ℤ) * hS
    rcases mul_eq_zero.1 hR with h0 | h0
    · exact absurd h0 hpz'
    · omega

/-- The `p ↔ p'` duality `h_{r,s}(b) = h_{s,r}(b⁻¹)` (l.3124). -/
theorem kacH_swap (u v : ℤ) (b : ℂ) : kacH u v b = kacH v u b⁻¹ := by
  simp only [kacH, inv_inv]
  ring

theorem dual_sq (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) :
    b⁻¹ ^ 2 = -(p : ℂ) / p' := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  rw [inv_pow, hb]
  field_simp

end Arith

/-- `ℛ_{R,S}(b,h_{u,v}(b)) ∈ ℂ(b)` is regular at a point `b₁ ≠ 0` where no factor of the
denominator of `𝒜_{R,S}` vanishes, with value `ℛ_{R,S}(b₁,h_{u,v}(b₁))`. -/
theorem evToK_genR {b : ℂ} (hb : b ≠ 0) (R S : ℕ) (u v : ℤ)
    (hlin : ∀ pq ∈ genAIndex R S, (pq.1 : ℂ) * b + (pq.2 : ℂ) * b⁻¹ ≠ 0) :
    EvToK b (genR R S (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ)))
      (genR R S b (kacH u v b)) := by
  have hX := evToK_X (K := ℂ) (b := b)
  have hXi := hX.inv hb
  have hlam : EvToK b (lamSq (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ)))
      (lamSq b (kacH u v b)) := by
    unfold lamSq
    exact ((hX.add hXi).pow 2).sub ((evToK_ofNat 4).mul (evToK_kacH hb u v))
  unfold genR genA genP
  refine EvToK.mul (EvToK.mul ((evToK_ofNat 2).inv two_ne_zero)
    (EvToK.prod _ fun pq hpq => EvToK.inv
      (((evToK_intCast pq.1).mul hX).add ((evToK_intCast pq.2).mul hXi)) (hlin pq hpq)))
    (EvToK.prod _ fun k _ => EvToK.prod _ fun l _ => EvToK.mul ?_ ?_)
  · exact EvToK.div (hlam.sub ((((evToK_natCast k).mul hX).add
      ((evToK_natCast l).mul hXi)).pow 2)) (evToK_ofNat 4) (by norm_num)
  · exact EvToK.div (hlam.sub ((((evToK_natCast k).mul hX).sub
      ((evToK_natCast l).mul hXi)).pow 2)) (evToK_ofNat 4) (by norm_num)

open Classical in
/-- The recursion identity of `CollisionFree` (its fourth clause). -/
def TruncRecAt (b : ℂ) (u v : ℤ) (act : Label → Prop) : Prop :=
  ∀ N : ℕ, 1 ≤ N →
    Hrat (kacC b) (kacH u v b) N =
      ∑ a ∈ (labels N).filter act,
        RatFunc.C (RatFunc.eval (RingHom.id ℂ) b
            (genR a.1 a.2 (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ)))) /
          (RatFunc.X - RatFunc.C (kacHL a b)) *
        RatFunc.C (RatFunc.eval (RingHom.id ℂ) (kacHL a b + (a.lvl : ℂ))
          (Hrat (kacC b) (kacH u v b) (N - a.lvl)))

/-- Last step of the proof of Corollary 9.4, paper.tex l.1975–1978 and l.3153–3157: since every
denominator of the truncated recursion is nonzero at `b = b⋆`, `H_N(c⋆,Δ,d(b⋆))` is given by the
recursion over the active labels with all data evaluated at `b⋆`.

Demand sheet: `MinimalSetting`; first case all `m < min(s,p'-s)`, active labels `S ≤ m`,
`d(b) = h_{1,2m+1}(b)`; dual case all `k < min(r,p-r)`, active labels `R ≤ k`,
`d(b) = h_{2k+1,1}(b)`; every `N ≥ 1`; the identity is the fourth clause of `CollisionFree`,
word for word. -/
def Stmt_sub_truncated_recursion : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    (∀ m : ℕ, m < min s (p' - s) → TruncRecAt b 1 (2 * (m : ℤ) + 1) (fun a => a.2 ≤ m)) ∧
    (∀ k : ℕ, k < min r (p - r) → TruncRecAt b (2 * (k : ℤ) + 1) 1 (fun a => a.1 ≤ k))

/-- Corollary 9.4 from its three obstructions (l.3123–3152) and the recursion identity at
`b⋆`. -/
theorem cor_collision_free_of_trunc (h : Stmt_sub_truncated_recursion) :
    Stmt_cor_collision_free := by
  intro p p' r s b hset
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  have hbi := dual_sq hp hp' hb
  refine ⟨fun m hm => ⟨?_, ?_, ?_, (h p p' r s b hset).1 m hm⟩,
    fun k hk => ⟨?_, ?_, ?_, (h p p' r s b hset).2 k hk⟩⟩
  · intro a h1 h2 hact
    refine (evToK_genR hb0 a.1 a.2 _ _ fun pq hpq => ?_).1
    rw [genAIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpq
    refine lin_ne_minimal hp hp' hcop hb _ _ (abs_lt.2 ⟨by omega, by omega⟩) ?_
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hpq.2.1 (Prod.ext hcon.1 hcon.2)
  · intro a a' h1 h2 hact h1' h2' hact' hne heq
    obtain ⟨e1, e2⟩ := no_primary_collision hp hp' hcop hb h1 h2 h1' h2' (by omega) (by omega) heq
    exact hne (Prod.ext e1 e2)
  · intro a a' h1 h2 hact h1' h2' hact'
    exact no_secondary_collision hp hp' hcop hb h1 h2 h1' h2' (by omega) (by omega)
  · intro a h1 h2 hact
    refine (evToK_genR hb0 a.1 a.2 _ _ fun pq hpq => ?_).1
    rw [genAIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpq
    have := lin_ne_minimal hp' hp hcop.symm hbi pq.2 pq.1 (abs_lt.2 ⟨by omega, by omega⟩) (by
      by_contra hcon
      rw [not_or, not_not, not_not] at hcon
      exact hpq.2.1 (Prod.ext hcon.2 hcon.1))
    rw [inv_inv] at this
    rwa [add_comm]
  · intro a a' h1 h2 hact h1' h2' hact' hne heq
    have heq' : kacH (a.2 : ℤ) (a.1 : ℤ) b⁻¹ = kacH (a'.2 : ℤ) (a'.1 : ℤ) b⁻¹ := by
      rw [← kacH_swap, ← kacH_swap]; exact heq
    obtain ⟨e1, e2⟩ := no_primary_collision hp' hp hcop.symm hbi h2 h1 h2' h1' (by omega)
      (by omega) heq'
    exact hne (Prod.ext e2 e1)
  · intro a a' h1 h2 hact h1' h2' hact' heq
    have hneg : kacH (-(a.2 : ℤ)) (a.1 : ℤ) b⁻¹ = kacH (a.2 : ℤ) (-(a.1 : ℤ)) b⁻¹ := by
      simp only [kacH]; push_cast; ring
    refine no_secondary_collision hp' hp hcop.symm hbi h2 h1 h2' h1' (by omega) (by omega) ?_
    rw [← hneg, ← kacH_swap, ← kacH_swap]
    exact heq

example (h : Stmt_sub_truncated_recursion) : Stmt_cor_collision_free :=
  cor_collision_free_of_trunc h

end Virasoro
