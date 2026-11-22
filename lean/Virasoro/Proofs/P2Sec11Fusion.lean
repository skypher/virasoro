import Virasoro.Proofs.P2Sec10FusRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 11.1 (exact intersection of primitive fusion and residue roots), paper.tex l.2295–2360
-/

namespace Virasoro

/-- For coprime `p, p'`: `p'x = py` gives `p ∣ x` and `p' ∣ y`. -/
theorem coprime_two_dvd {p p' : ℕ} (hcop : Nat.Coprime p p') {x y : ℤ}
    (h : (p' : ℤ) * x = p * y) : (p : ℤ) ∣ x ∧ (p' : ℤ) ∣ y := by
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  exact ⟨hc.dvd_of_dvd_mul_left ⟨y, by linear_combination h⟩,
    hc.symm.dvd_of_dvd_mul_left ⟨x, by linear_combination -h⟩⟩

/-- The arithmetic of the proof of Lemma 11.1 (l.2313–2359).  With `u_i = 2a_i+1`,
`v_i = 2c_i+1`, `u₁ ≤ 2r-1`, `u₂ ≤ 2(p-r)-1`, `v₁ ≤ 2s-1`, `v₂ ≤ 2(p'-s)-1` and signs `e_i`:
`p'u₁ - e₁pv₁ = ±(p'u₂ - e₂pv₂)` forces `u₁ = u₂`, `v₁ = v₂`, `e₁ = e₂`. -/
theorem fusion_arith {p p' r s : ℕ} (hcop : Nat.Coprime p p') (hr : r < p) (hs : s < p')
    {a1 a2 c1 c2 : ℕ} (ha1 : a1 < r) (ha2 : a2 < p - r) (hc1 : c1 < s) (hc2 : c2 < p' - s)
    {e1 e2 : ℤ} (he1 : e1 = 1 ∨ e1 = -1) (he2 : e2 = 1 ∨ e2 = -1)
    (h : (p' : ℤ) * (2 * a1 + 1) - p * (e1 * (2 * c1 + 1)) =
          p' * (2 * a2 + 1) - p * (e2 * (2 * c2 + 1)) ∨
        (p' : ℤ) * (2 * a1 + 1) - p * (e1 * (2 * c1 + 1)) =
          -(p' * (2 * a2 + 1) - p * (e2 * (2 * c2 + 1)))) :
    a1 = a2 ∧ c1 = c2 ∧ e1 = e2 := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp0' : (0 : ℤ) < p' := by exact_mod_cast (by omega : 0 < p')
  -- `2p ∣ u₁ - u₂` with `|u₁ - u₂| < 2p` (l.2318–2321)
  have diff : ∀ y : ℤ, (p' : ℤ) * ((a1 : ℤ) - a2) = p * y → a1 = a2 ∧ y = 0 := by
    intro y hy
    have h0 := Int.eq_zero_of_abs_lt_dvd (coprime_two_dvd hcop hy).1
      (abs_lt.2 ⟨by omega, by omega⟩)
    rw [h0, mul_zero] at hy
    exact ⟨by omega, by rcases mul_eq_zero.1 hy.symm with h | h <;> omega⟩
  -- `u₁ + u₂ < 2p` (l.2323–2326)
  have sumA : ∀ y : ℤ, (p' : ℤ) * ((a1 : ℤ) + a2 + 1) = p * y → False := by
    intro y hy
    have h0 := Int.eq_zero_of_abs_lt_dvd (coprime_two_dvd hcop hy).1
      (abs_lt.2 ⟨by omega, by omega⟩)
    omega
  -- `0 < v₁ + v₂ < 2p'` (l.2349–2351)
  have sumC : ∀ x : ℤ, (p' : ℤ) * x = p * ((c1 : ℤ) + c2 + 1) → False := by
    intro x hx
    have h0 := Int.eq_zero_of_abs_lt_dvd (coprime_two_dvd hcop hx).2
      (abs_lt.2 ⟨by omega, by omega⟩)
    omega
  rcases he1 with rfl | rfl <;> rcases he2 with rfl | rfl <;> rcases h with h | h
  · obtain ⟨h1, h2⟩ := diff ((c1 : ℤ) - c2) (by linarith)
    exact ⟨h1, by omega, rfl⟩
  · exact (sumA ((c1 : ℤ) + c2 + 1) (by linarith)).elim
  · exact (sumC ((a1 : ℤ) - a2) (by linarith)).elim
  · exact (sumA ((c1 : ℤ) - c2) (by linarith)).elim
  · exact (sumC ((a2 : ℤ) - a1) (by linarith)).elim
  · exact (sumA ((c2 : ℤ) - c1) (by linarith)).elim
  · obtain ⟨h1, h2⟩ := diff ((c2 : ℤ) - c1) (by linarith)
    exact ⟨h1, by omega, rfl⟩
  · -- both sides positive (l.2344–2345)
    exfalso
    have h1 : (0 : ℤ) < p' * (2 * a1 + 1) + p * (2 * c1 + 1) := by positivity
    have h2 : (0 : ℤ) < p' * (2 * a2 + 1) + p * (2 * c2 + 1) := by positivity
    linarith

theorem odd_of_mem_oddsBelow {n u : ℕ} (hu : u ∈ oddsBelow n) : ∃ a : ℕ, a < n ∧ u = 2 * a + 1 := by
  rw [mem_oddsBelow] at hu
  exact ⟨u / 2, by omega, by omega⟩

/-- The reflection `h_{r,s}(b⋆) = h_{p-r,p'-s}(b⋆)`. -/
theorem kacH_reflect {p p' r s : ℕ} {b : ℂ} (hp : 0 < p) (hp' : 0 < p')
    (hb : b ^ 2 = -(p' : ℂ) / p) (hr : r ≤ p) (hs : s ≤ p') :
    kacH (r : ℤ) (s : ℤ) b = kacH ((p - r : ℕ) : ℤ) ((p' - s : ℕ) : ℤ) b :=
  (kacH_eq_iff hp hp' hb _ _ _ _).2 (Or.inr (by
    rw [Nat.cast_sub hr, Nat.cast_sub hs]; ring))

/-- Paper label: lem:fusion-injective -/
theorem lem_fusion_injective : Stmt_lem_fusion_injective := by
  intro p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hsym := kacH_reflect hp hp' hb hr.le hs.le
  refine ⟨fun d => ?_, ?_, fun d => ?_⟩
  · -- (i), l.2313–2326
    have e1 := fusP_roots r s b d
    have e2 := fusP_roots (p - r) (p' - s) b d
    rw [← hsym] at e2
    rw [e1, e2]
    constructor
    · rintro ⟨⟨u1, hu1, v1, hv1, rfl⟩, ⟨u2, hu2, v2, hv2, h2⟩⟩
      obtain ⟨a1, ha1, rfl⟩ := odd_of_mem_oddsBelow hu1
      obtain ⟨c1, hc1, rfl⟩ := odd_of_mem_oddsBelow hv1
      obtain ⟨a2, ha2, rfl⟩ := odd_of_mem_oddsBelow hu2
      obtain ⟨c2, hc2, rfl⟩ := odd_of_mem_oddsBelow hv2
      have h3 := (kacH_eq_iff hp hp' hb _ _ _ _).1 h2
      push_cast at h3
      obtain ⟨rfl, rfl, -⟩ := fusion_arith hcop hr hs ha1 ha2 hc1 hc2 (Or.inl rfl) (Or.inl rfl)
        (by rcases h3 with h | h
            · left; linear_combination h
            · right; linear_combination h)
      exact ⟨a1, c1, lt_min ha1 ha2, lt_min hc1 hc2, by push_cast; rfl⟩
    · rintro ⟨k, m, hk, hm, rfl⟩
      rw [lt_min_iff] at hk hm
      refine ⟨⟨2 * k + 1, mem_oddsBelow.2 ⟨by omega, by omega⟩, 2 * m + 1,
          mem_oddsBelow.2 ⟨by omega, by omega⟩, by push_cast; rfl⟩,
        ⟨2 * k + 1, mem_oddsBelow.2 ⟨by omega, by omega⟩, 2 * m + 1,
          mem_oddsBelow.2 ⟨by omega, by omega⟩, by push_cast; rfl⟩⟩
  · -- (ii), l.2327–2329
    intro k m k' m' hk hm hk' hm' h
    rw [lt_min_iff] at hk hm hk' hm'
    have h3 := (kacH_eq_iff hp hp' hb _ _ _ _).1 h
    obtain ⟨h1, h2, -⟩ := fusion_arith hcop hr hs hk.1 hk'.2 hm.1 hm'.2 (Or.inl rfl) (Or.inl rfl)
      (by rcases h3 with h | h
          · left; linear_combination h
          · right; linear_combination h)
    exact ⟨h1, h2⟩
  · -- (iii), l.2331–2359
    rw [genP_roots, genP_roots]
    constructor
    · rintro ⟨⟨u1, hu1, v1, hv1, hd1⟩, ⟨u2, hu2, v2, hv2, hd2⟩⟩
      obtain ⟨a1, ha1, rfl⟩ := odd_of_mem_oddsBelow hu1
      obtain ⟨c1, hc1, rfl⟩ := odd_of_mem_oddsBelow hv1
      obtain ⟨a2, ha2, rfl⟩ := odd_of_mem_oddsBelow hu2
      obtain ⟨c2, hc2, rfl⟩ := odd_of_mem_oddsBelow hv2
      have key : ∀ e1 e2 : ℤ, e1 = 1 ∨ e1 = -1 → e2 = 1 ∨ e2 = -1 →
          kacH ((2 * a1 + 1 : ℕ) : ℤ) (e1 * ((2 * c1 + 1 : ℕ) : ℤ)) b =
            kacH ((2 * a2 + 1 : ℕ) : ℤ) (e2 * ((2 * c2 + 1 : ℕ) : ℤ)) b →
          a1 = a2 ∧ c1 = c2 ∧ e1 = e2 := by
        intro e1 e2 he1 he2 h
        have h3 := (kacH_eq_iff hp hp' hb _ _ _ _).1 h
        push_cast at h3
        exact fusion_arith hcop hr hs ha1 ha2 hc1 hc2 he1 he2
          (by rcases h3 with h | h
              · left; linear_combination h
              · right; linear_combination h)
      rcases hd1 with hd1 | hd1 <;> rcases hd2 with hd2 | hd2
      · obtain ⟨rfl, rfl, -⟩ := key 1 1 (Or.inl rfl) (Or.inl rfl)
          (by rw [one_mul, one_mul, ← hd1, ← hd2])
        exact ⟨a1, c1, lt_min ha1 ha2, lt_min hc1 hc2, Or.inl (by rw [hd1]; push_cast; rfl)⟩
      · have := (key 1 (-1) (Or.inl rfl) (Or.inr rfl)
          (by rw [one_mul, neg_one_mul, ← hd1, ← hd2])).2.2
        norm_num at this
      · have := (key (-1) 1 (Or.inr rfl) (Or.inl rfl)
          (by rw [one_mul, neg_one_mul, ← hd1, ← hd2])).2.2
        norm_num at this
      · obtain ⟨rfl, rfl, -⟩ := key (-1) (-1) (Or.inr rfl) (Or.inr rfl)
          (by rw [neg_one_mul, neg_one_mul, ← hd1, ← hd2])
        exact ⟨a1, c1, lt_min ha1 ha2, lt_min hc1 hc2, Or.inr (by rw [hd1]; push_cast; rfl)⟩
    · rintro ⟨k, m, hk, hm, hd⟩
      rw [lt_min_iff] at hk hm
      have hd' : d = kacH ((2 * k + 1 : ℕ) : ℤ) ((2 * m + 1 : ℕ) : ℤ) b ∨
          d = kacH ((2 * k + 1 : ℕ) : ℤ) (-((2 * m + 1 : ℕ) : ℤ)) b := by
        rcases hd with rfl | rfl
        · left; push_cast; rfl
        · right; push_cast; rfl
      exact ⟨⟨2 * k + 1, mem_oddsBelow.2 ⟨by omega, by omega⟩, 2 * m + 1,
          mem_oddsBelow.2 ⟨by omega, by omega⟩, hd'⟩,
        ⟨2 * k + 1, mem_oddsBelow.2 ⟨by omega, by omega⟩, 2 * m + 1,
          mem_oddsBelow.2 ⟨by omega, by omega⟩, hd'⟩⟩

example : Stmt_lem_fusion_injective := lem_fusion_injective

end Virasoro
