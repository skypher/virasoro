import Virasoro.Proofs.P2Sec11JointInt
import Virasoro.Proofs.P2Sec10OrbitArith

/-!
# Lemma 11.3 (joint regularity in `(b,Δ)`), paper.tex l.2499–2552

Last paragraph of the proof (l.2542–2551): a label `(R,S)` with `h_{R,S}(b⋆) = μ` in the orbit
has `p'R - pS = ±n_μ`; reducing modulo `p` and `p'` gives `R ≥ min(r,p-r)` and
`S ≥ min(s,p'-s)`, so `(R,S) ∉ 𝒦_N` and the denominator of `Stmt_sub_joint_denominator` does not
vanish at `(b⋆,μ)`.
-/

namespace Virasoro

open Polynomial

theorem ge_min_of_dvd {p r R : ℕ} (hr0 : 0 < r) (hr : r < p) (hR : 0 < R)
    (h : (p : ℤ) ∣ (R : ℤ) - r ∨ (p : ℤ) ∣ (R : ℤ) + r) : min r (p - r) ≤ R := by
  by_contra hlt
  have h1 : (R : ℤ) < r := by omega
  have h2 : (R : ℤ) + r < p := by omega
  have hR' : (0 : ℤ) < R := by omega
  have hp : (0 : ℤ) < p := by omega
  rcases h with ⟨t, ht⟩ | ⟨t, ht⟩
  · rcases le_or_gt 0 t with h0 | h0
    · have := mul_nonneg hp.le h0
      linarith
    · have : (p : ℤ) * t ≤ -p := by nlinarith
      linarith
  · rcases le_or_gt t 0 with h0 | h0
    · have : (p : ℤ) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp.le h0
      linarith
    · have : (p : ℤ) ≤ p * t := by nlinarith
      linarith

theorem momWt_eq {p p' : ℕ} (hp : 0 < p) (hp' : 0 < p') {n n' : ℤ}
    (h : momWt p p' n = momWt p p' n') : n = n' ∨ n = -n' := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  unfold momWt at h
  rw [div_left_inj' (by simp [hpc, hpc'] : (4 * (p : ℂ) * p') ≠ 0), sub_left_inj,
    sq_eq_sq_iff_eq_or_eq_neg] at h
  exact_mod_cast h

/-- Paper equation (10.5): `n_μ ≡ ±(p'r ± ps) (mod pp')`. -/
theorem nOrb_form (p p' r s : ℕ) (ε : Bool) (j : ℕ) : ∃ t σ₁ σ₂ : ℤ,
    (σ₁ = 1 ∨ σ₁ = -1) ∧ (σ₂ = 1 ∨ σ₂ = -1) ∧
      nOrb p p' r s ε j = t * p * p' + σ₁ * (p' * r) + σ₂ * (p * s) := by
  simp only [nOrb]
  split_ifs
  · exact ⟨j, 1, -1, Or.inl rfl, Or.inr rfl, by ring⟩
  · exact ⟨j, -1, 1, Or.inr rfl, Or.inl rfl, by ring⟩
  · exact ⟨j - 1, 1, 1, Or.inl rfl, Or.inl rfl, by ring⟩
  · exact ⟨j + 1, -1, -1, Or.inr rfl, Or.inr rfl, by ring⟩

/-- Paper.tex l.2542–2549: a positive label `(R,S)` with `h_{R,S}(b⋆)` in the orbit has
`R ≥ min(r,p-r)` and `S ≥ min(s,p'-s)`. -/
theorem label_ge_of_orbit {p p' r s : ℕ} {b : ℂ} (hp : 0 < p) (hp' : 0 < p')
    (hcop : Nat.Coprime p p') (hb : b ^ 2 = -(p' : ℂ) / p) (hr0 : 0 < r) (hr : r < p)
    (hs0 : 0 < s) (hs : s < p') {R S : ℕ} (hR : 0 < R) (hS : 0 < S) {μ : ℂ}
    (hμ : μ ∈ orbitSet p p' r s) (h : kacH R S b = μ) :
    min r (p - r) ≤ R ∧ min s (p' - s) ≤ S := by
  obtain ⟨ε, j, rfl⟩ := hμ
  rw [muOrb, kacH_momWt hp hp' hb] at h
  obtain ⟨t, σ₁, σ₂, h1, h2, hn⟩ := nOrb_form p p' r s ε j
  have hc : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have key : ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      (p' : ℤ) * R - p * S = e * (t * p * p' + σ₁ * (p' * r) + σ₂ * (p * s)) := by
    rcases momWt_eq hp hp' h with h' | h'
    · exact ⟨1, Or.inl rfl, by rw [h', hn]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h', hn]; ring⟩
  obtain ⟨e, he, hk⟩ := key
  have d1 : (p : ℤ) ∣ (R : ℤ) - e * σ₁ * r := by
    have : (p : ℤ) ∣ (p' : ℤ) * ((R : ℤ) - e * σ₁ * r) :=
      ⟨S + e * t * p' + e * σ₂ * s, by linear_combination hk⟩
    exact hc.dvd_of_dvd_mul_left this
  have d2 : (p' : ℤ) ∣ (S : ℤ) + e * σ₂ * s := by
    have : (p' : ℤ) ∣ (p : ℤ) * ((S : ℤ) + e * σ₂ * s) :=
      ⟨R - e * t * p - e * σ₁ * r, by linear_combination -hk⟩
    exact hc.symm.dvd_of_dvd_mul_left this
  refine ⟨ge_min_of_dvd hr0 hr hR ?_, ge_min_of_dvd hs0 hs hS ?_⟩
  · rcases he with rfl | rfl <;> rcases h1 with rfl | rfl
    · left; simpa using d1
    · right; simpa using d1
    · right; simpa using d1
    · left; simpa using d1
  · rcases he with rfl | rfl <;> rcases h2 with rfl | rfl
    · right; simpa using d2
    · left; simpa [sub_eq_add_neg] using d2
    · left; simpa [sub_eq_add_neg] using d2
    · right; simpa using d2

/-- Paper label: lem:joint-holomorphicity -/
theorem lem_joint_holomorphicity_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_lem_joint_holomorphicity := by
  classical
  intro p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs k m ε hk hm N μ hμ
  obtain ⟨e, P, hP⟩ := sub_joint_denominator hK hH k m ε N
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  let hpol : Label → ℂ[X] := fun a =>
    C (1 / 4 : ℂ) * ((X ^ 2 + 1) ^ 2 - (C (a.1 : ℂ) * X ^ 2 + C (a.2 : ℂ)) ^ 2)
  have hhpol : ∀ a, algebraMap ℂ[X] (RatFunc ℂ) (hpol a) =
      RatFunc.X ^ 2 * kacHL a (RatFunc.X : RatFunc ℂ) := by
    intro a
    have hX := RatFunc.X_ne_zero (K := ℂ)
    simp only [hpol, map_mul, map_sub, map_pow, map_add, map_one, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, kacHL, kacH, map_div₀, map_ofNat, map_natCast, Int.cast_natCast]
    field_simp
  have hhval : ∀ a, (hpol a).eval b = b ^ 2 * kacHL a b := by
    intro a
    simp only [hpol, eval_mul, eval_C, eval_sub, eval_pow, eval_add, eval_X, eval_one, kacHL,
      kacH, Int.cast_natCast]
    field_simp
  have hfac : ∀ a, (C (RatFunc.X ^ 2) * X - C (RatFunc.X ^ 2 * kacHL a (RatFunc.X : RatFunc ℂ)) :
      (RatFunc ℂ)[X]) = C (RatFunc.X ^ 2) * (X - C (kacHL a (RatFunc.X : RatFunc ℂ))) := by
    intro a
    rw [C_mul]
    ring
  refine ⟨P * C (X ^ (2 * (activeLabels k m N).card)),
    C (X ^ e) * ∏ a ∈ activeLabels k m N, (C (X ^ 2) * X - C (hpol a)), ?_, ?_⟩
  · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X, eval_pow, hhval]
    refine mul_ne_zero (pow_ne_zero _ hb0) (Finset.prod_ne_zero_iff.2 fun a ha => ?_)
    rw [← mul_sub]
    refine mul_ne_zero (pow_ne_zero _ hb0) (sub_ne_zero.2 fun hμa => ?_)
    rw [activeLabels, Finset.mem_filter] at ha
    obtain ⟨h1, h2, h3⟩ := label_pos ha.1
    have := label_ge_of_orbit (by omega) (by omega) hcop hb hr0 hr hs0 hs h1 h2 hμ hμa.symm
    omega
  · have hXp : ∀ n : ℕ, algebraMap ℂ[X] (RatFunc ℂ) (X ^ n) = RatFunc.X ^ n := fun n => by
      rw [map_pow, RatFunc.algebraMap_X]
    simp only [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_C,
      Polynomial.map_X, hXp, hhpol, hfac, Finset.prod_mul_distrib, Finset.prod_const]
    simp only [map_mul]
    rw [← hP]
    simp only [map_mul, map_pow, map_prod, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      activeLabels]
    ring

example (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_lem_joint_holomorphicity := lem_joint_holomorphicity_of_cited hK hH

end Virasoro
