import Mathlib.NumberTheory.Bernoulli
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Proposition 6.8(ii): polynomials in the level (paper.tex l.1293–1304, l.1350–1353)

"`g(M)` is a polynomial in `M` of degree at most `D`, valid for all `M ≥ 0`" (`PolyDeg`), its
closure under sums, products, the shift `M ↦ M(M−1)⋯(M−s+1) g(M−s)` (l.1300–1302), and sums
`∑_{u<M}` (Faulhaber's formula); families of power series in `t` whose `tⁿ`-coefficients are such
polynomials of degree at most `s·n − e` (`PD`); the elementary symmetric polynomials of such a
family through Newton's identities (l.1296–1299, l.1352).
-/

namespace Virasoro.H13D

open Polynomial

/-- `g(M)` is a polynomial in `M` of degree at most `D` for all `M ≥ 0` (the zero polynomial when
`D < 0`). -/
def PolyDeg (g : ℕ → ℚ) (D : ℤ) : Prop :=
  ∃ f : ℚ[X], (∀ n : ℕ, D < n → f.coeff n = 0) ∧ ∀ M : ℕ, g M = f.eval (M : ℚ)

theorem PolyDeg.congr {g g' : ℕ → ℚ} {D : ℤ} (h : PolyDeg g D) (hg : ∀ M, g' M = g M) :
    PolyDeg g' D :=
  let ⟨f, h1, h2⟩ := h
  ⟨f, h1, fun M => (hg M).trans (h2 M)⟩

theorem PolyDeg.mono {g : ℕ → ℚ} {D D' : ℤ} (h : PolyDeg g D) (hD : D ≤ D') : PolyDeg g D' :=
  let ⟨f, h1, h2⟩ := h
  ⟨f, fun n hn => h1 n (lt_of_le_of_lt hD hn), h2⟩

theorem polyDeg_zero (D : ℤ) : PolyDeg (fun _ => 0) D :=
  ⟨0, fun _ _ => coeff_zero _, fun _ => by simp⟩

theorem PolyDeg.eq_zero {g : ℕ → ℚ} {D : ℤ} (h : PolyDeg g D) (hD : D < 0) (M : ℕ) : g M = 0 := by
  obtain ⟨f, h1, h2⟩ := h
  have hf : f = 0 := by
    ext n
    rw [coeff_zero]
    exact h1 n (by omega)
  rw [h2, hf, eval_zero]

theorem polyDeg_const (c : ℚ) : PolyDeg (fun _ => c) 0 :=
  ⟨C c, fun n hn => by rw [coeff_C, if_neg (by omega)], fun _ => by simp⟩

theorem PolyDeg.add {g g' : ℕ → ℚ} {D : ℤ} (h : PolyDeg g D) (h' : PolyDeg g' D) :
    PolyDeg (fun M => g M + g' M) D := by
  obtain ⟨f, h1, h2⟩ := h
  obtain ⟨f', h1', h2'⟩ := h'
  exact ⟨f + f', fun n hn => by rw [coeff_add, h1 n hn, h1' n hn, add_zero],
    fun M => by beta_reduce; rw [h2, h2', eval_add]⟩

theorem PolyDeg.sum {ι : Type*} (s : Finset ι) {g : ι → ℕ → ℚ} {D : ℤ}
    (h : ∀ a ∈ s, PolyDeg (g a) D) : PolyDeg (fun M => ∑ a ∈ s, g a M) D := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (polyDeg_zero D).congr fun M => Finset.sum_empty
  | insert a s ha ih =>
    have h3 := (h a (Finset.mem_insert_self a s)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
    exact h3.congr fun M => Finset.sum_insert ha

theorem PolyDeg.mul {g g' : ℕ → ℚ} {D D' : ℤ} (h : PolyDeg g D) (h' : PolyDeg g' D') :
    PolyDeg (fun M => g M * g' M) (D + D') := by
  obtain ⟨f, h1, h2⟩ := h
  obtain ⟨f', h1', h2'⟩ := h'
  refine ⟨f * f', fun n hn => ?_, fun M => by beta_reduce; rw [h2, h2', eval_mul]⟩
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.mem_antidiagonal.1 hp
  by_cases ha : D < p.1
  · rw [h1 _ ha, zero_mul]
  · rw [h1' p.2 (by omega), mul_zero]

theorem PolyDeg.const_mul {g : ℕ → ℚ} {D : ℤ} (c : ℚ) (h : PolyDeg g D) :
    PolyDeg (fun M => c * g M) D := by
  have h3 := (polyDeg_const c).mul h
  rwa [zero_add] at h3

/-! ### Faulhaber's formula -/

/-- The polynomial `F_n` with `F_n(M) = ∑_{k<M} kⁿ`. -/
noncomputable def faul (n : ℕ) : ℚ[X] :=
  ∑ i ∈ Finset.range (n + 1), C (bernoulli i * ((n + 1).choose i) / (n + 1)) * X ^ (n + 1 - i)

theorem faul_eval (n M : ℕ) : (faul n).eval (M : ℚ) = ∑ k ∈ Finset.range M, (k : ℚ) ^ n := by
  rw [sum_range_pow, faul, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem faul_coeff (n k : ℕ) (hk : n + 1 < k) : (faul n).coeff k = 0 := by
  rw [faul, finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero]

/-- Faulhaber: `∑_{u<M} h(u)` is a polynomial in `M` of degree one more. -/
theorem PolyDeg.sum_range {h : ℕ → ℚ} {D : ℤ} (hh : PolyDeg h D) :
    PolyDeg (fun M => ∑ u ∈ Finset.range M, h u) (D + 1) := by
  obtain ⟨f, h1, h2⟩ := hh
  refine ⟨∑ n ∈ f.support, C (f.coeff n) * faul n, fun k hk => ?_, fun M => ?_⟩
  · rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [coeff_C_mul]
    by_cases hD : D < n
    · rw [h1 n hD, zero_mul]
    · rw [faul_coeff n k (by omega), mul_zero]
  · have e1 : ∀ u : ℕ, h u = ∑ n ∈ f.support, f.coeff n * (u : ℚ) ^ n := fun u => by
      rw [h2, eval_eq_sum, Polynomial.sum_def]
    beta_reduce
    rw [eval_finsetSum, Finset.sum_congr rfl fun u _ => e1 u, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [eval_mul, eval_C, faul_eval, Finset.mul_sum]

/-- `M(M−1)⋯(M−s+1) g(M−s)` is a polynomial of degree at most `D + s`; the falling factorial
vanishes for `0 ≤ M < s` (paper.tex l.1300–1302). -/
theorem PolyDeg.shift {g : ℕ → ℚ} {D : ℤ} (h : PolyDeg g D) (s : ℕ) :
    PolyDeg (fun M => (M.descFactorial s : ℚ) * g (M - s)) (D + s) := by
  obtain ⟨f, h1, h2⟩ := h
  refine ⟨descPochhammer ℚ s * f.comp (X - C (s : ℚ)), fun n hn => ?_, fun M => ?_⟩
  · by_cases hf : f = 0
    · simp [hf]
    have hfd : (f.natDegree : ℤ) ≤ D := by
      by_contra hc
      exact (leadingCoeff_ne_zero.2 hf) (h1 _ (by omega))
    apply coeff_eq_zero_of_natDegree_lt
    have ha : (descPochhammer ℚ s).natDegree ≤ s := (descPochhammer_natDegree ℚ s).le
    have hb : (f.comp (X - C (s : ℚ))).natDegree ≤ f.natDegree :=
      natDegree_comp_le.trans
        ((Nat.mul_le_mul_left _ (natDegree_X_sub_C_le _)).trans (by rw [mul_one]))
    have h3 := natDegree_mul_le (p := descPochhammer ℚ s) (q := f.comp (X - C (s : ℚ)))
    omega
  · rw [eval_mul, eval_comp, eval_sub, eval_X, eval_C, descPochhammer_eval_eq_descFactorial]
    beta_reduce
    by_cases hM : s ≤ M
    · rw [h2, Nat.cast_sub hM]
    · have h0 : M.descFactorial s = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      rw [h0, Nat.cast_zero, zero_mul, zero_mul]

/-! ### Families of power series in `t` -/

/-- `[tⁿ] G_M` is a polynomial in `M` of degree at most `s·n − e`, for all `M ≥ 0`. -/
def PD (G : ℕ → PowerSeries ℚ) (s e : ℤ) : Prop :=
  ∀ n : ℕ, PolyDeg (fun M => PowerSeries.coeff n (G M)) (s * n - e)

theorem PD.mul {G G' : ℕ → PowerSeries ℚ} {s e e' : ℤ} (h : PD G s e) (h' : PD G' s e') :
    PD (fun M => G M * G' M) s (e + e') := by
  intro n
  have h3 : PolyDeg (fun M => ∑ p ∈ Finset.antidiagonal n,
      PowerSeries.coeff p.1 (G M) * PowerSeries.coeff p.2 (G' M)) (s * n - (e + e')) :=
    PolyDeg.sum _ fun p hp => by
      have hp' := Finset.mem_antidiagonal.1 hp
      refine ((h p.1).mul (h' p.2)).mono (le_of_eq ?_)
      rw [← hp']
      push_cast
      ring
  exact h3.congr fun M => PowerSeries.coeff_mul n _ _

theorem PD.sum {ι : Type*} (S : Finset ι) {G : ι → ℕ → PowerSeries ℚ} {s e : ℤ}
    (h : ∀ a ∈ S, PD (G a) s e) : PD (fun M => ∑ a ∈ S, G a M) s e := by
  intro n
  exact (PolyDeg.sum S fun a ha => h a ha n).congr fun M => map_sum _ _ _

theorem PD_C (c : ℚ) (s : ℤ) : PD (fun _ => PowerSeries.C c) s 0 := by
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ((polyDeg_const c).mono (by simp)).congr fun M => ?_
    simp
  · refine ((polyDeg_zero _).congr fun M => ?_)
    rw [PowerSeries.coeff_C, if_neg hn.ne']

theorem PD.pow {G : ℕ → PowerSeries ℚ} {s e : ℤ} (h : PD G s e) (m : ℕ) :
    PD (fun M => G M ^ m) s (m * e) := by
  induction m with
  | zero =>
    have h3 := PD_C 1 s
    simpa using h3
  | succ m ih =>
    have h3 := ih.mul h
    have e1 : ((m + 1 : ℕ) : ℤ) * e = (m : ℤ) * e + e := by push_cast; ring
    rw [e1]
    intro n
    exact (h3 n).congr fun M => by beta_reduce; rw [pow_succ]

/-- Power sums: if `[tⁿ] y_u` has degree at most `n − 1` in `u` and `t² ∣ y_u`, then
`[tⁿ] ∑_{u<M} y_u^m` has degree at most `2n − 2m` in `M` (`m ≥ 1`). -/
theorem PD_psum (y : ℕ → PowerSeries ℚ) (hy : PD y 1 1)
    (hy2 : ∀ u, (PowerSeries.X : PowerSeries ℚ) ^ 2 ∣ y u) (m : ℕ) (hm : 1 ≤ m) :
    PD (fun M => ∑ u ∈ Finset.range M, y u ^ m) 2 (2 * m) := by
  intro n
  by_cases hn : n < 2 * m
  · refine (polyDeg_zero _).congr fun M => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun u _ => ?_
    have hd : (PowerSeries.X : PowerSeries ℚ) ^ (2 * m) ∣ y u ^ m := by
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd (hy2 u) m
    exact PowerSeries.X_pow_dvd_iff.1 hd n hn
  · have h3 := (hy.pow m n).sum_range
    refine (h3.mono (by push_cast; omega)).congr fun M => ?_
    rw [map_sum]

/-- Newton's identities: the elementary symmetric polynomials `e_k(y_0,…,y_{M−1})` of a family
whose power sums have `[tⁿ]` of degree at most `2n − 2m` have `[tⁿ]` of degree at most
`2n − 2k`. -/
theorem PD_esymm (y : ℕ → PowerSeries ℚ)
    (hP : ∀ m : ℕ, 1 ≤ m → PD (fun M => ∑ u ∈ Finset.range M, y u ^ m) 2 (2 * m)) (k : ℕ) :
    PD (fun M => MvPolynomial.aeval (fun u : Fin M => y u) (MvPolynomial.esymm (Fin M) ℚ k))
      2 (2 * k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h3 := PD_C 1 2
      intro n
      refine (h3 n).congr fun M => ?_
      beta_reduce
      rw [MvPolynomial.esymm_zero, map_one (MvPolynomial.aeval _), map_one PowerSeries.C]
    · have hterm : ∀ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          PD (fun M => PowerSeries.C ((-1 : ℚ) ^ a.1) *
            MvPolynomial.aeval (fun u : Fin M => y u) (MvPolynomial.esymm (Fin M) ℚ a.1) *
            ∑ u ∈ Finset.range M, y u ^ a.2) 2 (2 * k) := by
        intro a ha
        rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
        have h3 := ((PD_C ((-1 : ℚ) ^ a.1) 2).mul (ih a.1 ha.2)).mul (hP a.2 (by omega))
        have e1 : (0 : ℤ) + 2 * (a.1 : ℕ) + 2 * (a.2 : ℕ) = 2 * (k : ℕ) := by
          rw [← ha.1]
          push_cast
          ring
        rwa [e1] at h3
      have hsum := PD.sum _ hterm
      intro n
      have h4 := ((hsum n).const_mul ((-1 : ℚ) ^ (k + 1) / k))
      refine h4.congr fun M => ?_
      beta_reduce
      have hN := congrArg (MvPolynomial.aeval (fun u : Fin M => y u))
        (MvPolynomial.mul_esymm_eq_sum (Fin M) ℚ k)
      simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum, MvPolynomial.psum,
        MvPolynomial.aeval_X] at hN
      have hN2 := congrArg (PowerSeries.coeff n) hN
      have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have e2 : ((k : ℕ) : PowerSeries ℚ) = PowerSeries.C (k : ℚ) := by simp
      have e3 : ((-1 : PowerSeries ℚ)) ^ (k + 1) = PowerSeries.C ((-1 : ℚ) ^ (k + 1)) := by simp
      rw [e2, e3, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hN2
      have e4 : (∑ x ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
          (-1 : PowerSeries ℚ) ^ x.1 *
            MvPolynomial.aeval (fun u : Fin M => y u) (MvPolynomial.esymm (Fin M) ℚ x.1) *
            ∑ i : Fin M, y i ^ x.2) =
          ∑ a ∈ (Finset.antidiagonal k).filter (fun a => a.1 < k),
            PowerSeries.C ((-1 : ℚ) ^ a.1) *
            MvPolynomial.aeval (fun u : Fin M => y u) (MvPolynomial.esymm (Fin M) ℚ a.1) *
            ∑ u ∈ Finset.range M, y u ^ a.2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Fin.sum_univ_eq_sum_range (fun u => y u ^ a.2) M]
        simp
      rw [e4] at hN2
      field_simp
      linear_combination hN2

end Virasoro.H13D
