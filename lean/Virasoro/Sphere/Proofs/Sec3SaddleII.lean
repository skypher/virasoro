import Virasoro.Sphere.Proofs.Sec3SaddlePsi
import Virasoro.Sphere.Proofs.Sec3SaddlePdeAll

/-!
# Sphere paper Lemma 3.4(ii) (`sphere/paper.tex` l.719–723, proof l.749–757)

With `w = p/(1+√(1-p))²`, `v = q/(1+√(1-q))²`:
`√(1-p)√(1-q) B(p,q) = -2wv/(1-wv)² = -2∑_n n (wv)^n`, so
`B_{m,l} = -2∑_n n [p^m]ψ_n [q^l]ψ_n` with `ψ_n = w^n/√(1-p)`, `[p^m]ψ_n = [w^{-n}]p(w)^{-m}`.
Together with `A_m = -4i∑_n (-1)^{n-1}[p^m]ψ_n` this is
`S⁽⁰⁾(σ) = -4i∑_n (-1)^{n-1} t_n - 2∑_n n t_n²`.

Consumer: part (ii) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem trunc_sum {R : Type*} [CommRing R] (B ab Esq Z : R) (Φ : ℕ → R)
    (hΦ : ∀ n, Φ n * ab * Esq ^ n = Z ^ n) (h0 : B * ab * (Esq - Z) ^ 2 = -2 * Z * Esq)
    (N : ℕ) :
    (B + 2 * ∑ n ∈ range (N + 1), (n : R) * Φ n) * (ab * (Esq - Z) ^ 2 * Esq ^ N) =
      Z ^ (N + 1) * (-2 * ((N : R) + 1) * Esq + 2 * (N : R) * Z) := by
  induction N with
  | zero =>
    simp only [zero_add, sum_range_one, Nat.cast_zero, zero_mul, mul_zero, add_zero, pow_zero,
      mul_one, pow_one]
    linear_combination h0
  | succ N ih =>
    rw [sum_range_succ]
    push_cast
    linear_combination Esq * ih + 2 * ((N : R) + 1) * (Esq - Z) ^ 2 * hΦ (N + 1)

/-- `ψ_n(p) ψ_n(q)`. -/
noncomputable def Phi2 (n : ℕ) : MvPowerSeries (Fin 2) ℚ := one 0 (psi n) * one 1 (psi n)

theorem coeff_Phi2 (n m l : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 l) (Phi2 n) =
      PowerSeries.coeff m (psi n) * PowerSeries.coeff l (psi n) := by
  have hx0 : (Finsupp.single 0 m + Finsupp.single 1 l : Fin 2 →₀ ℕ) 0 = m := by simp
  rw [Phi2, coeff_one_mul, hx0, sum_eq_single m]
  · rw [coeff_one1]
    simp
  · intro j hj hjm
    have := mem_range.1 hj
    rw [coeff_one1, if_neg, mul_zero]
    simp
    omega
  · intro h
    exact absurd (mem_range.2 (Nat.lt_succ_self m)) h

theorem Phi2_rel (n : ℕ) :
    Phi2 n * (aS 0 * aS 1) * (((1 + aS 0) * (1 + aS 1)) ^ 2) ^ n =
      (MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ n := by
  have h0 := congrArg (one (0 : Fin 2)) (psi_rel n)
  have h1 := congrArg (one (1 : Fin 2)) (psi_rel n)
  simp only [map_mul, map_pow, map_add, map_one, one_X] at h0 h1
  rw [← pow_mul, mul_pow, Phi2, aS, aS]
  linear_combination (one 1 (psi n) * one 1 sOne * (1 + one 1 sOne) ^ (2 * n)) * h0 +
    MvPowerSeries.X 0 ^ n * h1

theorem E_rel : ((1 + aS 0) * (1 + aS 1)) ^ 2 - MvPowerSeries.X 0 * MvPowerSeries.X 1 =
    2 * ((1 + aS 0) * (1 + aS 1)) * (aS 0 + aS 1 : MvPowerSeries (Fin 2) ℚ) := by
  linear_combination (-(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℚ)) * aS_sq (0 : Fin 2) -
    (1 - aS 0 ^ 2) * aS_sq (1 : Fin 2)

theorem Bgf_E_rel :
    Bgf * (aS 0 * aS 1) *
        (((1 + aS 0) * (1 + aS 1)) ^ 2 - MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ 2 =
      -2 * (MvPowerSeries.X 0 * MvPowerSeries.X 1) * ((1 + aS 0) * (1 + aS 1)) ^ 2 := by
  linear_combination
    (Bgf * (aS 0 * aS 1) *
      ((((1 + aS 0) * (1 + aS 1)) ^ 2 - MvPowerSeries.X 0 * MvPowerSeries.X 1) +
        2 * ((1 + aS 0) * (1 + aS 1)) * (aS 0 + aS 1))) * E_rel +
    (2 * ((1 + aS 0) * (1 + aS 1)) ^ 2) * Bgf_mul_aS

theorem coeff2_eq_zero_of_mul_unit {f U V : MvPowerSeries (Fin 2) ℚ} {N : ℕ} {x : Fin 2 →₀ ℕ}
    (hU : MvPowerSeries.constantCoeff U ≠ 0)
    (h : f * U = (MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ (N + 1) * V) (hx : x 0 ≤ N) :
    MvPowerSeries.coeff x f = 0 := by
  have hf : f = MvPowerSeries.X 0 ^ (N + 1) * (MvPowerSeries.X 1 ^ (N + 1) * (V * U⁻¹)) := by
    rw [← mul_assoc, ← mul_assoc, ← mul_pow, ← h, mul_assoc, MvPowerSeries.mul_inv_cancel _ hU,
      mul_one]
  rw [hf, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul,
    if_neg (by rw [Finsupp.single_le_iff]; omega)]

/-- `B_{m,l} = -2∑_{n=0}^N n [p^m]ψ_n [q^l]ψ_n` for `m ≤ N`. -/
theorem Bcoef_eq_sum_psi (m l N : ℕ) (hm : m ≤ N) :
    Bcoef m l = -2 * ∑ n ∈ range (N + 1),
      (n : ℚ) * (PowerSeries.coeff m (psi n) * PowerSeries.coeff l (psi n)) := by
  have h := trunc_sum Bgf (aS 0 * aS 1) (((1 + aS 0) * (1 + aS 1)) ^ 2)
    (MvPowerSeries.X 0 * MvPowerSeries.X 1) Phi2 Phi2_rel Bgf_E_rel N
  have hU : MvPowerSeries.constantCoeff
      (aS 0 * aS 1 * (((1 + aS 0) * (1 + aS 1)) ^ 2 - MvPowerSeries.X 0 * MvPowerSeries.X 1) ^ 2 *
        (((1 + aS 0) * (1 + aS 1)) ^ 2) ^ N : MvPowerSeries (Fin 2) ℚ) ≠ 0 := by
    simp only [map_mul, map_pow, map_add, map_sub, map_one, constantCoeff_aS,
      MvPowerSeries.constantCoeff_X]
    positivity
  have h0 := coeff2_eq_zero_of_mul_unit (x := Finsupp.single 0 m + Finsupp.single 1 l) hU h
    (by simpa using hm)
  have h2 : (2 : MvPowerSeries (Fin 2) ℚ) = MvPowerSeries.C 2 := (map_ofNat _ 2).symm
  rw [map_add, h2, MvPowerSeries.coeff_C_mul, map_sum] at h0
  have h3 : ∀ n ∈ range (N + 1), MvPowerSeries.coeff (Finsupp.single 0 m + Finsupp.single 1 l)
      ((n : MvPowerSeries (Fin 2) ℚ) * Phi2 n) =
        (n : ℚ) * (PowerSeries.coeff m (psi n) * PowerSeries.coeff l (psi n)) := by
    intro n _
    rw [show (n : MvPowerSeries (Fin 2) ℚ) = MvPowerSeries.C (n : ℚ) from (map_natCast _ n).symm,
      MvPowerSeries.coeff_C_mul, coeff_Phi2]
  rw [sum_congr rfl h3] at h0
  rw [Bcoef]
  linarith

theorem tcoef_eq (n m : ℕ) : tcoef n m = ((PowerSeries.coeff m (psi n) : ℚ) : ℂ) := by
  rw [tcoef, psi, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [Nat.choose_symm_of_eq_add (show 2 * m = (m - n) + (m + n) by omega)]
    push_cast
    rfl
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `B_{m,l} = -2∑_{n=1}^N n t_{n,m} t_{n,l}` for `m ≤ N`. -/
theorem Bcoef_eq_sum_tcoef (m l N : ℕ) (hm : m ≤ N) :
    (Bcoef m l : ℂ) = -2 * ∑ n ∈ Icc 1 N, (n : ℂ) * (tcoef n m * tcoef n l) := by
  have h := Bcoef_eq_sum_psi m l N hm
  have h' : Bcoef m l = -2 * ∑ n ∈ Icc 1 N,
      (n : ℚ) * (PowerSeries.coeff m (psi n) * PowerSeries.coeff l (psi n)) := by
    rw [h, sum_range_succ', sum_Icc_one_eq_range]
    simp
  rw [h']
  push_cast
  simp only [tcoef_eq]

/-- `A_m = -4i∑_{n=1}^m (-1)^{n-1} t_{n,m}`. -/
theorem Acoef_eq_sum_tcoef (m : ℕ) (hm : 1 ≤ m) :
    Acoef m = ∑ n ∈ Icc 1 m, (-4 * Complex.I * (-1) ^ (n - 1)) * tcoef n m := by
  have h := alt_sum_psi m hm
  have hc : ∑ n ∈ Icc 1 m, ((-1 : ℂ)) ^ n * tcoef n m = -(halfBinom m : ℂ) / 2 := by
    simp only [tcoef_eq]
    exact_mod_cast h
  have hs : ∑ n ∈ Icc 1 m, (-4 * Complex.I * (-1) ^ (n - 1)) * tcoef n m =
      4 * Complex.I * ∑ n ∈ Icc 1 m, ((-1 : ℂ)) ^ n * tcoef n m := by
    rw [mul_sum]
    refine sum_congr rfl fun n hn => ?_
    have h1 := (mem_Icc.1 hn).1
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  rw [hs, hc, Acoef]
  ring

theorem coeff_tsum (α : ℕ+ →₀ ℕ) (N : ℕ) :
    MvPowerSeries.coeff α (∑ n ∈ Icc 1 N,
        ((-4 * Complex.I * (-1) ^ (n - 1)) • tlin n - (2 * (n : ℂ)) • tlin n ^ 2)) =
      ∑ n ∈ Icc 1 N, ((-4 * Complex.I * (-1) ^ (n - 1)) * linSeries (fun m => tcoef n m) α -
        (2 * (n : ℂ)) * MvPowerSeries.coeff α
          (linSeries (fun m => tcoef n m) * linSeries (fun m => tcoef n m))) := by
  rw [map_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [map_sub, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, pow_two]
  rfl

/-- Lemma 3.4(ii): `S⁽⁰⁾(σ) = -4i∑_n (-1)^{n-1} t_n - 2∑_n n t_n²`. -/
theorem S0_diag : S0 = fun α : ℕ+ →₀ ℕ =>
    MvPowerSeries.coeff α
      (∑ n ∈ Icc 1 (α.support.sup fun m => (m : ℕ)),
        ((-4 * Complex.I * (-1) ^ (n - 1)) • tlin n - (2 * (n : ℂ)) • tlin n ^ 2)) := by
  funext α
  show S0 α = _
  rw [coeff_tsum]
  rcases Nat.lt_or_ge α.degree 3 with h | h
  · have h0 : α.degree = 0 ∨ α.degree = 1 ∨ α.degree = 2 := by omega
    rcases h0 with hd | hd | hd
    · have : α = 0 := (Finsupp.degree_eq_zero_iff _).1 hd
      subst this
      simp [S0]
    · obtain ⟨m, rfl⟩ := exists_single_of_degree_one α hd
      rw [S0_single, Finsupp.support_single_ne_zero _ one_ne_zero, sup_singleton,
        Acoef_eq_sum_tcoef m m.pos]
      refine sum_congr rfl fun n _ => ?_
      rw [linSeries_single, coeff_linSeries_mul_of_degree_ne _ _ _
        (by rw [Finsupp.degree_single]; norm_num), mul_zero, sub_zero]
    · obtain ⟨m, l, rfl⟩ := exists_pair_of_degree_two α hd
      have hlin : ∀ c, linSeries c (Finsupp.single m 1 + Finsupp.single l 1) = 0 := fun c =>
        linSeries_of_degree_ne c _ (by omega)
      have hmN : (m : ℕ) ≤ (Finsupp.single m 1 + Finsupp.single l 1 : ℕ+ →₀ ℕ).support.sup
          (fun m : ℕ+ => (m : ℕ)) :=
        Finset.le_sup (f := fun m : ℕ+ => (m : ℕ)) (by simp [Finsupp.mem_support_iff])
      have hB := Bcoef_eq_sum_tcoef m l _ hmN
      by_cases hml : m = l
      · subst hml
        rw [S0_pair, if_pos rfl, hB]
        simp only [hlin, mul_zero, zero_sub, coeff_linSeries_mul_eq]
        rw [mul_sum]
        exact sum_congr rfl fun n _ => by ring
      · rw [S0_pair, if_neg hml, Bcoef_symm l m, hB]
        simp only [hlin, mul_zero, zero_sub, coeff_linSeries_mul_ne _ _ m l hml]
        rw [← two_mul, mul_sum, mul_sum]
        exact sum_congr rfl fun n _ => by ring
  · rw [S0, if_neg (by omega), if_neg (by omega)]
    symm
    refine sum_eq_zero fun n _ => ?_
    rw [linSeries_of_degree_ne _ _ (by omega),
      coeff_linSeries_mul_of_degree_ne _ _ _ (by omega)]
    ring

end Virasoro.Sphere
