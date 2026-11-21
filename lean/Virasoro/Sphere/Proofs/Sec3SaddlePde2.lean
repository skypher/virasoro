import Virasoro.Sphere.Proofs.Sec3SaddlePde1

/-!
# Sphere paper Lemma 3.4(i), the `σ²` identity (`sphere/paper.tex` l.742–745)

In the three variables `(p,q,r)`:
`q∂_q(T₁ - U) + r∂_r(T₂ - U) = B(p,q)B(p,r)`, with
`(q-p)T₁ = p(B(q,r) - B(p,r))`, `(r-p)T₂ = p(B(q,r) - B(p,q))`, `(1-p)U = pB(q,r)`.
In coefficients, for `k ≥ 1`:
`m(B_{k+m,l} - B_{m,l}) + l(B_{k+l,m} - B_{m,l}) = ∑_{n=0}^k B_{n,m}B_{k-n,l}`.

Consumer: the `σ²` component of `pdeZero k S0` in part (i) of `Stmt_lem_saddle`.
-/

namespace Virasoro.Sphere

open Finset

theorem rename_one {σ τ : Type*} [DecidableEq σ] [DecidableEq τ] (g : σ → τ)
    [Filter.TendstoCofinite g] (i : σ) (f : PowerSeries ℚ) :
    MvPowerSeries.rename g (one i f) = one (g i) f :=
  MvPowerSeries.rename_rename (fun _ : Unit => i) g f

theorem rename_aS {σ τ : Type*} [DecidableEq σ] [DecidableEq τ] (g : σ → τ)
    [Filter.TendstoCofinite g] (i : σ) :
    MvPowerSeries.rename g (aS i : MvPowerSeries σ ℚ) = aS (g i) :=
  rename_one g i sOne

theorem Bgf_mul_aS : Bgf * (2 * aS 0 * aS 1 * (aS 0 + aS 1) ^ 2) =
    -(MvPowerSeries.X 0 * MvPowerSeries.X 1) := by
  have := Bgf_mul_Bden
  rw [Bden, sqrtOneSub_eq_aS, sqrtOneSub_eq_aS] at this
  exact this

theorem Bden_aS_ne {σ : Type*} [DecidableEq σ] (i j : σ) :
    (2 * aS i * aS j * (aS i + aS j) ^ 2 : MvPowerSeries σ ℚ) ≠ 0 := by
  apply ne_zero_of_constantCoeff
  simp only [map_mul, map_pow, map_add, constantCoeff_aS, map_ofNat]
  norm_num

/-- `B(p,q) = B(q,p)`. -/
theorem Bcoef_symm (m n : ℕ) : Bcoef m n = Bcoef n m := by
  have h1 := congrArg (MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1)) Bgf_mul_aS
  simp only [map_mul, map_pow, map_add, map_neg, map_ofNat, rename_aS,
    MvPowerSeries.rename_X, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1
  have h2 : MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1) Bgf = Bgf := by
    refine mul_right_cancel₀ (Bden_aS_ne (0 : Fin 2) 1) ?_
    linear_combination h1 - Bgf_mul_aS
  have h3 := MvPowerSeries.coeff_embDomain_rename (Equiv.swap (0 : Fin 2) 1).toEmbedding Bgf
    (Finsupp.single 0 m + Finsupp.single 1 n)
  have h4 : Finsupp.embDomain (Equiv.swap (0 : Fin 2) 1).toEmbedding
      (Finsupp.single 0 m + Finsupp.single 1 n) = Finsupp.single 0 n + Finsupp.single 1 m := by
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      Finsupp.mapDomain_single]
    simp [add_comm]
  rw [h4] at h3
  have h5 : MvPowerSeries.rename (Equiv.swap (0 : Fin 2) 1).toEmbedding Bgf = Bgf := h2
  rw [h5] at h3
  exact h3.symm

/-! ### Three variables -/

theorem coeff_rename_fin (g : Fin 2 → Fin 3) (hg : Function.Injective g) (j : Fin 3)
    (hj : ∀ i, g i ≠ j) (hall : ∀ t, t = g 0 ∨ t = g 1 ∨ t = j)
    (f : MvPowerSeries (Fin 2) ℚ) (x : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff x (MvPowerSeries.rename g f) =
      if x j = 0 then
        MvPowerSeries.coeff (Finsupp.single 0 (x (g 0)) + Finsupp.single 1 (x (g 1))) f
      else 0 := by
  by_cases h : x j = 0
  · rw [if_pos h]
    let e : Fin 2 ↪ Fin 3 := ⟨g, hg⟩
    have hx : x = Finsupp.embDomain e
        (Finsupp.single 0 (x (g 0)) + Finsupp.single 1 (x (g 1))) := by
      rw [Finsupp.embDomain_eq_mapDomain, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
        Finsupp.mapDomain_single]
      have h01 : g 0 ≠ g 1 := fun h => by simpa using hg h
      ext t
      rcases hall t with rfl | rfl | rfl
      · simp [e, Finsupp.single_apply, h01.symm]
      · simp [e, Finsupp.single_apply, h01]
      · simp [e, Finsupp.single_apply, hj 0, hj 1, h]
    conv_lhs => rw [hx]
    exact MvPowerSeries.coeff_embDomain_rename e f _
  · rw [if_neg h]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨y, rfl⟩
    apply h
    exact Finsupp.mapDomain_of_notMem_range y j (by rintro ⟨i, hi⟩; exact hj i hi)

/-- `B(p,q)`, `B(p,r)`, `B(q,r)` in the variables `(p,q,r)`. -/
noncomputable def P1 : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.rename ![(0 : Fin 3), 1] Bgf
noncomputable def P2 : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.rename ![(0 : Fin 3), 2] Bgf
noncomputable def P3 : MvPowerSeries (Fin 3) ℚ := MvPowerSeries.rename ![(1 : Fin 3), 2] Bgf

theorem coeff_P1 (x : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff x P1 = if x 2 = 0 then Bcoef (x 0) (x 1) else 0 := by
  rw [P1, coeff_rename_fin ![(0 : Fin 3), 1] (by decide) 2 (by decide) (by decide)]
  rfl

theorem coeff_P2 (x : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff x P2 = if x 1 = 0 then Bcoef (x 0) (x 2) else 0 := by
  rw [P2, coeff_rename_fin ![(0 : Fin 3), 2] (by decide) 1 (by decide) (by decide)]
  rfl

theorem coeff_P3 (x : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff x P3 = if x 0 = 0 then Bcoef (x 1) (x 2) else 0 := by
  rw [P3, coeff_rename_fin ![(1 : Fin 3), 2] (by decide) 0 (by decide) (by decide)]
  rfl

theorem P1_rel : P1 * (2 * aS 0 * aS 1 * (aS 0 + aS 1) ^ 2) =
    -(MvPowerSeries.X 0 * MvPowerSeries.X 1) := by
  have h := congrArg (MvPowerSeries.rename ![(0 : Fin 3), 1]) Bgf_mul_aS
  rw [P1]
  simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat, rename_aS,
    MvPowerSeries.rename_X, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem P2_rel : P2 * (2 * aS 0 * aS 2 * (aS 0 + aS 2) ^ 2) =
    -(MvPowerSeries.X 0 * MvPowerSeries.X 2) := by
  have h := congrArg (MvPowerSeries.rename ![(0 : Fin 3), 2]) Bgf_mul_aS
  rw [P2]
  simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat, rename_aS,
    MvPowerSeries.rename_X, Matrix.cons_val_zero, Matrix.cons_val_one] using h

theorem P3_rel : P3 * (2 * aS 1 * aS 2 * (aS 1 + aS 2) ^ 2) =
    -(MvPowerSeries.X 1 * MvPowerSeries.X 2) := by
  have h := congrArg (MvPowerSeries.rename ![(1 : Fin 3), 2]) Bgf_mul_aS
  rw [P3]
  simpa only [map_mul, map_pow, map_add, map_neg, map_ofNat, rename_aS,
    MvPowerSeries.rename_X, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- `T₁ = ∑_{k≥1,m,l} B_{k+m,l} p^k q^m r^l`. -/
noncomputable def T1 : MvPowerSeries (Fin 3) ℚ :=
  fun x => if 1 ≤ x 0 then Bcoef (x 0 + x 1) (x 2) else 0

/-- `T₂ = ∑_{k≥1,m,l} B_{k+l,m} p^k q^m r^l`. -/
noncomputable def T2 : MvPowerSeries (Fin 3) ℚ :=
  fun x => if 1 ≤ x 0 then Bcoef (x 0 + x 2) (x 1) else 0

/-- `U = ∑_{k≥1,m,l} B_{m,l} p^k q^m r^l`. -/
noncomputable def Uq : MvPowerSeries (Fin 3) ℚ :=
  fun x => if 1 ≤ x 0 then Bcoef (x 1) (x 2) else 0

theorem coeff_T1 (x : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff x T1 = if 1 ≤ x 0 then Bcoef (x 0 + x 1) (x 2) else 0 := rfl

theorem coeff_T2 (x : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff x T2 = if 1 ≤ x 0 then Bcoef (x 0 + x 2) (x 1) else 0 := rfl

theorem coeff_Uq (x : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff x Uq = if 1 ≤ x 0 then Bcoef (x 1) (x 2) else 0 := rfl

theorem fin3_exists (x : Fin 3 →₀ ℕ) :
    ∃ k m l, x = Finsupp.single 0 k + Finsupp.single 1 m + Finsupp.single 2 l :=
  ⟨x 0, x 1, x 2, by ext i; fin_cases i <;> simp⟩

theorem T1_rel : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * T1 =
    MvPowerSeries.X 0 * P3 - MvPowerSeries.X 0 * P2 := by
  ext x
  rw [sub_mul, map_sub, map_sub, coeff_X_mul', coeff_X_mul', coeff_X_mul', coeff_X_mul']
  obtain ⟨k, m, l, rfl⟩ := fin3_exists x
  rcases k with _ | _ | k <;> rcases m with _ | m <;>
    simp [coeff_T1, coeff_P2, coeff_P3, Finsupp.single_apply, Bcoef_zero_left, Bcoef_zero_right]
  all_goals first
    | exact Bcoef_symm _ _
    | (rw [add_comm 1]; exact Bcoef_symm _ _)
    | (rw [add_comm 1])
    | (rw [show ∀ a b : ℕ, a + 1 + 1 + b = a + 1 + (b + 1) from fun a b => by omega, sub_self])

theorem T2_rel : (MvPowerSeries.X 2 - MvPowerSeries.X 0) * T2 =
    MvPowerSeries.X 0 * P3 - MvPowerSeries.X 0 * P1 := by
  ext x
  rw [sub_mul, map_sub, map_sub, coeff_X_mul', coeff_X_mul', coeff_X_mul', coeff_X_mul']
  obtain ⟨k, m, l, rfl⟩ := fin3_exists x
  rcases k with _ | _ | k <;> rcases l with _ | l <;>
    simp [coeff_T2, coeff_P1, coeff_P3, Finsupp.single_apply, Bcoef_zero_left, Bcoef_zero_right]
  all_goals first
    | exact Bcoef_symm _ _
    | (rw [add_comm 1]; exact Bcoef_symm _ _)
    | (rw [add_comm 1])
    | (rw [show ∀ a b : ℕ, a + 1 + 1 + b = a + 1 + (b + 1) from fun a b => by omega, sub_self])

theorem Uq_rel : (1 - MvPowerSeries.X 0) * Uq = MvPowerSeries.X 0 * P3 := by
  ext x
  rw [sub_mul, one_mul, map_sub, coeff_X_mul', coeff_X_mul']
  obtain ⟨k, m, l, rfl⟩ := fin3_exists x
  rcases k with _ | _ | k <;> simp [coeff_Uq, coeff_P3, Finsupp.single_apply]

theorem pderiv_P2 : MvPowerSeries.pderiv ℚ 1 P2 = 0 := by
  ext x
  rw [MvPowerSeries.coeff_pderiv, coeff_P2, if_neg (by simp), zero_mul, map_zero]

theorem pderiv_P1 : MvPowerSeries.pderiv ℚ 2 P1 = 0 := by
  ext x
  rw [MvPowerSeries.coeff_pderiv, coeff_P1, if_neg (by simp), zero_mul, map_zero]

theorem X_sub_X_ne (i j : Fin 3) (hij : i ≠ j) :
    (MvPowerSeries.X i - MvPowerSeries.X j : MvPowerSeries (Fin 3) ℚ) ≠ 0 := by
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  simp [MvPowerSeries.coeff_index_single_X, hij] at this

end Virasoro.Sphere
