import Virasoro.Sphere.Statements.Sec2
import Virasoro.Proofs.Sec4Core1
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The claims of Definition 2.2 of `sphere/paper.tex`

* `z(q) = 16 q ψ(q)⁴ θ₃(q)⁻⁴` with `ψ, θ₃ ∈ 1 + qℤ[[q]]`, so `z(q) ∈ 16q(1 + qℤ[[q]])`.
* Each of the three factors of `Φ̃` is a power `f^a = ∑_k binom(a,k)(f-1)^k` of a series
  `f ∈ 1 + qℚ[[q]]` with an exponent `a` that is a polynomial over `ℚ` in `(c,Δ,Δ_i)`; the
  coefficient of `q^n` is a finite sum of products of such polynomials and rational numbers.
* `H_0 = ℬ_0 = 1`.
-/

namespace Virasoro.Sphere

section Maps

variable {A B : Type*} [Field A] [Field B] (f : A →+* B)

theorem map_th3 : PowerSeries.map f (th3 A) = th3 B := by
  ext n
  simp [th3, PowerSeries.coeff_map]

theorem map_thPsi : PowerSeries.map f (thPsi A) = thPsi B := by
  ext n
  simp [thPsi, PowerSeries.coeff_map]

theorem constantCoeff_th3 : PowerSeries.constantCoeff (th3 A) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [th3, theta3Z, PowerSeries.coeff_map, PowerSeries.coeff_mk]

theorem constantCoeff_thPsi : PowerSeries.constantCoeff (thPsi A) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [thPsi, thetaPsiZ, PowerSeries.coeff_map, PowerSeries.coeff_mk]

theorem map_inv_of_ne (φ : PowerSeries A) (h : PowerSeries.constantCoeff φ ≠ 0) :
    PowerSeries.map f φ⁻¹ = (PowerSeries.map f φ)⁻¹ := by
  have h' : PowerSeries.constantCoeff (PowerSeries.map f φ) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (map_ne_zero f).2 h
  rw [PowerSeries.eq_inv_iff_mul_eq_one h', ← map_mul, PowerSeries.inv_mul_cancel _ h, map_one]

theorem map_nomeRatio : PowerSeries.map f (nomeRatio A) = nomeRatio B := by
  unfold nomeRatio
  rw [map_mul, map_inv_of_ne f _ (by rw [map_pow, constantCoeff_thPsi]; norm_num), map_pow,
    map_pow, map_th3, map_thPsi]

theorem map_zq : PowerSeries.map f (zq A) = zq B := by
  unfold zq
  rw [map_mul, map_mul, map_mul, map_inv_of_ne f _ (by rw [map_pow, constantCoeff_th3]; norm_num),
    map_pow, map_pow, map_th3, map_thPsi, map_ofNat, PowerSeries.map_X]

end Maps

/-! ### `z(q) ∈ 16q(1 + qℤ[[q]])` -/

theorem zq_rat_eq :
    zq ℚ = PowerSeries.X * (PowerSeries.C (16 : ℚ) *
      PowerSeries.map (Int.castRingHom ℚ)
        (thetaPsiZ ^ 4 * PowerSeries.invOfUnit (theta3Z ^ 4) 1)) := by
  have h3 : PowerSeries.constantCoeff theta3Z = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [theta3Z, PowerSeries.coeff_mk]
  have hc : PowerSeries.constantCoeff (theta3Z ^ 4) = ((1 : ℤˣ) : ℤ) := by
    rw [map_pow, h3]
    norm_num
  have h34 : PowerSeries.constantCoeff (th3 ℚ ^ 4) ≠ 0 := by
    rw [map_pow, constantCoeff_th3]
    norm_num
  have e3 : th3 ℚ ^ 4 = PowerSeries.map (Int.castRingHom ℚ) (theta3Z ^ 4) := by
    rw [map_pow]
    rfl
  have ep : thPsi ℚ ^ 4 = PowerSeries.map (Int.castRingHom ℚ) (thetaPsiZ ^ 4) := by
    rw [map_pow]
    rfl
  have hinv : (th3 ℚ ^ 4)⁻¹ =
      PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOfUnit (theta3Z ^ 4) 1) := by
    symm
    rw [PowerSeries.eq_inv_iff_mul_eq_one h34, e3, ← map_mul, mul_comm,
      PowerSeries.mul_invOfUnit _ _ hc, map_one]
  unfold zq
  rw [hinv, ep, map_mul, ← map_ofNat (PowerSeries.C (R := ℚ)) 16]
  ring

theorem coeff_zero_U :
    PowerSeries.coeff 0 (thetaPsiZ ^ 4 * PowerSeries.invOfUnit (theta3Z ^ 4) 1) = 1 := by
  have hp : PowerSeries.constantCoeff thetaPsiZ = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [thetaPsiZ, PowerSeries.coeff_mk]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, hp,
    PowerSeries.constantCoeff_invOfUnit]
  norm_num

/-! ### `H_0 = 1` -/

section Zero

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

theorem Bsph_zero (c : 𝔽) (Δe : Fin 4 → 𝔽) : Bsph c Δe 0 = 1 := by
  have hg : gramPoly c 0 = 1 := by
    ext Y Y'
    rw [Subsingleton.elim Y Y']
    simp [gramPoly, gram, partition_zero_word, gramWord, vac]
  have hγ : ∀ (a b : 𝔽) (Y : Nat.Partition 0), gammaPoly a b 0 Y = 1 := by
    intro a b Y
    simp [gammaPoly, partition_zero_word, gammaY]
  unfold Bsph Bnum
  rw [hg, Matrix.det_one, Matrix.adjugate_one]
  simp [hγ, Matrix.one_apply]

theorem fpow_coeff_zero {A : Type*} [Field A] (f : PowerSeries A) (a : A) :
    PowerSeries.coeff 0 (fpow f a) = 1 := by
  simp [fpow, gbinom, PowerSeries.coeff_mk]

theorem PhiTilde_coeff_zero (c : 𝔽) (Δe : Fin 4 → 𝔽) :
    PowerSeries.coeff 0 (PhiTilde c Δe) = 1 := by
  unfold PhiTilde
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_mul,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, fpow_coeff_zero, fpow_coeff_zero,
    fpow_coeff_zero]
  norm_num

theorem Hsph_zero (c : 𝔽) (Δe : Fin 4 → 𝔽) : Hsph c Δe 0 = 1 := by
  have hB : PowerSeries.coeff 0 (BzSeries c Δe) = 1 := by
    simp [BzSeries, PowerSeries.coeff_mk, Bsph_zero]
  unfold Hsph Hseries
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_inv,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PhiTilde_coeff_zero, hB]
  norm_num

end Zero

/-! ### The coefficients of `Φ̃` are polynomials in `(c,Δ,Δ_1,…,Δ_4)` over `ℚ` -/

/-- The point `(c, Δ, Δ₁, Δ₂, Δ₃, Δ₄)` of `ℂ(Δ)⁶`. -/
noncomputable abbrev vec6 (c : ℂ) (Δe : Fin 4 → ℂ) : Fin 6 → RatFunc ℂ :=
  ![RatFunc.C c, RatFunc.X, RatFunc.C (Δe 0), RatFunc.C (Δe 1), RatFunc.C (Δe 2),
    RatFunc.C (Δe 3)]

/-- A family of elements of `ℂ(Δ)` given by one polynomial over `ℚ` in `(c,Δ,Δ_i)`. -/
def IsPolyFam (F : ℂ → (Fin 4 → ℂ) → RatFunc ℂ) : Prop :=
  ∃ Q : MvPolynomial (Fin 6) ℚ, ∀ c Δe, F c Δe = MvPolynomial.aeval (vec6 c Δe) Q

theorem IsPolyFam.const (r : ℚ) : IsPolyFam fun _ _ => algebraMap ℚ (RatFunc ℂ) r :=
  ⟨MvPolynomial.C r, fun c Δe => by rw [MvPolynomial.aeval_C]⟩

theorem IsPolyFam.add {F G : ℂ → (Fin 4 → ℂ) → RatFunc ℂ} (hF : IsPolyFam F)
    (hG : IsPolyFam G) : IsPolyFam fun c Δe => F c Δe + G c Δe := by
  obtain ⟨P, hP⟩ := hF
  obtain ⟨Q, hQ⟩ := hG
  exact ⟨P + Q, fun c Δe => by simp only [map_add, hP c Δe, hQ c Δe]⟩

theorem IsPolyFam.mul {F G : ℂ → (Fin 4 → ℂ) → RatFunc ℂ} (hF : IsPolyFam F)
    (hG : IsPolyFam G) : IsPolyFam fun c Δe => F c Δe * G c Δe := by
  obtain ⟨P, hP⟩ := hF
  obtain ⟨Q, hQ⟩ := hG
  exact ⟨P * Q, fun c Δe => by simp only [map_mul, hP c Δe, hQ c Δe]⟩

theorem IsPolyFam.sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → (Fin 4 → ℂ) → RatFunc ℂ}
    (hF : ∀ i ∈ s, IsPolyFam (F i)) : IsPolyFam fun c Δe => ∑ i ∈ s, F i c Δe := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, fun c Δe => by simp only [Finset.sum_empty, map_zero]⟩
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    obtain ⟨Q, hQ⟩ := h1.add h2
    exact ⟨Q, fun c Δe => by simpa only [Finset.sum_insert ha] using hQ c Δe⟩

theorem IsPolyFam.prod {ι : Type*} (s : Finset ι) {F : ι → ℂ → (Fin 4 → ℂ) → RatFunc ℂ}
    (hF : ∀ i ∈ s, IsPolyFam (F i)) : IsPolyFam fun c Δe => ∏ i ∈ s, F i c Δe := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, fun c Δe => by simp only [Finset.prod_empty, map_one]⟩
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    obtain ⟨Q, hQ⟩ := h1.mul h2
    exact ⟨Q, fun c Δe => by simpa only [Finset.prod_insert ha] using hQ c Δe⟩

theorem IsPolyFam.gbinom {a : ℂ → (Fin 4 → ℂ) → RatFunc ℂ} (ha : IsPolyFam a) (k : ℕ) :
    IsPolyFam fun c Δe => Virasoro.Sphere.gbinom (a c Δe) k := by
  have h1 : IsPolyFam fun c Δe => ∏ i ∈ Finset.range k, (a c Δe - (i : RatFunc ℂ)) := by
    refine IsPolyFam.prod _ fun i _ => ?_
    obtain ⟨Q, hQ⟩ := ha.add (IsPolyFam.const (-(i : ℚ)))
    refine ⟨Q, fun c Δe => ?_⟩
    have h := hQ c Δe
    simp only [map_neg, map_natCast] at h
    rw [← h]
    exact sub_eq_add_neg _ _
  obtain ⟨Q, hQ⟩ := h1.mul (IsPolyFam.const ((k.factorial : ℚ)⁻¹))
  refine ⟨Q, fun c Δe => ?_⟩
  have h := hQ c Δe
  simp only [map_inv₀, map_natCast] at h
  rw [← h]
  exact div_eq_mul_inv _ _

theorem IsPolyFam.fpow_coeff (g : PowerSeries ℚ) {a : ℂ → (Fin 4 → ℂ) → RatFunc ℂ}
    (ha : IsPolyFam a) (n : ℕ) :
    IsPolyFam fun c Δe =>
      PowerSeries.coeff n (fpow (PowerSeries.map (algebraMap ℚ (RatFunc ℂ)) g) (a c Δe)) := by
  have hk : ∀ k : ℕ, PowerSeries.coeff n
      ((PowerSeries.map (algebraMap ℚ (RatFunc ℂ)) g - 1) ^ k) =
        algebraMap ℚ (RatFunc ℂ) (PowerSeries.coeff n ((g - 1) ^ k)) := by
    intro k
    have e : (PowerSeries.map (algebraMap ℚ (RatFunc ℂ)) g - 1) ^ k =
        PowerSeries.map (algebraMap ℚ (RatFunc ℂ)) ((g - 1) ^ k) := by
      rw [map_pow, map_sub, map_one]
    rw [e, PowerSeries.coeff_map]
  obtain ⟨Q, hQ⟩ := IsPolyFam.sum (Finset.range (n + 1)) fun k _ =>
    (ha.gbinom k).mul (IsPolyFam.const (PowerSeries.coeff n ((g - 1) ^ k)))
  refine ⟨Q, fun c Δe => ?_⟩
  rw [← hQ c Δe]
  simp only [Virasoro.Sphere.fpow, PowerSeries.coeff_mk, hk]

theorem IsPolyFam.coeff_mul {S T : ℂ → (Fin 4 → ℂ) → PowerSeries (RatFunc ℂ)}
    (hS : ∀ n, IsPolyFam fun c Δe => PowerSeries.coeff n (S c Δe))
    (hT : ∀ n, IsPolyFam fun c Δe => PowerSeries.coeff n (T c Δe)) (n : ℕ) :
    IsPolyFam fun c Δe => PowerSeries.coeff n (S c Δe * T c Δe) := by
  obtain ⟨Q, hQ⟩ := IsPolyFam.sum (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ))
    fun p _ => (hS p.1).mul (hT p.2)
  refine ⟨Q, fun c Δe => ?_⟩
  exact (PowerSeries.coeff_mul n (S c Δe) (T c Δe)).trans (hQ c Δe)

theorem isPolyFam_PhiTilde (n : ℕ) :
    IsPolyFam fun c Δe => PowerSeries.coeff n (PhiTilde c Δe) := by
  have a1 : IsPolyFam fun c _ => (RatFunc.X - (RatFunc.C c - 1) / 24 : RatFunc ℂ) := by
    refine ⟨MvPolynomial.X 1 - (MvPolynomial.X 0 - 1) * MvPolynomial.C (1 / 24), fun c Δe => ?_⟩
    simp [vec6, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    ring
  have a2 : IsPolyFam fun c Δe =>
      ((RatFunc.C c - 1) / 24 - RatFunc.C (Δe 1) - RatFunc.C (Δe 2) : RatFunc ℂ) := by
    refine ⟨(MvPolynomial.X 0 - 1) * MvPolynomial.C (1 / 24) - MvPolynomial.X 3
      - MvPolynomial.X 4, fun c Δe => ?_⟩
    simp [vec6, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    ring
  have a3 : IsPolyFam fun c Δe =>
      ((RatFunc.C c - 1) / 2 - 4 * RatFunc.C (Δe 0 + Δe 1 + Δe 2 + Δe 3) : RatFunc ℂ) := by
    refine ⟨(MvPolynomial.X 0 - 1) * MvPolynomial.C (1 / 2) - 4 * (MvPolynomial.X 2
      + MvPolynomial.X 3 + MvPolynomial.X 4 + MvPolynomial.X 5), fun c Δe => ?_⟩
    simp [vec6, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    ring
  have e1 : nomeRatio (RatFunc ℂ) =
      PowerSeries.map (algebraMap ℚ (RatFunc ℂ)) (nomeRatio ℚ) := (map_nomeRatio _).symm
  have e2 : (1 - zq (RatFunc ℂ) : PowerSeries (RatFunc ℂ)) =
      PowerSeries.map (algebraMap ℚ (RatFunc ℂ)) (1 - zq ℚ) := by
    rw [map_sub, map_one, map_zq]
  have e3 : th3 (RatFunc ℂ) = PowerSeries.map (algebraMap ℚ (RatFunc ℂ)) (th3 ℚ) :=
    (map_th3 _).symm
  unfold PhiTilde
  rw [e1, e2, e3]
  exact IsPolyFam.coeff_mul
    (IsPolyFam.coeff_mul (fun m => IsPolyFam.fpow_coeff _ a1 m)
      (fun m => IsPolyFam.fpow_coeff _ a2 m))
    (fun m => IsPolyFam.fpow_coeff _ a3 m) n

/-- The claims of Definition 2.2.

Paper label: def:H-series -/
theorem def_H_series : Stmt_def_H_series := by
  refine ⟨⟨?_, ?_, fun n => ?_⟩, fun n => ?_, fun c Δe => Hsph_zero c Δe⟩
  · rw [zq_rat_eq, PowerSeries.coeff_zero_X_mul]
  · rw [zq_rat_eq, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
      coeff_zero_U]
    norm_num
  · refine ⟨PowerSeries.coeff (n + 1)
      (thetaPsiZ ^ 4 * PowerSeries.invOfUnit (theta3Z ^ 4) 1), ?_⟩
    rw [zq_rat_eq, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]
    rfl
  · by_cases hn : n = 0
    · subst hn
      exact ⟨1, fun _ => rfl, fun c Δe => by rw [PhiTilde_coeff_zero, map_one]⟩
    · obtain ⟨Q, hQ⟩ := isPolyFam_PhiTilde n
      exact ⟨Q, fun h => absurd h hn, fun c Δe => hQ c Δe⟩

example : Stmt_def_H_series := def_H_series

end Virasoro.Sphere
