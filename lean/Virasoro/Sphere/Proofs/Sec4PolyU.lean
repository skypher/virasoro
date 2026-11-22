import Virasoro.Sphere.Proofs.Sec3PolyH

/-!
# `H_N det G_N` is one polynomial over `ℚ` in `(c,Δ,Δ_i)`, over every field

Sphere paper Theorem 3.1 (l.411–414) states `H_N = P_N/det G_N` with
`P_N ∈ ℚ[c,Δ,Δ_1,…,Δ_4]`.  The polynomial `P_N` is the same over every field of characteristic
zero: the coefficients of `Φ̃` and `Φ̃⁻¹`, the numerators of `ℬ_m` and the quotients
`det G_N/det G_m` are given by polynomials over `ℚ`.  This is the form in which Proposition 4.4
is applied to the germ `b = b⋆ + t` in the proof of Theorem 4.7 (l.1392–1393).
-/

namespace Virasoro.Sphere

open Polynomial

/-- A family of rational functions of `Δ`, one over each field of characteristic zero. -/
abbrev Fam : Type 1 := ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽], 𝔽 → (Fin 4 → 𝔽) → RatFunc 𝔽

/-- The point `(c, Δ, Δ₁, Δ₂, Δ₃, Δ₄)` of `𝔽(Δ)⁶`. -/
noncomputable abbrev vec6U {𝔽 : Type} [Field 𝔽] (c : 𝔽) (Δe : Fin 4 → 𝔽) : Fin 6 → RatFunc 𝔽 :=
  ![RatFunc.C c, RatFunc.X, RatFunc.C (Δe 0), RatFunc.C (Δe 1), RatFunc.C (Δe 2),
    RatFunc.C (Δe 3)]

/-- A family given by one polynomial over `ℚ` in `(c,Δ,Δ_i)`. -/
def IsPolyFamU (F : Fam) : Prop :=
  ∃ Q : MvPolynomial (Fin 6) ℚ, ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] (c : 𝔽) (Δe : Fin 4 → 𝔽),
    F 𝔽 c Δe = MvPolynomial.aeval (vec6U c Δe) Q

theorem IsPolyFamU.const (r : ℚ) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] _ _ => algebraMap ℚ (RatFunc 𝔽) r :=
  ⟨MvPolynomial.C r, by intro 𝔽 _ _ c Δe; rw [MvPolynomial.aeval_C]⟩

theorem isPolyFamU_zero :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] _ _ => (0 : RatFunc 𝔽) :=
  ⟨0, by intro 𝔽 _ _ c Δe; rw [map_zero]⟩

theorem IsPolyFamU.add {F G : Fam} (hF : IsPolyFamU F) (hG : IsPolyFamU G) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe => F 𝔽 c Δe + G 𝔽 c Δe := by
  obtain ⟨P, hP⟩ := hF
  obtain ⟨Q, hQ⟩ := hG
  exact ⟨P + Q, by intro 𝔽 _ _ c Δe; simp only [map_add, hP 𝔽 c Δe, hQ 𝔽 c Δe]⟩

theorem IsPolyFamU.mul {F G : Fam} (hF : IsPolyFamU F) (hG : IsPolyFamU G) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe => F 𝔽 c Δe * G 𝔽 c Δe := by
  obtain ⟨P, hP⟩ := hF
  obtain ⟨Q, hQ⟩ := hG
  exact ⟨P * Q, by intro 𝔽 _ _ c Δe; simp only [map_mul, hP 𝔽 c Δe, hQ 𝔽 c Δe]⟩

theorem IsPolyFamU.sum {ι : Type*} (s : Finset ι) {F : ι → Fam}
    (hF : ∀ i ∈ s, IsPolyFamU (F i)) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe => ∑ i ∈ s, F i 𝔽 c Δe := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, by intro 𝔽 _ _ c Δe; simp only [Finset.sum_empty, map_zero]⟩
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    obtain ⟨Q, hQ⟩ := h1.add h2
    exact ⟨Q, by intro 𝔽 _ _ c Δe; simpa only [Finset.sum_insert ha] using hQ 𝔽 c Δe⟩

theorem IsPolyFamU.prod {ι : Type*} (s : Finset ι) {F : ι → Fam}
    (hF : ∀ i ∈ s, IsPolyFamU (F i)) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe => ∏ i ∈ s, F i 𝔽 c Δe := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, by intro 𝔽 _ _ c Δe; simp only [Finset.prod_empty, map_one]⟩
  | insert a s ha ih =>
    have h1 := hF a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi => hF i (Finset.mem_insert_of_mem hi)
    obtain ⟨Q, hQ⟩ := h1.mul h2
    exact ⟨Q, by intro 𝔽 _ _ c Δe; simpa only [Finset.prod_insert ha] using hQ 𝔽 c Δe⟩

theorem IsPolyFamU.gbinom {a : Fam} (ha : IsPolyFamU a) (k : ℕ) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      Virasoro.Sphere.gbinom (a 𝔽 c Δe) k := by
  have h1 : IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      ∏ i ∈ Finset.range k, (a 𝔽 c Δe - (i : RatFunc 𝔽)) := by
    refine IsPolyFamU.prod (F := fun (i : ℕ) (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      a 𝔽 c Δe - (i : RatFunc 𝔽)) _ fun i _ => ?_
    obtain ⟨Q, hQ⟩ := ha.add (IsPolyFamU.const (-(i : ℚ)))
    refine ⟨Q, ?_⟩
    intro 𝔽 _ _ c Δe
    have h := hQ 𝔽 c Δe
    simp only [map_neg, map_natCast] at h
    rw [← h]
    exact sub_eq_add_neg _ _
  obtain ⟨Q, hQ⟩ := h1.mul (IsPolyFamU.const ((k.factorial : ℚ)⁻¹))
  refine ⟨Q, ?_⟩
  intro 𝔽 _ _ c Δe
  have h := hQ 𝔽 c Δe
  simp only [map_inv₀, map_natCast] at h
  rw [← h]
  exact div_eq_mul_inv _ _

theorem IsPolyFamU.fpow_coeff (g : PowerSeries ℚ) {a : Fam} (ha : IsPolyFamU a) (n : ℕ) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      PowerSeries.coeff n (fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g) (a 𝔽 c Δe)) := by
  have hk : ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] (k : ℕ), PowerSeries.coeff n
      ((PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g - 1) ^ k) =
        algebraMap ℚ (RatFunc 𝔽) (PowerSeries.coeff n ((g - 1) ^ k)) := by
    intro 𝔽 _ _ k
    have e : (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) g - 1) ^ k =
        PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) ((g - 1) ^ k) := by
      rw [map_pow, map_sub, map_one]
    rw [e, PowerSeries.coeff_map]
  obtain ⟨Q, hQ⟩ := IsPolyFamU.sum (Finset.range (n + 1))
    (F := fun k (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      Virasoro.Sphere.gbinom (a 𝔽 c Δe) k *
        algebraMap ℚ (RatFunc 𝔽) (PowerSeries.coeff n ((g - 1) ^ k)))
    fun k _ => (ha.gbinom k).mul (IsPolyFamU.const (PowerSeries.coeff n ((g - 1) ^ k)))
  refine ⟨Q, ?_⟩
  intro 𝔽 _ _ c Δe
  rw [← hQ 𝔽 c Δe]
  beta_reduce
  simp only [Virasoro.Sphere.fpow, PowerSeries.coeff_mk, hk 𝔽]

theorem IsPolyFamU.coeff_mul
    {S T : ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽], 𝔽 → (Fin 4 → 𝔽) → PowerSeries (RatFunc 𝔽)}
    (hS : ∀ n, IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      PowerSeries.coeff n (S 𝔽 c Δe))
    (hT : ∀ n, IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      PowerSeries.coeff n (T 𝔽 c Δe)) (n : ℕ) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      PowerSeries.coeff n (S 𝔽 c Δe * T 𝔽 c Δe) := by
  obtain ⟨Q, hQ⟩ := IsPolyFamU.sum (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ))
    (F := fun p (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      PowerSeries.coeff p.1 (S 𝔽 c Δe) * PowerSeries.coeff p.2 (T 𝔽 c Δe))
    fun p _ => (hS p.1).mul (hT p.2)
  refine ⟨Q, ?_⟩
  intro 𝔽 _ _ c Δe
  exact (PowerSeries.coeff_mul n (S 𝔽 c Δe) (T 𝔽 c Δe)).trans (hQ 𝔽 c Δe)

theorem isPolyFamU_PhiTilde (n : ℕ) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      PowerSeries.coeff n (PhiTilde c Δe) := by
  have a1 : IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c _ =>
      (RatFunc.X - (RatFunc.C c - 1) / 24 : RatFunc 𝔽) := by
    refine ⟨MvPolynomial.X 1 - (MvPolynomial.X 0 - 1) * MvPolynomial.C (1 / 24), ?_⟩
    intro 𝔽 _ _ c Δe
    simp [vec6U, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    ring
  have a2 : IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      ((RatFunc.C c - 1) / 24 - RatFunc.C (Δe 1) - RatFunc.C (Δe 2) : RatFunc 𝔽) := by
    refine ⟨(MvPolynomial.X 0 - 1) * MvPolynomial.C (1 / 24) - MvPolynomial.X 3
      - MvPolynomial.X 4, ?_⟩
    intro 𝔽 _ _ c Δe
    simp [vec6U, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    ring
  have a3 : IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      ((RatFunc.C c - 1) / 2 - 4 * RatFunc.C (Δe 0 + Δe 1 + Δe 2 + Δe 3) : RatFunc 𝔽) := by
    refine ⟨(MvPolynomial.X 0 - 1) * MvPolynomial.C (1 / 2) - 4 * (MvPolynomial.X 2
      + MvPolynomial.X 3 + MvPolynomial.X 4 + MvPolynomial.X 5), ?_⟩
    intro 𝔽 _ _ c Δe
    simp [vec6U, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    ring
  have hrw : ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] (c : 𝔽) (Δe : Fin 4 → 𝔽), PhiTilde c Δe =
      fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (nomeRatio ℚ))
          (RatFunc.X - (RatFunc.C c - 1) / 24) *
        fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (1 - zq ℚ))
          ((RatFunc.C c - 1) / 24 - RatFunc.C (Δe 1) - RatFunc.C (Δe 2)) *
        fpow (PowerSeries.map (algebraMap ℚ (RatFunc 𝔽)) (th3 ℚ))
          ((RatFunc.C c - 1) / 2 - 4 * RatFunc.C (Δe 0 + Δe 1 + Δe 2 + Δe 3)) := by
    intro 𝔽 _ _ c Δe
    rw [map_nomeRatio, map_sub, map_one, map_zq, map_th3]
    rfl
  obtain ⟨Q, hQ⟩ := IsPolyFamU.coeff_mul
    (IsPolyFamU.coeff_mul (fun m => IsPolyFamU.fpow_coeff (nomeRatio ℚ) a1 m)
      (fun m => IsPolyFamU.fpow_coeff (1 - zq ℚ) a2 m))
    (fun m => IsPolyFamU.fpow_coeff (th3 ℚ) a3 m) n
  refine ⟨Q, ?_⟩
  intro 𝔽 _ _ c Δe
  have hq := hQ 𝔽 c Δe
  beta_reduce at hq ⊢
  rw [hrw 𝔽 c Δe]
  exact hq

/-- The coefficients of `Φ̃⁻¹` are polynomials over `ℚ` in `(c,Δ,Δ_i)`, over every field. -/
theorem isPolyFamU_PhiTilde_inv (n : ℕ) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      PowerSeries.coeff n (PhiTilde c Δe)⁻¹ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hcc : ∀ (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] (c : 𝔽) (Δe : Fin 4 → 𝔽),
        PowerSeries.constantCoeff (PhiTilde c Δe) = 1 := by
      intro 𝔽 _ _ c Δe
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PhiTilde_coeff_zero]
    rcases n.eq_zero_or_pos with rfl | hn
    · refine ⟨1, ?_⟩
      intro 𝔽 _ _ c Δe
      beta_reduce
      rw [PowerSeries.coeff_inv, if_pos rfl, hcc, inv_one, map_one]
    · have hterm : ∀ x : ℕ × ℕ, IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
          if x.2 < n then PowerSeries.coeff x.1 (PhiTilde c Δe) *
            PowerSeries.coeff x.2 (PhiTilde c Δe)⁻¹ else 0 := by
        intro x
        by_cases hx : x.2 < n
        · simp only [if_pos hx]
          exact (isPolyFamU_PhiTilde x.1).mul (ih x.2 hx)
        · simp only [if_neg hx]
          exact isPolyFamU_zero
      obtain ⟨Q, hQ⟩ := (IsPolyFamU.const (-1)).mul
        (IsPolyFamU.sum (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ))
          (F := fun x (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
            if x.2 < n then PowerSeries.coeff x.1 (PhiTilde c Δe) *
              PowerSeries.coeff x.2 (PhiTilde c Δe)⁻¹ else 0)
          fun x _ => hterm x)
      refine ⟨Q, ?_⟩
      intro 𝔽 _ _ c Δe
      rw [← hQ 𝔽 c Δe]
      beta_reduce
      rw [PowerSeries.coeff_inv, if_neg hn.ne', hcc, inv_one, map_neg, map_one]

/-! ### The numerator of `ℬ_m` over a field -/

section Field

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

/-- Evaluation at the point `(c,Δ,Δ₁,…,Δ₄)` of `𝔽(Δ)⁶`. -/
noncomputable def a6U (c : 𝔽) (Δe : Fin 4 → 𝔽) : R6 →+* RatFunc 𝔽 :=
  (MvPolynomial.aeval (vec6U c Δe)).toRingHom

theorem a6U_apply (c : 𝔽) (Δe : Fin 4 → 𝔽) (Q : R6) :
    a6U c Δe Q = MvPolynomial.aeval (vec6U c Δe) Q := rfl

theorem a6U_X (c : 𝔽) (Δe : Fin 4 → 𝔽) (i : Fin 6) :
    a6U c Δe (MvPolynomial.X i) = vec6U c Δe i := by
  rw [a6U_apply, MvPolynomial.aeval_X]

theorem a6U_gram6 (c : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) :
    (gram6 N).map (a6U c Δe) = (gramPoly c N).map (algebraMap 𝔽[X] (RatFunc 𝔽)) := by
  rw [gram6, ← gram_map (a6U c Δe), gramPoly, ← gram_map (algebraMap 𝔽[X] (RatFunc 𝔽)), a6U_X,
    a6U_X, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rfl

theorem a6U_det6 (c : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ) :
    a6U c Δe (det6 N) = algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det := by
  rw [det6, RingHom.map_det, RingHom.mapMatrix_apply, a6U_gram6, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]

theorem a6U_gamma6 (c : 𝔽) (Δe : Fin 4 → 𝔽) (i j : Fin 6) (w : List ℕ) :
    a6U c Δe (gamma6 i j w) = gammaY RatFunc.X (vec6U c Δe i) (vec6U c Δe j) w := by
  rw [gamma6, map_gammaY, a6U_X, a6U_X, a6U_X]
  rfl

theorem algebraMap_gammaPolyU (Δa Δb : 𝔽) (N : ℕ) (Y : Nat.Partition N) :
    algebraMap 𝔽[X] (RatFunc 𝔽) (gammaPoly Δa Δb N Y) =
      gammaY RatFunc.X (RatFunc.C Δa) (RatFunc.C Δb) Y.word := by
  rw [gammaPoly, map_gammaY, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_C]

theorem a6U_Bnum6 (c : 𝔽) (Δe : Fin 4 → 𝔽) (m : ℕ) :
    a6U c Δe (Bnum6 m) = algebraMap 𝔽[X] (RatFunc 𝔽) (Bnum c Δe m) := by
  have hadj : (gram6 m).adjugate.map (a6U c Δe) =
      (gramPoly c m).adjugate.map (algebraMap 𝔽[X] (RatFunc 𝔽)) := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, a6U_gram6,
      ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply]
  rw [Bnum6, Bnum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  have h1 := congrFun (congrFun hadj Y) Z
  rw [Matrix.map_apply, Matrix.map_apply] at h1
  rw [map_mul, map_mul, map_mul, map_mul, h1, a6U_gamma6, a6U_gamma6, algebraMap_gammaPolyU,
    algebraMap_gammaPolyU]
  rfl

theorem coeff_zq_pow_ratU (j m : ℕ) :
    PowerSeries.coeff j (zq (RatFunc 𝔽) ^ m) =
      algebraMap ℚ (RatFunc 𝔽) (PowerSeries.coeff j (zq ℚ ^ m)) := by
  rw [← map_zq (algebraMap ℚ (RatFunc 𝔽)), ← map_pow, PowerSeries.coeff_map]

end Field

/-- `ℬ_m det G_N ∈ ℚ[c,Δ,Δ_i]` for `m ≤ N`, over every field. -/
theorem isPolyFamU_Bsph_det (hK : Cited_KacDeterminant) {m N : ℕ} (h : m ≤ N) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      Bsph c Δe m * algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det := by
  obtain ⟨q, hq⟩ := det6_dvd hK h
  refine ⟨Bnum6 m * q, ?_⟩
  intro 𝔽 _ _ c Δe
  have hN := a6U_det6 c Δe N
  have hm := a6U_det6 c Δe m
  rw [hq, map_mul, hm] at hN
  have hD : algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c m).det ≠ 0 := by
    intro h0
    exact gramPoly_det_ne_zero c m
      ((map_eq_zero_iff _ (IsFractionRing.injective 𝔽[X] (RatFunc 𝔽))).mp h0)
  show Bsph c Δe m * _ = a6U c Δe (Bnum6 m * q)
  rw [map_mul, a6U_Bnum6, ← hN, Bsph]
  field_simp

/-- `H_N det G_N ∈ ℚ[c,Δ,Δ_1,…,Δ_4]`, with one polynomial for all fields of characteristic
zero. -/
theorem isPolyFamU_Hsph_det (hK : Cited_KacDeterminant) (N : ℕ) :
    IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      Hsph c Δe N * algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det := by
  have hBz : ∀ j ≤ N, IsPolyFamU fun (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
      PowerSeries.coeff j (BzSeries c Δe) * algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det := by
    intro j hj
    obtain ⟨Q, hQ⟩ := IsPolyFamU.sum (Finset.range (j + 1))
      (F := fun m (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
        (Bsph c Δe m * algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det) *
        algebraMap ℚ (RatFunc 𝔽) (PowerSeries.coeff j (zq ℚ ^ m)))
      fun m hm => (isPolyFamU_Bsph_det hK (by have := Finset.mem_range.mp hm; omega)).mul
        (IsPolyFamU.const _)
    refine ⟨Q, ?_⟩
    intro 𝔽 _ _ c Δe
    rw [← hQ 𝔽 c Δe]
    beta_reduce
    unfold BzSeries
    rw [PowerSeries.coeff_mk, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_zq_pow_ratU]
    ring
  obtain ⟨Q, hQ⟩ := (IsPolyFamU.const (1 / 16 ^ N)).mul
    (IsPolyFamU.sum (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ))
      (F := fun p (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] c Δe =>
        PowerSeries.coeff p.1 (PhiTilde c Δe)⁻¹ *
        (PowerSeries.coeff p.2 (BzSeries c Δe) *
          algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det))
      fun p hp => (isPolyFamU_PhiTilde_inv p.1).mul
        (hBz p.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega)))
  refine ⟨Q, ?_⟩
  intro 𝔽 _ _ c Δe
  have e : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      PowerSeries.coeff p.1 (PhiTilde c Δe)⁻¹ * PowerSeries.coeff p.2 (BzSeries c Δe)) *
        algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det =
      ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        PowerSeries.coeff p.1 (PhiTilde c Δe)⁻¹ *
        (PowerSeries.coeff p.2 (BzSeries c Δe) *
          algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  have h16 : algebraMap ℚ (RatFunc 𝔽) (1 / 16 ^ N) = 1 / 16 ^ N := by
    simp
  rw [← hQ 𝔽 c Δe]
  beta_reduce
  rw [← e, h16, Hsph, Hseries, PowerSeries.coeff_mul]
  ring

end Virasoro.Sphere
