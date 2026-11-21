import Virasoro.Sphere.Proofs.Sec3Density
import Virasoro.Sphere.Proofs.Sec3Dvd
import Virasoro.Sphere.Proofs.Sec4Imported
import Virasoro.Proofs.Naturality
import Virasoro.Proofs.GramDegree

/-!
# `ℬ_m det G_N` is a polynomial over `ℚ` in `(c,Δ,Δ_i)` for `m ≤ N`

sphere/paper.tex l.495–497: since `det G_m ∣ det G_N` for `m ≤ N`, the product `ℬ_m det G_N` is
given by one polynomial in `ℚ[c,Δ,Δ_1,…,Δ_4]`.  The division is carried out in
`ℚ[c,Δ_1,…,Δ_4][Δ]`, where `det G_m` has the constant leading coefficient `K_m`; the remainder
vanishes at every complex point by the Kac determinant formula.
-/

namespace Virasoro.Sphere

open Polynomial

/-- `ℚ[c,Δ,Δ₁,…,Δ₄]`. -/
abbrev R6 : Type := MvPolynomial (Fin 6) ℚ

/-- Evaluation at the point `(c,Δ,Δ₁,…,Δ₄)` of `ℂ(Δ)⁶`. -/
noncomputable def a6 (c : ℂ) (Δe : Fin 4 → ℂ) : R6 →+* RatFunc ℂ :=
  (MvPolynomial.aeval (vec6 c Δe)).toRingHom

theorem a6_apply (c : ℂ) (Δe : Fin 4 → ℂ) (Q : R6) :
    a6 c Δe Q = MvPolynomial.aeval (vec6 c Δe) Q := rfl

theorem a6_X (c : ℂ) (Δe : Fin 4 → ℂ) (i : Fin 6) : a6 c Δe (MvPolynomial.X i) = vec6 c Δe i := by
  rw [a6_apply, MvPolynomial.aeval_X]

/-- The Shapovalov matrix over `ℚ[c,Δ,Δ_i]`. -/
noncomputable def gram6 (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) R6 :=
  gram (MvPolynomial.X 0) (MvPolynomial.X 1) N

noncomputable def det6 (N : ℕ) : R6 := (gram6 N).det

theorem a6_gram6 (c : ℂ) (Δe : Fin 4 → ℂ) (N : ℕ) :
    (gram6 N).map (a6 c Δe) = (gramPoly c N).map (algebraMap ℂ[X] (RatFunc ℂ)) := by
  rw [gram6, ← gram_map (a6 c Δe), gramPoly, ← gram_map (algebraMap ℂ[X] (RatFunc ℂ)), a6_X, a6_X,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rfl

theorem a6_det6 (c : ℂ) (Δe : Fin 4 → ℂ) (N : ℕ) :
    a6 c Δe (det6 N) = algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det := by
  rw [det6, RingHom.map_det, RingHom.mapMatrix_apply, a6_gram6, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]

theorem tau_det6_map (c : ℂ) (Δe : Fin 4 → ℂ) (N : ℕ) :
    (tau (det6 N)).map (ev5 c Δe) = (gramPoly c N).det := by
  apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
  rw [← aeval_vec6, ← a6_apply, a6_det6]

/-! ### Polynomials vanishing at every complex point -/

theorem PA_eq_zero (p : PA) (h : ∀ (c : ℂ) (Δe : Fin 4 → ℂ), ev5 c Δe p = 0) : p = 0 := by
  apply MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  rw [map_zero]
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have h1 := h (x 0) (fun i => x i.succ)
  have hpt : pt5 (x 0) (fun i => x i.succ) = x := by
    funext i
    fin_cases i <;> rfl
  rw [ev5, hpt] at h1
  rw [MvPolynomial.eval_map]
  exact h1

theorem polyX_eq_zero (U : PA[X]) (h : ∀ (c : ℂ) (Δe : Fin 4 → ℂ), U.map (ev5 c Δe) = 0) :
    U = 0 := by
  apply Polynomial.ext
  intro d
  rw [coeff_zero]
  refine PA_eq_zero _ fun c Δe => ?_
  rw [← coeff_map, h, coeff_zero]

/-! ### The leading coefficient of `det G_N` -/

/-- `K_N = ∏_{|Y|=N} (coefficient of Δ^{ℓ(Y)} in ⟨Δ|L_Y L_{-Y}|Δ⟩)`. -/
def KN (N : ℕ) : ℕ := ∏ Y : Nat.Partition N, topNat Y.word Y.word

theorem KN_ne_zero (N : ℕ) : KN N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun Y _ => (topNat_self_pos Y.word (word_pos Y)).ne'

theorem gramPoly_det_coeff_top (c : ℂ) (N : ℕ) :
    (gramPoly c N).det.coeff (dN N) = (KN N : ℂ) := by
  rw [dN, det_coeff_top (gramPoly c N) (fun Y => Y.word.length)]
  · rw [KN, Nat.cast_prod]
    refine Finset.prod_congr rfl fun Y _ => ?_
    have h := coeff_gramWord_top c Y.word Y.word (word_pos Y) rfl
    simp only [gramPoly, gram, Matrix.of_apply]
    rw [h, topFun_eq_topNat]
  · intro Y Y'
    exact natDegree_gramWord_le c Y.word Y'.word (word_pos Y)
  · intro Y Y' hne hlen
    have h := coeff_gramWord_top c Y.word Y'.word (word_pos Y) hlen
    simp only [gramPoly, gram, Matrix.of_apply]
    rw [h, topFun_eq_topNat, topNat_eq_zero_of_not_perm hlen, Nat.cast_zero]
    intro hperm
    exact hne (word_injective hperm).symm

/-- `det G_N` in `ℚ[c,Δ_i][Δ]`. -/
noncomputable def DU (N : ℕ) : PA[X] := tau (det6 N)

theorem DU_coeff_top (m : ℕ) : (DU m).coeff (dN m) = (KN m : PA) := by
  refine sub_eq_zero.mp (PA_eq_zero _ fun c Δe => ?_)
  rw [map_sub, ← coeff_map, DU, tau_det6_map, gramPoly_det_coeff_top, map_natCast, sub_self]

theorem DU_natDegree_le (m : ℕ) : (DU m).natDegree ≤ dN m := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro d hd
  refine PA_eq_zero _ fun c Δe => ?_
  rw [← coeff_map, DU, tau_det6_map]
  exact coeff_eq_zero_of_natDegree_lt (by rw [gramPoly_det_natDegree]; exact hd)

/-- `det G_m / K_m`, monic in `Δ`. -/
noncomputable def DUmonic (m : ℕ) : PA[X] := C (MvPolynomial.C (1 / (KN m : ℚ))) * DU m

theorem DUmonic_monic (m : ℕ) : (DUmonic m).Monic := by
  refine monic_of_natDegree_le_of_coeff_eq_one (dN m)
    ((natDegree_C_mul_le _ _).trans (DU_natDegree_le m)) ?_
  rw [DUmonic, coeff_C_mul, DU_coeff_top, ← map_natCast (MvPolynomial.C (σ := Fin 5) (R := ℚ)),
    ← map_mul, one_div_mul_cancel (Nat.cast_ne_zero.mpr (KN_ne_zero m)), map_one]

theorem DU_dvd (hK : Cited_KacDeterminant) {m N : ℕ} (h : m ≤ N) : DU m ∣ DU N := by
  have hM := DUmonic_monic m
  have hrem : DU N %ₘ DUmonic m = 0 := by
    refine polyX_eq_zero _ fun c Δe => ?_
    rw [map_modByMonic _ hM, modByMonic_eq_zero_iff_dvd (hM.map _), DUmonic, Polynomial.map_mul,
      map_C, DU, DU, tau_det6_map, tau_det6_map]
    have hk : ev5 c Δe (MvPolynomial.C (1 / (KN m : ℚ))) ≠ 0 := by
      have : ev5 c Δe (MvPolynomial.C (1 / (KN m : ℚ))) = 1 / (KN m : ℂ) := by
        simp [ev5]
      rw [this]
      exact one_div_ne_zero (Nat.cast_ne_zero.mpr (KN_ne_zero m))
    exact (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hk)).mul_left_dvd.mpr (gramPoly_det_dvd hK c h)
  have hdiv := modByMonic_add_div (DU N) (DUmonic m)
  rw [hrem, zero_add] at hdiv
  refine ⟨C (MvPolynomial.C (1 / (KN m : ℚ))) * (DU N /ₘ DUmonic m), ?_⟩
  have key : ∀ Qq : PA[X],
      DUmonic m * Qq = DU m * (C (MvPolynomial.C (1 / (KN m : ℚ))) * Qq) := by
    intro Qq
    rw [DUmonic]
    ring
  exact hdiv.symm.trans (key _)

/-! ### Back to `ℚ[c,Δ,Δ_i]` -/

/-- `ℚ[c,Δ₁,…,Δ₄][Δ] → ℚ[c,Δ,Δ₁,…,Δ₄]`. -/
noncomputable def sigma : PA[X] →+* R6 :=
  eval₂RingHom (MvPolynomial.aeval (![MvPolynomial.X 0, MvPolynomial.X 2, MvPolynomial.X 3,
    MvPolynomial.X 4, MvPolynomial.X 5] : Fin 5 → R6)).toRingHom (MvPolynomial.X 1)

theorem sigma_tau (Q : R6) : sigma (tau Q) = Q := by
  have h : sigma.comp tau = RingHom.id R6 := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tau, sigma]
    · intro i
      fin_cases i <;> simp [tau, sigma]
  exact DFunLike.congr_fun h Q

theorem det6_dvd (hK : Cited_KacDeterminant) {m N : ℕ} (h : m ≤ N) : det6 m ∣ det6 N := by
  obtain ⟨q, hq⟩ := DU_dvd hK h
  refine ⟨sigma q, ?_⟩
  calc det6 N = sigma (tau (det6 N)) := (sigma_tau _).symm
    _ = sigma (tau (det6 m) * q) := by
      have hq' : tau (det6 N) = tau (det6 m) * q := hq
      rw [hq']
    _ = det6 m * sigma q := by rw [map_mul, sigma_tau]

/-! ### The numerator of `ℬ_m` -/

/-- `γ_w(Δ;Δ_a,Δ_b)` over `ℚ[c,Δ,Δ_i]`, the external weights being the variables `i`, `j`. -/
noncomputable def gamma6 (i j : Fin 6) (w : List ℕ) : R6 :=
  gammaY (MvPolynomial.X 1) (MvPolynomial.X i) (MvPolynomial.X j) w

theorem a6_gamma6 (c : ℂ) (Δe : Fin 4 → ℂ) (i j : Fin 6) (w : List ℕ) :
    a6 c Δe (gamma6 i j w) = gammaY RatFunc.X (vec6 c Δe i) (vec6 c Δe j) w := by
  rw [gamma6, map_gammaY, a6_X, a6_X, a6_X]
  rfl

theorem algebraMap_gammaPoly (Δa Δb : ℂ) (N : ℕ) (Y : Nat.Partition N) :
    algebraMap ℂ[X] (RatFunc ℂ) (gammaPoly Δa Δb N Y) =
      gammaY RatFunc.X (RatFunc.C Δa) (RatFunc.C Δb) Y.word := by
  rw [gammaPoly, map_gammaY, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_C]

noncomputable def Bnum6 (m : ℕ) : R6 :=
  ∑ Y : Nat.Partition m, ∑ Z : Nat.Partition m,
    gamma6 5 4 Y.word * (gram6 m).adjugate Y Z * gamma6 2 3 Z.word

theorem a6_Bnum6 (c : ℂ) (Δe : Fin 4 → ℂ) (m : ℕ) :
    a6 c Δe (Bnum6 m) = algebraMap ℂ[X] (RatFunc ℂ) (Bnum c Δe m) := by
  have hadj : (gram6 m).adjugate.map (a6 c Δe) =
      (gramPoly c m).adjugate.map (algebraMap ℂ[X] (RatFunc ℂ)) := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, a6_gram6,
      ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate, RingHom.mapMatrix_apply]
  rw [Bnum6, Bnum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun Z _ => ?_
  have h1 := congrFun (congrFun hadj Y) Z
  rw [Matrix.map_apply, Matrix.map_apply] at h1
  rw [map_mul, map_mul, map_mul, map_mul, h1, a6_gamma6, a6_gamma6, algebraMap_gammaPoly,
    algebraMap_gammaPoly]
  rfl

/-- `ℬ_m det G_N ∈ ℚ[c,Δ,Δ_i]` for `m ≤ N`. -/
theorem isPolyFam_Bsph_det (hK : Cited_KacDeterminant) {m N : ℕ} (h : m ≤ N) :
    IsPolyFam fun c Δe => Bsph c Δe m * algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det := by
  obtain ⟨q, hq⟩ := det6_dvd hK h
  refine ⟨Bnum6 m * q, fun c Δe => ?_⟩
  have hN := a6_det6 c Δe N
  have hm := a6_det6 c Δe m
  rw [hq, map_mul, hm] at hN
  have hD : algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c m).det ≠ 0 := by
    intro h0
    exact gramPoly_det_ne_zero c m
      ((map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))).mp h0)
  show Bsph c Δe m * _ = a6 c Δe (Bnum6 m * q)
  rw [map_mul, a6_Bnum6, ← hN, Bsph]
  field_simp

end Virasoro.Sphere
