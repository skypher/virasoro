import Virasoro.Proofs.Sec4Poly
import Virasoro.Proofs.SubringCoeff
import Virasoro.Sphere.Proofs.Sec4ConflMain

/-!
# Sphere paper Theorem 4.7, parts (i) and (ii)

`sphere/paper.tex` l.1369–1422.  Part (ii) is the confluence identity over
`K⋆ = ℂ(Δ₁,…,Δ₄)`.  Part (i): the collision moments are the principal-part coefficients of
`H_N(c⋆,Δ,Δ_i) ∈ ℚ(b⋆)[Δ₁,…,Δ₄](Δ)` at the points `λ ∈ ℚ(b⋆)`, hence lie in
`ℚ(b⋆)[Δ₁,…,Δ₄]` (l.1418–1421).
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Polynomial

/-- Part (iii) of Theorem 4.7 (sphere/paper.tex l.1385–1388, proof l.1421–1422 from equation
(2.8), l.386–396): `ℬ_N(c⋆,Δ,Δ_i)` is a polynomial of degree `N` in `Δ` plus the sum of its
principal parts at `Λ_N(b⋆)`.

Demand sheet.
- every `b⋆ ≠ 0`, every `N ≥ 1` (l.1371);
- `deg Q = N` exactly: `ℬ_N ∼ Δ^N/(2^N N!)` (l.396–397);
- the sum over the points of `Λ_N(b⋆)` (l.1387–1388). -/
def Stmt_sub_confluence_poly_part : Prop :=
  ∀ b : ℂ, b ≠ 0 → ∀ N : ℕ, 1 ≤ N →
    ∃ Q : K4[X], Q.natDegree = N ∧
      Bsph (kacC (cK b)) ΔK N =
        algebraMap K4[X] (RatFunc K4) Q + ∑ lam ∈ Lam N b, PP (Bsph (kacC (cK b)) ΔK N) (cK lam)

theorem cK_injective : Function.Injective (cK : ℂ → K4) := (algebraMap ℂ K4).injective

open Classical in
theorem Lam_cK (N : ℕ) (b : ℂ) :
    (Lam N (cK b) : Finset K4) = (Lam N b).image (fun lam : ℂ => (cK lam : K4)) := by
  unfold Lam
  rw [Finset.image_image]
  ext x
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, map_kacHL (algebraMap ℂ K4) a b⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, (map_kacHL (algebraMap ℂ K4) a b).symm⟩

theorem RgK_eq (b : ℂ) : RgK (cK b) ΔK = RgSph b := rfl

/-- Theorem 4.7 (ii). -/
theorem confluence_eq_sph (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) {b : ℂ} (hb : b ≠ 0)
    {N : ℕ} (hN : 1 ≤ N) :
    Hsph (kacC (cK b)) ΔK N =
      ∑ lam ∈ Lam N b, ∑ k ∈ Finset.Icc 1 (Mhatg (cK b) (RgSph b) N (cK lam)),
        RatFunc.C (Atildeg (cK b) (RgSph b) N (cK lam) k) /
          (RatFunc.X - RatFunc.C (cK lam)) ^ k := by
  classical
  have hbs : cK b ≠ 0 := (map_ne_zero (algebraMap ℂ K4)).2 hb
  have h := confluence_identity_sph ΔK hK hbs hN fun M hM _ =>
    germ_sph_recursion (ι := algebraMap K4 (RatFunc K4)) (cK b) ΔK hF hK hJ1 hJ2 hH hFus M hM
  rw [RgK_eq, Lam_cK, Finset.sum_image fun x _ y _ hxy => cK_injective hxy] at h
  exact h

/-! ### Part (i) -/

/-- The ring homomorphism `k[Δ₁,…,Δ₄] → ℂ(Δ₁,…,Δ₄)` for a subfield `k ⊆ ℂ`. -/
noncomputable def polyHom4 (k : Subfield ℂ) : MvPolynomial (Fin 4) ↥k →+* K4 :=
  (algebraMap (MvPolynomial (Fin 4) ℂ) K4).comp (MvPolynomial.map k.subtype)

theorem polyHom4_C (k : Subfield ℂ) (x : ↥k) : polyHom4 k (MvPolynomial.C x) = cK (x : ℂ) := by
  simp only [polyHom4, RingHom.comp_apply, MvPolynomial.map_C, Subfield.coe_subtype]
  rw [cK, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin 4) ℂ) K4]
  rfl

theorem polyHom4_X (k : Subfield ℂ) (i : Fin 4) : polyHom4 k (MvPolynomial.X i) = ΔK i := by
  simp only [polyHom4, RingHom.comp_apply, MvPolynomial.map_X]
  rfl

theorem closure_b_of_Qb2 {b x : ℂ} (h : x ∈ Qb2 b) : x ∈ Subfield.closure ({b} : Set ℂ) := by
  refine Subfield.closure_le.2 ?_ h
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact pow_mem (Subfield.subset_closure (Set.mem_singleton b)) 2

/-- Every Laurent coefficient of `H_N(c⋆,Δ,Δ_i)` at a point of `ℚ(b⋆)` lies in
`ℚ(b⋆)[Δ₁,…,Δ₄]`. -/
theorem lcoeff_Hsph_mem (hK : Cited_KacDeterminant) (b : ℂ) (hb : b ≠ 0) (N : ℕ) {lam : ℂ}
    (hlam : lam ∈ Subfield.closure ({b} : Set ℂ)) (n : ℤ) :
    lcoeff (Hsph (kacC (cK b)) ΔK N) (cK lam) n ∈
      (polyHom4 (Subfield.closure ({b} : Set ℂ))).range := by
  set k := Subfield.closure ({b} : Set ℂ) with hk
  have : CharZero ↥k := RingHom.charZero k.subtype
  let c' : ↥k := ⟨kacC b, closure_b_of_Qb2 (kacC_mem b hb)⟩
  let j₀ : ↥k →+* K4 := (algebraMap ℂ K4).comp k.subtype
  have hj₀ : ∀ x : ↥k, j₀ x = polyHom4 k (MvPolynomial.C x) := fun x => (polyHom4_C k x).symm
  have hc : kacC (cK b) = j₀ c' := (map_kacC (algebraMap ℂ K4) b).symm
  obtain ⟨Q, hQ⟩ := isPolyFamU_Hsph_det hK N
  have hQ4 := hQ K4 (kacC (cK b)) ΔK
  beta_reduce at hQ4
  have hD : algebraMap K4[X] (RatFunc K4) (gramPoly (kacC (cK b)) N).det ≠ 0 := by
    intro h0
    exact gramPoly_det_ne_zero (kacC (cK b)) N
      ((map_eq_zero_iff _ (IsFractionRing.injective K4[X] (RatFunc K4))).mp h0)
  have hH : Hsph (kacC (cK b)) ΔK N =
      algebraMap K4[X] (RatFunc K4) ((tau Q).map (ev5U (kacC (cK b)) ΔK)) /
        algebraMap K4[X] (RatFunc K4) (gramPoly (kacC (cK b)) N).det := by
    rw [eq_div_iff hD, hQ4, aeval_vec6U]
  -- numerator: coefficients in `k[Δ_i]`
  have hev : ev5U (kacC (cK b)) ΔK =
      (polyHom4 k).comp (MvPolynomial.aeval (![MvPolynomial.C c', MvPolynomial.X 0,
        MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3] :
          Fin 5 → MvPolynomial (Fin 4) ↥k)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ev5U, eq_ratCast]
      rw [polyHom4_C]
      simp
    · intro i
      fin_cases i
      · simp only [ev5U, pt5U, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X,
          RingHom.comp_apply]
        show kacC (cK b) = polyHom4 k (MvPolynomial.C c')
        rw [hc, hj₀]
      all_goals
        simp only [ev5U, pt5U, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X,
          RingHom.comp_apply]
        exact (polyHom4_X k _).symm
  have hnum : ∀ i, ((tau Q).map (ev5U (kacC (cK b)) ΔK)).coeff i ∈ (polyHom4 k).range := by
    intro i
    rw [coeff_map, hev]
    exact ⟨_, rfl⟩
  -- denominator: coefficients in `k`
  have hden : ∀ i, (gramPoly (kacC (cK b)) N).det.coeff i ∈ j₀.fieldRange := by
    intro i
    have h := map_detR (Polynomial.mapRingHom j₀) (C c') (X : (↥k)[X]) N
    simp only [coe_mapRingHom, Polynomial.map_C, Polynomial.map_X] at h
    rw [← hc] at h
    have h' : (gramPoly (kacC (cK b)) N).det = detR (C (kacC (cK b))) X N := rfl
    rw [h', ← h, Polynomial.coeff_map]
    exact ⟨_, rfl⟩
  have hsub : ∀ x ∈ j₀.fieldRange, x ∈ (polyHom4 k).range := by
    rintro x ⟨y, rfl⟩
    exact ⟨MvPolynomial.C y, (hj₀ y).symm⟩
  have hμ : cK lam ∈ j₀.fieldRange := ⟨⟨lam, hlam⟩, rfl⟩
  have := lcoeff_div_mem (polyHom4 k).range j₀.fieldRange hsub hnum hden
    (gramPoly_det_ne_zero _ N) hμ n
  rw [hH]
  exact this

/-- Theorem 4.7 (i): the collision moments lie in `ℚ(b⋆)[Δ₁,…,Δ₄]`. -/
theorem confluence_moments_sph (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) {b : ℂ} (hb : b ≠ 0)
    {N : ℕ} (hN : 1 ≤ N) {lam : ℂ} (hlam : lam ∈ Lam N b) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ Mhatg (cK b) (RgSph b) N (cK lam)) :
    ∃ P : MvPolynomial (Fin 4) ℂ, (∀ m, P.coeff m ∈ Subfield.closure ({b} : Set ℂ)) ∧
      algebraMap (MvPolynomial (Fin 4) ℂ) K4 P = Atildeg (cK b) (RgSph b) N (cK lam) k := by
  classical
  have heq := confluence_eq_sph hF hK hJ1 hJ2 hH hFus hb hN
  have hinj : Set.InjOn (fun lam : ℂ => cK lam) (Lam N b : Set ℂ) :=
    fun x _ y _ hxy => cK_injective hxy
  have hpp := ppCoeff_sum (Lam N b) (fun lam : ℂ => cK lam) hinj
    (fun lam => Mhatg (cK b) (RgSph b) N (cK lam))
    (fun lam k => Atildeg (cK b) (RgSph b) N (cK lam) k) hlam hk1
  rw [← heq, if_pos hk2] at hpp
  have hlam' : lam ∈ Subfield.closure ({b} : Set ℂ) := by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hlam
    exact closure_b_of_Qb2 (kacH_mem b hb _ _)
  obtain ⟨p, hp⟩ := lcoeff_Hsph_mem hK b hb N hlam' (-(k : ℤ))
  refine ⟨MvPolynomial.map (Subfield.closure ({b} : Set ℂ)).subtype p, fun m => ?_, ?_⟩
  · rw [MvPolynomial.coeff_map]
    exact (p.coeff m).2
  · rw [← hpp]
    exact hp

/-- Theorem 4.7 from its part (iii). -/
theorem thm_confluence_of_poly_part (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial)
    (h3 : Stmt_sub_confluence_poly_part) : Stmt_thm_confluence := by
  intro b hb N hN
  exact ⟨fun lam hlam k hk1 hk2 => confluence_moments_sph hF hK hJ1 hJ2 hH hFus hb hN hlam hk1 hk2,
    confluence_eq_sph hF hK hJ1 hJ2 hH hFus hb hN, h3 b hb N hN⟩

end Virasoro.Sphere
