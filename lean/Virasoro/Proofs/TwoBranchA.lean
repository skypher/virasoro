import Virasoro.Proofs.Reg2
import Virasoro.Proofs.GenericResidue
import Virasoro.Proofs.Sec4Thm

/-!
# Proposition 7.7, first part: the shifted coefficient on a branch

Under hypothesis (i) of Proposition 7.7 the only factor of `det G_M(c(b), Δ)` vanishing near
`(b⋆, z)` is `Δ - h_τ(b)`, with exponent one.  Hence
`U(b,Δ) = (Δ - h_τ(b)) H_M(c(b),Δ,d)` is regular at `(b⋆, z)`.
-/

namespace Virasoro

open Polynomial
open scoped LaurentSeries

variable {K : Type} [Field K] [CharZero K]

omit [CharZero K] in
theorem mapL_id (x : K⸨X⸩) : mapL (RingHom.id K) x = x := by
  ext n
  rw [mapL_coeff]
  rfl

omit [CharZero K] in
/-- `c(b⋆ + t)` is regular at `t = 0` with value `c(b⋆)`. -/
theorem regVal_kacC_germ {bs : K} (hbs : bs ≠ 0) : RegVal (kacC (bGerm bs)) (kacC bs) := by
  have hb := regVal_bGerm bs
  have hbi := hb.inv hbs
  unfold kacC
  have h1 : RegVal (1 : K⸨X⸩) 1 := by simpa using regVal_C (1 : K)
  exact h1.add ((regVal_ofNat 6).mul ((hb.add hbi).pow 2))

theorem numR_map_toLS (cp dp : PowerSeries K) (M : ℕ) :
    (numR (C cp) X (C dp) M).map toLS = numR (C (toLS cp)) X (C (toLS dp)) M := by
  rw [← coe_mapRingHom, map_numR, coe_mapRingHom, map_C, map_X, map_C]

theorem numR_map_red0 (cp dp : PowerSeries K) (M : ℕ) :
    (numR (C cp) X (C dp) M).map red0 = numR (C (red0 cp)) X (C (red0 dp)) M := by
  rw [← coe_mapRingHom, map_numR, coe_mapRingHom, map_C, map_X, map_C]

theorem detR_map_toLS (cp : PowerSeries K) (M : ℕ) :
    (detR (C cp) X M).map toLS = (gramPoly (toLS cp) M).det := by
  rw [← coe_mapRingHom, map_detR, coe_mapRingHom, map_C, map_X]
  rfl

theorem detR_map_red0 (cp : PowerSeries K) (M : ℕ) :
    (detR (C cp) X M).map red0 = (gramPoly (red0 cp) M).det := by
  rw [← coe_mapRingHom, map_detR, coe_mapRingHom, map_C, map_X]
  rfl

theorem Frat_up (cp dp : PowerSeries K) (M : ℕ) :
    Frat (toLS cp) (toLS dp) M = upHom (numR (C cp) X (C dp) M) / upHom (detR (C cp) X M) := by
  rw [upHom_apply, upHom_apply, numR_map_toLS, detR_map_toLS]
  rfl

theorem Frat_dn (cp dp : PowerSeries K) (M : ℕ) :
    Frat (red0 cp) (red0 dp) M = dnHom (numR (C cp) X (C dp) M) / dnHom (detR (C cp) X M) := by
  rw [dnHom_apply, dnHom_apply, numR_map_red0, detR_map_red0]
  rfl

/-- `G_M(c(b), z)` is invertible if `z` is no Kac weight of level at most `M`. -/
theorem gram_det_ne_of_labels (hK : Cited_KacDeterminant) {b z : K} (hb : b ≠ 0) {M : ℕ}
    (hz : ∀ g ∈ labels M, kacHL g b ≠ z) : (gram (kacC b) z M).det ≠ 0 := by
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK hb M
  rw [← gramPoly_det_eval, hdet, eval_mul, eval_C, kacProd, eval_prod]
  refine mul_ne_zero hC₀ (Finset.prod_ne_zero_iff.2 fun g hg => ?_)
  rw [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.2 (hz g hg).symm)

/-- `det G_M(c(b), h_a(b)) = 0` for a label `a` of level at most `M`. -/
theorem gram_det_eq_zero_of_label (hK : Cited_KacDeterminant) {b : K} (hb : b ≠ 0) {M : ℕ}
    {a : Label} (ha : a ∈ labels M) : (gram (kacC b) (kacHL a b) M).det = 0 := by
  obtain ⟨C₀, -, hdet⟩ := kac_det_field hK hb M
  rw [← gramPoly_det_eval, hdet, eval_mul, kacProd, eval_prod, Finset.prod_eq_zero ha, mul_zero]
  rw [eval_pow, eval_sub, eval_X, eval_C, sub_self]
  exact zero_pow Fintype.card_ne_zero

omit [CharZero K] in
/-- If `a` is the only label of level at most `M` with Kac weight `h_a(b)`, then `h_a(b)` is a
root of the Kac product of multiplicity `p(M - ℓ_a)`. -/
theorem rootMultiplicity_kacProd_unique {b : K} {M : ℕ} {a : Label} (ha : a ∈ labels M)
    (huniq : ∀ g ∈ labels M, kacHL g b = kacHL a b → g = a) :
    (kacProd b M).rootMultiplicity (kacHL a b) = Fintype.card (Nat.Partition (M - a.lvl)) := by
  classical
  have hne : kacProd b M ≠ 0 := (kacProd_monic b M).ne_zero
  have hsplit : kacProd b M
      = (X - C (kacHL a b)) ^ Fintype.card (Nat.Partition (M - a.lvl))
        * ∏ g ∈ (labels M).erase a,
            (X - C (kacHL g b)) ^ Fintype.card (Nat.Partition (M - g.lvl)) := by
    unfold kacProd
    rw [Finset.mul_prod_erase (labels M)
      (fun g => (X - C (kacHL g b)) ^ Fintype.card (Nat.Partition (M - g.lvl))) ha]
  have hnr : ¬ IsRoot (∏ g ∈ (labels M).erase a,
      (X - C (kacHL g b)) ^ Fintype.card (Nat.Partition (M - g.lvl))) (kacHL a b) := by
    rw [IsRoot, eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun g hg => ?_
    rw [eval_pow, eval_sub, eval_X, eval_C]
    refine pow_ne_zero _ (sub_ne_zero.2 fun h => ?_)
    have hg' := Finset.mem_erase.1 hg
    exact hg'.1 (huniq g hg'.2 h.symm)
  rw [hsplit] at hne ⊢
  rw [rootMultiplicity_mul hne, rootMultiplicity_X_sub_C_pow, rootMultiplicity_eq_zero hnr,
    add_zero]

/-- If `τ` has level `M` and is the only label of level at most `M` with weight `h_τ(b⋆)`, then
`(Δ - h_τ(b)) F_M(c(b),Δ,d)` is regular at `(b⋆, h_τ(b⋆))`. -/
theorem reg2_linear_mul_Frat (hK : Cited_KacDeterminant) {bs : K} (hbs : bs ≠ 0)
    (cp dp hp : PowerSeries K) (hcp : toLS cp = kacC (bGerm bs)) (hcp0 : red0 cp = kacC bs)
    {τ : Label} {M : ℕ} (hτ : τ ∈ labels M) (hτlvl : τ.lvl = M)
    (hhp : toLS hp = hG bs τ) (hhp0 : red0 hp = kacHL τ bs)
    (huniq : ∀ g ∈ labels M, kacHL g bs = kacHL τ bs → g = τ) :
    Reg2 (kacHL τ bs) ((RatFunc.X - RatFunc.C (toLS hp)) * Frat (toLS cp) (toLS dp) M)
      ((RatFunc.X - RatFunc.C (kacHL τ bs)) * Frat (red0 cp) (red0 dp) M) := by
  have hroot : (detR (C cp) X M).eval hp = 0 := by
    apply toLS_injective
    rw [← eval_map_toLS, detR_map_toLS, gramPoly_det_eval, hcp, hhp, map_zero]
    exact gram_det_eq_zero_of_label hK (bGerm_ne_zero hbs) hτ
  obtain ⟨E', hE'⟩ := dvd_iff_isRoot.2 hroot
  obtain ⟨C₀, hC₀, hdet⟩ := kac_det_field hK hbs M
  have h0 : (X - C (kacHL τ bs)) * E'.map red0 = C C₀ * kacProd bs M := by
    rw [← hdet, ← hcp0, ← detR_map_red0, hE', Polynomial.map_mul, Polynomial.map_sub, map_X,
      map_C, hhp0]
  have hE'z : (E'.map red0).eval (kacHL τ bs) ≠ 0 := by
    intro h0'
    obtain ⟨W, hW⟩ := dvd_iff_isRoot.2 h0'
    have hne : C C₀ * kacProd bs M ≠ 0 :=
      mul_ne_zero (C_ne_zero.2 hC₀) (kacProd_monic bs M).ne_zero
    have h2 : (X - C (kacHL τ bs)) ^ 2 ∣ C C₀ * kacProd bs M :=
      ⟨W, by rw [← h0, hW]; ring⟩
    have h3 := (le_rootMultiplicity_iff hne).2 h2
    rw [rootMultiplicity_mul hne, rootMultiplicity_C, zero_add,
      rootMultiplicity_kacProd_unique hτ huniq, hτlvl, Nat.sub_self] at h3
    have := Fintype.card_le_one_iff_subsingleton.2
      (inferInstance : Subsingleton (Nat.Partition 0))
    omega
  have hne1 := ratFunc_X_sub_C_ne_zero (toLS hp)
  have hne2 := ratFunc_X_sub_C_ne_zero (kacHL τ bs)
  have hu := upHom_ne_zero hE'z
  have hd := dnHom_ne_zero hE'z
  refine ⟨numR (C cp) X (C dp) M, E', hE'z, ?_, ?_⟩
  · rw [Frat_up, hE', map_mul, map_sub, upHom_X, upHom_C]
    field_simp
  · rw [Frat_dn, hE', map_mul, map_sub, dnHom_X, dnHom_C, hhp0]
    field_simp

omit [CharZero K] in
theorem regAt_X_sub_C (z μ : K) : RegAt z (RatFunc.X - RatFunc.C μ) ∧
    evalAt z (RatFunc.X - RatFunc.C μ) = z - μ := by
  have e : (RatFunc.X - RatFunc.C μ : RatFunc K) = algebraMap K[X] (RatFunc K) (X - C μ) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  rw [e]
  refine ⟨regAt_algebraMap z _, ?_⟩
  rw [evalAt_algebraMap, eval_sub, eval_X, eval_C]

omit [CharZero K] in
theorem regAt_pole {z μ : K} (hz : z ≠ μ) (r : K) :
    RegAt z (RatFunc.C r / (RatFunc.X - RatFunc.C μ)) ∧
      evalAt z (RatFunc.C r / (RatFunc.X - RatFunc.C μ)) = r / (z - μ) := by
  have e : (RatFunc.C r / (RatFunc.X - RatFunc.C μ) : RatFunc K)
      = algebraMap K[X] (RatFunc K) (C r) / algebraMap K[X] (RatFunc K) (X - C μ) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_C]
  have hq : (X - C μ : K[X]).eval z ≠ 0 := by
    rw [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.2 hz
  rw [e]
  refine ⟨regAt_div z _ hq, ?_⟩
  rw [evalAt_div z _ hq, eval_sub, eval_X, eval_C, eval_C]

omit [CharZero K] in
theorem regAt_pole_mul {z μ : K} (hz : z ≠ μ) (r s : K) :
    RegAt z (RatFunc.C r / (RatFunc.X - RatFunc.C μ) * RatFunc.C s) := by
  refine (regAt_pole hz r).1.mul ?_
  rw [← RatFunc.algebraMap_C]
  exact regAt_algebraMap z _

end Virasoro
