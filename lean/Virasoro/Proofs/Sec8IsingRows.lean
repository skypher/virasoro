import Virasoro.Proofs.Sec8IsingPoles
import Virasoro.Proofs.Sec8Theta7
import Virasoro.Proofs.Sec9Leading
import Virasoro.Proofs.Sec5TopCoeff
import Virasoro.Proofs.Sec5TwoStep
import Virasoro.Proofs.Singular
import Virasoro.Proofs.Family
import Virasoro.Proofs.PairingConstr

/-!
# Proposition 8.1 of `paper.tex` at 70bac53: the singular vectors at the levels `7` and `10`

The singular vector that starts the second Jantzen layer is `ξ₇ = φ₅ ξ₂` at `λ = 1/2` and
`χ₁₀ = ψ₈ χ₂` at `λ = 1/16`.  Its torus norm factorizes by Lemma 5.5 into the torus norms of
the two factors, which are `𝒫_{R,S}(b₀,d)` by Proposition 6.2.
-/

namespace Virasoro

open Verma Module Polynomial

/-- Lemma 5.5 summed over the coordinates `q` of a level-`m` operator: the torus norm of
`(∑_Y q_Y L_{-Y}) χ` is the torus norm of `χ` times the torus form of `q` at `h + ℓ`. -/
theorem pairing_coordOp (c h d : ℂ) {ℓ m : ℕ} {χ : Verma ℂ c h} (hχ : IsSingular χ ℓ)
    (q : Nat.Partition m → ℂ) :
    pairing c h d (coordOp c q • χ) (coordOp c q • χ) =
      pairing c h d χ χ * torusForm c (h + (ℓ : ℂ)) d m q q := by
  have hf := lem_singular_factorization c h d _ (isPrimaryPairing_pairing (c := c) (h := h) d)
    χ ℓ hχ m
  unfold coordOp
  simp only [Finset.sum_smul, smul_assoc, map_sum, LinearMap.sum_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul, hf, torusForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => ?_
  ring

/-- `𝒫_{r,s}(b,d)` over `ℂ(d)`, with `d` the indeterminate, is the image of the polynomial
`𝒫_{r,s}(b,·)`. -/
theorem genP_Kd_poly (r s : ℕ) (b : ℂ) :
    genP r s (RatFunc.C b : Kd) dvar = algebraMap ℂ[X] Kd (genPpoly r s b) := by
  unfold genP genPpoly lamSq
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [map_mul, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_div₀, map_pow,
    map_add, map_inv₀, map_natCast, map_ofNat]
  ring

theorem genP_Kd {r s : ℕ} {Q : ℂ[X]} (h : ∀ d : ℂ, genP r s b0 d = Q.eval d) :
    genP r s (RatFunc.C b0 : Kd) dvar = algebraMap ℂ[X] Kd Q := by
  rw [genP_Kd_poly]
  congr 1
  exact Polynomial.funext fun d => by rw [genPpoly_eval, h d]

/-- A vector of `K₂` lies in `J²` and its second Jantzen norm is the second crossing form. -/
theorem jform_two_of_ker2 {c h : ℂ} {N : ℕ} {x v₁ : Nat.Partition N → ℂ}
    (hx : x ∈ ker2 (gramLocal c h N))
    (hv₁ : (coeffMat 0 (gramLocal c h N)).mulVec v₁ = -(coeffMat 1 (gramLocal c h N)).mulVec x) :
    jform c h N 2 x x = cross2 (gramLocal c h N) x x v₁ := by
  have hl : x ∈ jantzenLayer c h N 2 := by
    rw [jantzenLayer_eq_layer, ← ker2_eq_layer (gramLocal_isSymm c h N)]
    exact hx
  exact jform_two c h hl hl hv₁

/-- The torus norm of `(St.toOp s) χ` for a singular vector `χ = St.toVerma t` of level `ℓ`. -/
theorem torusForm_composite {h : ℂ} (d : ℂ) {ℓ m : ℕ} (s t x : List (List ℕ × ℚ))
    (hs : IsLevelSt m s) (ht : IsLevelSt ℓ t) (hx : IsLevelSt (ℓ + m) x)
    (hχ : IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := h) (mapSt qC t)) ℓ)
    (hprod : St.toOp (1 / 2 : ℂ) (mapSt qC s) • St.toVerma (c := (1 / 2 : ℂ)) (h := h) (mapSt qC t)
      = St.toVerma (mapSt qC x)) :
    torusForm (1 / 2 : ℂ) h d (ℓ + m) (St.coords (ℓ + m) (mapSt qC x))
        (St.coords (ℓ + m) (mapSt qC x)) =
      torusForm (1 / 2 : ℂ) h d ℓ (St.coords ℓ (mapSt qC t)) (St.coords ℓ (mapSt qC t)) *
        torusForm (1 / 2 : ℂ) (h + (ℓ : ℂ)) d m (St.coords m (mapSt qC s))
          (St.coords m (mapSt qC s)) := by
  have hT := isPrimaryPairing_pairing (c := (1 / 2 : ℂ)) (h := h) d
  rw [← primary_pbwCoord hT (ℓ + m), ← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ hx), ← hprod,
    ← coordOp_coords _ (isLevelSt_mapSt _ hs), pairing_coordOp _ _ _ hχ,
    toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ ht), primary_pbwCoord hT ℓ]

theorem isLevel_xi2Q : IsLevelSt 2 xi2Q := by unfold IsLevelSt PosWord; decide

/-- The normalized singular vector `ξ₇ = φ₅ ξ₂` of level `7` in `M(1/2,1/2)` and its torus norm
`𝒫_{2,1}(b₀,d) 𝒫_{1,5}(b₀,d)` (Lemma 5.5 and Proposition 6.2). -/
theorem vec_seven (hH : Cited_HJSNormalizations) :
    St.coords 7 (mapSt qC x7Q) (onesPartition 7) = 1 ∧
    IsSingular (pbwCoord (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) 7
      (St.coords 7 (mapSt qC x7Q))) 7 ∧
    ∀ d : ℂ, torusForm (1 / 2 : ℂ) (1 / 2) d 7 (St.coords 7 (mapSt qC x7Q))
      (St.coords 7 (mapSt qC x7Q)) = genP 2 1 b0 d * genP 1 5 b0 d := by
  refine ⟨coords_one_of _ (by decide +kernel), ?_, fun d => ?_⟩
  · rw [← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_x7Q)]; exact x7_singular
  · have hξ2 : IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) (mapSt qC xi2Q)) 2 := by
      rw [← xi2_eq_mapSt]; exact xi2_singular'
    have hprod : St.toOp (1 / 2 : ℂ) (mapSt qC phi5Q) •
        St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 2 : ℂ)) (mapSt qC xi2Q)
          = St.toVerma (mapSt qC x7Q) := by
      rw [← phi5_eq_mapSt, ← xi2_eq_mapSt]; exact xi7_eq_x7
    have h := torusForm_composite d phi5Q xi2Q x7Q isLevel_phi5Q isLevel_xi2Q isLevel_x7Q hξ2 hprod
    have hid2 := identities_at_b0 hH 2 1 (by norm_num) (by norm_num) (1 / 2 : ℂ)
      (by rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]) levelData_2
      (detC_ne (1 / 2) _ (1 / 2 : ℂ) (by simp [map_div₀]) detB_21 (by norm_num))
      (St.coords 2 (mapSt qC xi2Q)) (coords_one_of _ (by decide +kernel))
      (by rw [← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_xi2Q)]; exact hξ2)
    have hφ5 : IsSingular (pbwCoord (c := (1 / 2 : ℂ)) (h := (5 / 2 : ℂ)) 5
        (St.coords 5 (mapSt qC phi5Q))) 5 := by
      rw [← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_phi5Q), ← phi5_eq_mapSt]
      exact phi5_singular
    have hid5 := identities_at_b0 hH 1 5 (by norm_num) (by norm_num) (5 / 2 : ℂ)
      (by rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]) levelData_5
      (detC_ne (5 / 2) _ (5 / 2 : ℂ) (by simp [map_div₀]) detB_15 (by norm_num))
      (St.coords 5 (mapSt qC phi5Q)) (coords_one_of _ (by decide +kernel)) hφ5
    rw [show ((1 / 2 : ℂ) + ((2 : ℕ) : ℂ)) = 5 / 2 by norm_num] at h
    rw [← hid2.2 d, ← hid5.2 d]
    exact h

theorem isLevel_chi2Q : IsLevelSt 2 chi2Q := by unfold IsLevelSt PosWord; decide

set_option maxHeartbeats 4000000 in
theorem x10_singular :
    IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) (mapSt qC x10Q)) 10 := by
  refine isSingular_ofQ 60 (1 / 2) (1 / 16) (by simp [map_div₀]) (by simp [map_div₀]) x10Q
    isLevel_x10Q (coords_ne_of_ones _ (by decide +kernel)) fun n h1 h2 => ?_
  interval_cases n <;> decide +kernel

set_option maxRecDepth 100000 in
theorem x10_ones : St.coords 10 (mapSt qC x10Q) (onesPartition 10) = 1 :=
  coords_one_of _ (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The normalized singular vector `χ₁₀ = ψ₈ χ₂` of level `10` in `M(1/2,1/16)` and its torus
norm `𝒫_{1,2}(b₀,d) 𝒫_{4,2}(b₀,d)` (Lemma 5.5 and Proposition 6.2). -/
theorem vec_ten (hH : Cited_HJSNormalizations) :
    St.coords 10 (mapSt qC x10Q) (onesPartition 10) = 1 ∧
    IsSingular (pbwCoord (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) 10
      (St.coords 10 (mapSt qC x10Q))) 10 ∧
    ∀ d : ℂ, torusForm (1 / 2 : ℂ) (1 / 16) d 10 (St.coords 10 (mapSt qC x10Q))
      (St.coords 10 (mapSt qC x10Q)) = genP 1 2 b0 d * genP 4 2 b0 d := by
  refine ⟨x10_ones, ?_, fun d => ?_⟩
  · rw [← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_x10Q)]; exact x10_singular
  · have hχ2 : IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) (mapSt qC chi2Q)) 2 := by
      rw [← chi2_eq_mapSt, chi2_eq]; exact chi2_singular ℂ
    have hprod : St.toOp (1 / 2 : ℂ) (mapSt qC psi8Q) •
        St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) (mapSt qC chi2Q)
          = St.toVerma (mapSt qC x10Q) := by
      rw [← toVerma_opN_of 60 (1 / 2) (1 / 16) (by simp [map_div₀]) (by simp [map_div₀]),
        toVerma_mapSt_perm opN_psi8_chi2]
    have h := torusForm_composite d psi8Q chi2Q x10Q isLevel_psi8Q isLevel_chi2Q isLevel_x10Q
      hχ2 hprod
    have hid2 := identities_at_b0 hH 1 2 (by norm_num) (by norm_num) (1 / 16 : ℂ)
      (by rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]) levelData_2
      (detC_ne (1 / 16) _ (1 / 16 : ℂ) (by simp [map_div₀]) detB_12 (by norm_num))
      (St.coords 2 (mapSt qC chi2Q)) (coords_one_of _ (by decide +kernel))
      (by rw [← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_chi2Q)]; exact hχ2)
    have hψ8 : IsSingular (pbwCoord (c := (1 / 2 : ℂ)) (h := (33 / 16 : ℂ)) 8
        (St.coords 8 (mapSt qC psi8Q))) 8 := by
      rw [← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_psi8Q)]; exact psi8_singular
    have hid8 := identities_at_b0 hH 4 2 (by norm_num) (by norm_num) (33 / 16 : ℂ)
      (by rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]) levelData_8
      (detC_ne (33 / 16) _ (33 / 16 : ℂ) (by simp [map_div₀]) detB_42 (by norm_num))
      (St.coords 8 (mapSt qC psi8Q)) (coords_one_of _ (by decide +kernel)) hψ8
    rw [show ((1 / 16 : ℂ) + ((2 : ℕ) : ℂ)) = 33 / 16 by norm_num] at h
    rw [← hid2.2 d, ← hid8.2 d]
    exact h

end Virasoro
