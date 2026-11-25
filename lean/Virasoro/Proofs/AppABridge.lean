import Virasoro.Proofs.AppAModeCount
import Virasoro.Proofs.Sec6H13Values

/-!
# Lemma A.1 of `paper.tex` and the rescaled matrices `GsM`, `RsM`

The matrices `G₁`, `ρ̃` of `Stmt_lem_mode_count` are tied to the rescaled Gram and torus matrices
`GsM`, `RsM` over `ℚ[t][Y]` through the injectivity of `ℚ[t,Y,ζ] → ℚ(t,Y,ζ)`
(`evtYz_Gt2`, `evtYz_rhot3`).  This gives the two facts of the lemma that its consumers use in
`ℚ[t][Y]`: `G̃(0,Y) = D₀(Y)` (`GsM_ev0_of_modeCount`) and that `ρ̃(0,Y)` is the same at
`ζ = −1` and `ζ = 2` (`RsM_ev0_of_modeCount`).
-/

namespace Virasoro

open Polynomial

/-! ### The matrices of Lemma A.1 and `G̃`, `ρ̃` in `ℚ[t][Y]` -/

theorem thetaMv_tS : thetaMv tS = MvPolynomial.X 0 := by simp [thetaMv, tS]

theorem thetaMv_X : thetaMv (X : PS) = MvPolynomial.X 1 := by simp [thetaMv]

theorem thetaMv_cS : thetaMv cS = ct2 := by
  simp only [thetaMv, cS, ct2, coe_eval₂RingHom, eval₂_C, map_add, map_mul, map_pow,
    AlgHom.coe_toRingHom, aeval_X]
  rw [map_ofNat (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)) 6,
    map_ofNat (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)) 13]

theorem thetaMv_GsM (n : ℕ) (Z Z' : Nat.Partition n) : thetaMv (GsM n Z Z') = Gt2 n Z Z' := by
  simp only [GsM, Matrix.of_apply]
  rw [← gramT_map, thetaMv_tS, thetaMv_cS, thetaMv_X]
  rfl

/-- `ζ_ν`: `ζ = −1` for `ν = 0` and `ζ = 2` for `ν = 1`. -/
noncomputable def zetaVal (ν : Fin 2) : ℚ := if ν = 0 then -1 else 2

/-- `t ↦ t`, `Y ↦ Y`, `ζ ↦ ζ_ν`. -/
noncomputable def specZ (ν : Fin 2) : MvPolynomial (Fin 3) ℚ →+* MvPolynomial (Fin 2) ℚ :=
  (MvPolynomial.aeval (R := ℚ) (σ := Fin 3)
    (![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C (zetaVal ν)] :
      Fin 3 → MvPolynomial (Fin 2) ℚ)).toRingHom

theorem specZ_X0 (ν : Fin 2) : specZ ν (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [specZ]

theorem specZ_X2 (ν : Fin 2) : specZ ν (MvPolynomial.X 2) = MvPolynomial.C (zetaVal ν) := by
  simp [specZ]

theorem specZ_ct3 (ν : Fin 2) : specZ ν ct3 = ct2 := by
  simp only [ct3, ct2, map_add, map_mul, map_pow, specZ_X0]
  rw [map_ofNat (specZ ν) 6, map_ofNat (specZ ν) 13]

theorem specZ_dt3 (ν : Fin 2) : specZ ν dt3 = thetaMv (dS ν) := by
  have ha : aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) (2 : ℚ[X]) = 2 :=
    map_ofNat (aeval (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ)) 2
  have hC : (MvPolynomial.C (2 : ℚ) : MvPolynomial (Fin 2) ℚ) = 2 := map_ofNat _ 2
  simp only [dt3, map_add, map_mul, map_neg, specZ_X0, specZ_X2]
  rw [map_ofNat (specZ ν) 2]
  unfold dS zetaVal
  split_ifs <;> simp [thetaMv, ha, hC] <;> ring

/-- `ρ̃` at `ζ = ζ_ν` is `RsM ν`. -/
theorem thetaMv_RsM (ν : Fin 2) (n : ℕ) (Z Z' : Nat.Partition n) :
    thetaMv (RsM ν n Z Z') = specZ ν (rhot3 n Z Z') := by
  simp only [RsM, Matrix.of_apply, rhot3]
  rw [← torusWordT_map, ← torusWordT_map, thetaMv_tS, thetaMv_cS, thetaMv_X, specZ_ct3,
    specZ_dt3]
  simp [specZ]

theorem evtYz_rename_injective :
    Function.Injective fun p : MvPolynomial (Fin 2) ℚ =>
      evtYz (MvPolynomial.rename Fin.castSucc p) :=
  (IsFractionRing.injective (MvPolynomial (Fin 3) ℚ) KtYz).comp
    (MvPolynomial.rename_injective _ (Fin.castSucc_injective _))

/-- `G̃(0,Y) = D₀(Y)`, from Lemma A.1. -/
theorem GsM_ev0_of_modeCount (h : Stmt_lem_mode_count) (n : ℕ) :
    (GsM n).map ev0 = Matrix.diagonal fun Y : Nat.Partition n => D0 Y := by
  obtain ⟨G1, ρt, hA⟩ := h n
  dsimp only at hA
  obtain ⟨-, -, hG, -, -⟩ := hA
  ext Z Z'
  have e : Gt2 n Z Z' = (if Z = Z' then MvPolynomial.C (appKZ Z : ℚ) *
      MvPolynomial.X 1 ^ Z.parts.card else 0) + MvPolynomial.X 0 * G1 Z Z' :=
    evtYz_rename_injective ((evtYz_Gt2 n Z Z').trans (hG Z Z').symm)
  rw [Matrix.map_apply, ← aeval0_thetaMv, thetaMv_GsM, e, map_add, map_mul, MvPolynomial.aeval_X]
  simp only [Matrix.cons_val_zero, zero_mul, add_zero]
  by_cases hZ : Z = Z'
  · subst hZ
    rw [if_pos rfl, Matrix.diagonal_apply_eq, D0, topNat_word_eq_appKZ, word_length_eq_card]
    simp
  · rw [if_neg hZ, Matrix.diagonal_apply_ne _ hZ, map_zero]

/-- `ρ̃(0,Y;ζ)` does not depend on `ζ`, from Lemma A.1: the two values `ζ = −1, 2` agree. -/
theorem RsM_ev0_of_modeCount (h : Stmt_lem_mode_count) (n : ℕ) (Z Z' : Nat.Partition n) :
    ev0 (RsM 1 n Z Z') = ev0 (RsM 0 n Z Z') := by
  obtain ⟨G1, ρt, hA⟩ := h n
  dsimp only at hA
  obtain ⟨-, -, -, hρ, h0⟩ := hA
  have e : ρt Z Z' = rhot3 n Z Z' :=
    IsFractionRing.injective (MvPolynomial (Fin 3) ℚ) KtYz ((hρ Z Z').trans (evtYz_rhot3 n Z Z').symm)
  have key : ∀ ν : Fin 2, ev0 (RsM ν n Z Z') =
      MvPolynomial.aeval (![0, X, 0] : Fin 3 → ℚ[X]) (ρt Z Z') := by
    intro ν
    let φ : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] ℚ[X] :=
      MvPolynomial.aeval (![0, X, C (zetaVal ν)] : Fin 3 → ℚ[X])
    have c1 : ((MvPolynomial.aeval (![0, X] : Fin 2 → ℚ[X])).comp
        (MvPolynomial.aeval (R := ℚ) (σ := Fin 3)
          (![MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.C (zetaVal ν)] :
            Fin 3 → MvPolynomial (Fin 2) ℚ))) = φ := by
      rw [MvPolynomial.comp_aeval]
      congr 1
      funext i
      fin_cases i <;> simp
    have c2 : φ.comp (MvPolynomial.aeval (![0, MvPolynomial.X 1, MvPolynomial.X 2] :
        Fin 3 → MvPolynomial (Fin 3) ℚ)) = φ := by
      rw [MvPolynomial.comp_aeval]
      congr 1
      funext i
      fin_cases i <;> simp [φ]
    have c3 : φ.comp (MvPolynomial.aeval (![0, MvPolynomial.X 1, 0] :
        Fin 3 → MvPolynomial (Fin 3) ℚ)) = MvPolynomial.aeval (![0, X, 0] : Fin 3 → ℚ[X]) := by
      rw [MvPolynomial.comp_aeval]
      congr 1
      funext i
      fin_cases i <;> simp [φ]
    rw [← aeval0_thetaMv, thetaMv_RsM, ← e]
    have d1 := AlgHom.congr_fun c1 (ρt Z Z')
    have d2 := AlgHom.congr_fun c2 (ρt Z Z')
    have d3 := AlgHom.congr_fun c3 (ρt Z Z')
    simp only [AlgHom.comp_apply] at d1 d2 d3
    rw [h0 Z Z'] at d2
    exact d1.trans (d2.symm.trans d3)
  rw [key, key]

end Virasoro
