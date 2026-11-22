import Virasoro.Proofs.Sec6H13IntA
import Virasoro.Proofs.Sec6H13Lip

/-!
# Proposition 6.8(i): `P_M^{(ν)} ∈ ℤ[1/2][t,Y]` (paper.tex l.1261–1291)

With `G_n = B_n(q₀,2q₀−α)ᵀ D_n B_n(q₀,α)` (`TFock.gram_factor`), `M! D_n⁻¹ ∈ Mat(ℤ)` for `n ≤ M`
(Lagrange) and `det B_n(q₀,2q₀−α) det B_n(q₀,α) = ± 2^{∑ℓ(λ)} ∏ (Δ − h_{u,v})^{p(n−uv)}`, the value
`P_M^{(ν)}(t,Y)` times a unit at `𝔭` is integral, so the coefficients of `P_M^{(ν)}` are
`ℓ`-integral for every odd prime `ℓ` (`H13Local.local_integral`).
-/

namespace Virasoro

open Polynomial H13Local

theorem sigK_thetaInv {K : Type*} [Field K] [CharZero K] (t₀ y₀ : K)
    (P : MvPolynomial (Fin 2) ℚ) :
    sigK t₀ y₀ (thetaInv P) = MvPolynomial.aeval (![t₀, y₀] : Fin 2 → K) P := by
  have h : (sigK t₀ y₀).comp thetaInv =
      ((MvPolynomial.aeval (![t₀, y₀] : Fin 2 → K) : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] K) :
        MvPolynomial (Fin 2) ℚ →+* K) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · exact RingHom.congr_fun (RingHom.ext_rat (((sigK t₀ y₀).comp thetaInv).comp MvPolynomial.C)
        (((MvPolynomial.aeval (![t₀, y₀] : Fin 2 → K) : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] K) :
          MvPolynomial (Fin 2) ℚ →+* K).comp MvPolynomial.C)) r
    · fin_cases i <;> simp [thetaInv, sigK, tS]
  exact RingHom.congr_fun h P

/-- `B_n(q₀, α)` at the point of `ℚ(s)(α)` (rows `λ`). -/
noncomputable def BK (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) K0 := TFock.Bm aK qK n

/-- `B_n(q₀, 2q₀ − α)`. -/
noncomputable def BK' (n : ℕ) : Matrix (Nat.Partition n) (Nat.Partition n) K0 :=
  TFock.Bm (2 * qK - aK) qK n

/-- `det B_n(q₀,2q₀−α) det B_n(q₀,α)`. -/
noncomputable def deltaK (n : ℕ) : K0 := (BK' n).det * (BK n).det

/-- `det D_n`. -/
noncomputable def dprod (n : ℕ) : ℤ := ∏ Z : Nat.Partition n, TFock.Dm Z

theorem gramK_factor (n : ℕ) :
    gram (cT tK) DK n =
      BK' n * Matrix.diagonal (fun Z : Nat.Partition n => ((TFock.Dm Z : ℤ) : K0)) *
        (BK n).transpose := by
  have := TFock.gram_factor aK qK n
  rw [c_K0, wt_K0] at this
  exact this

theorem gramK_det (n : ℕ) : (gram (cT tK) DK n).det = deltaK n * (dprod n : K0) := by
  rw [gramK_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_transpose,
    deltaK, dprod]
  push_cast
  ring

theorem BK_mem (n : ℕ) (Y Z : Nat.Partition n) : BK n Y Z ∈ S0 :=
  TFock.Bm_mem (by rw [half_K0]; exact half_mem) aK_mem qK_mem Y Z

theorem BK'_mem (n : ℕ) (Y Z : Nat.Partition n) : BK' n Y Z ∈ S0 :=
  TFock.Bm_mem (by rw [half_K0]; exact half_mem)
    (S0.sub_mem (S0.mul_mem two_mem qK_mem) aK_mem) qK_mem Y Z

theorem deltaK_mem (n : ℕ) : deltaK n ∈ S0 :=
  S0.mul_mem (det_mem S0 _ (BK'_mem n)) (det_mem S0 _ (BK_mem n))

/-- `n!/D_λ`. -/
noncomputable def mK (n : ℕ) (Z : Nat.Partition n) : ℤ := (n.factorial : ℤ) / TFock.Dm Z

theorem mK_spec (hL : Stmt_sub_h13_lagrange) (n : ℕ) (Z : Nat.Partition n) :
    TFock.Dm Z * mK n Z = (n.factorial : ℤ) :=
  Int.mul_ediv_cancel' (hL n Z)

theorem Dm_ne_zero (hL : Stmt_sub_h13_lagrange) {n : ℕ} (Z : Nat.Partition n) :
    TFock.Dm Z ≠ 0 := by
  intro h
  have := hL n Z
  rw [h, zero_dvd_iff] at this
  exact (Nat.cast_ne_zero.2 n.factorial_ne_zero) this

theorem dprod_ne_zero (hL : Stmt_sub_h13_lagrange) (n : ℕ) : dprod n ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun Z _ => Dm_ne_zero hL Z

/-- `∑ (B⁻ᵀ-adjugate · (n! D⁻¹) · B'-adjugate) ρ`: `n! Tr(G_n⁻¹ ρ_n)` times
`det B_n(q₀,2q₀−α) det B_n(q₀,α)` (paper.tex l.1285–1286). -/
noncomputable def NFK (ν : Fin 2) (n : ℕ) : K0 :=
  ∑ Y, ∑ Y', ((BK n).transpose.adjugate *
      Matrix.diagonal (fun Z : Nat.Partition n => ((mK n Z : ℤ) : K0)) * (BK' n).adjugate) Y Y' *
    torus (cT tK) DK (dvalK ν tK) n Y Y'

theorem NFK_mem (ν : Fin 2) (n : ℕ) : NFK ν n ∈ S0 := by
  refine S0.sum_mem fun Y _ => S0.sum_mem fun Y' _ => S0.mul_mem ?_ ?_
  · refine mul_mem_entries S0 _ _ (mul_mem_entries S0 _ _
      (adjugate_mem S0 _ fun i j => BK_mem n j i) fun i j => ?_) (adjugate_mem S0 _ (BK'_mem n)) Y Y'
    rw [Matrix.diagonal_apply]
    split_ifs
    exacts [intCast_mem S0 _, S0.zero_mem]
  · exact TFock.torusWord_mem (by rw [half_K0]; exact half_mem) cT_mem DK_mem (dvalK_mem ν) _ _

/-- `n! ∑ adj(G_n) ρ_n = det D_n · NF_n`. -/
theorem fact_AK (hL : Stmt_sub_h13_lagrange) (ν : Fin 2) (n : ℕ) :
    (n.factorial : K0) * AK ν tK DK n = (dprod n : K0) * NFK ν n := by
  have hd : (n.factorial : K0) • Matrix.diagonal
        (fun Z : Nat.Partition n => ∏ W ∈ Finset.univ.erase Z, ((TFock.Dm W : ℤ) : K0)) =
      (dprod n : K0) • Matrix.diagonal (fun Z : Nat.Partition n => ((mK n Z : ℤ) : K0)) := by
    rw [← Matrix.diagonal_smul, ← Matrix.diagonal_smul]
    congr 1
    funext Z
    simp only [Pi.smul_apply, smul_eq_mul]
    have e1 : (dprod n : K0) = ((TFock.Dm Z : ℤ) : K0) *
        ∏ W ∈ Finset.univ.erase Z, ((TFock.Dm W : ℤ) : K0) := by
      rw [dprod, Int.cast_prod,
        Finset.mul_prod_erase _ (fun W => ((TFock.Dm W : ℤ) : K0)) (Finset.mem_univ Z)]
    have e2 : (n.factorial : K0) = ((TFock.Dm Z : ℤ) : K0) * ((mK n Z : ℤ) : K0) := by
      have := congrArg (Int.cast : ℤ → K0) (mK_spec hL n Z)
      push_cast at this
      exact this.symm
    rw [e1, e2]
    ring
  have hmat : (n.factorial : K0) • (gram (cT tK) DK n).adjugate =
      (dprod n : K0) • ((BK n).transpose.adjugate *
        Matrix.diagonal (fun Z : Nat.Partition n => ((mK n Z : ℤ) : K0)) * (BK' n).adjugate) := by
    rw [gramK_factor, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
      Matrix.adjugate_diagonal, ← Matrix.mul_smul, ← Matrix.smul_mul, hd, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc]
  unfold AK NFK
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Y' _ => ?_
  have e := congrFun (congrFun hmat Y) Y'
  simp only [Matrix.smul_apply, smul_eq_mul] at e
  rw [← mul_assoc, e, mul_assoc]

/-- `det B_n(q₀,2q₀−α) det B_n(q₀,α)` is a unit at `𝔭` (paper.tex l.1270–1281). -/
theorem unit_deltaK (hK : Cited_KacDeterminant) (hL : Stmt_sub_h13_lagrange)
    (hS : Stmt_sub_h13_detD) (ℓ : ℕ) [Fact ℓ.Prime] (h2 : ℓ ≠ 2) (n : ℕ) :
    Unit0 ℓ (deltaK n) := by
  have hd0 : (dprod n : K0) ≠ 0 := Int.cast_ne_zero.2 (dprod_ne_zero hL n)
  have heq : deltaK n * (dprod n : K0) = (kacK n : K0) *
      ∏ a ∈ labels n, (DK - hT (a.1 : ℤ) (a.2 : ℤ) tK) ^
        Fintype.card (Nat.Partition (n - a.lvl)) := by
    rw [← gramK_det]
    exact kac_det_T hK tK_ne_zero DK n
  have hk : (kacK n : K0) = 2 ^ lenSum n * ((|dprod n| : ℤ) : K0) := by
    have := congrArg (Int.cast : ℤ → K0) (hS n)
    push_cast at this
    rw [dprod]
    push_cast
    exact this
  have hPi : Unit0 ℓ (∏ a ∈ labels n, (DK - hT (a.1 : ℤ) (a.2 : ℤ) tK) ^
      Fintype.card (Nat.Partition (n - a.lvl))) :=
    Unit0.prod ℓ _ _ fun a _ => (unit_factor ℓ h2 _ _).pow ℓ _
  have h2n : Unit0 ℓ ((2 : K0) ^ lenSum n) := (unit_two ℓ h2).pow ℓ _
  rcases abs_choice (dprod n) with h | h
  · rw [h] at hk
    have : deltaK n = 2 ^ lenSum n * ∏ a ∈ labels n, (DK - hT (a.1 : ℤ) (a.2 : ℤ) tK) ^
        Fintype.card (Nat.Partition (n - a.lvl)) := by
      apply mul_right_cancel₀ hd0
      rw [heq, hk]
      ring
    rw [this]
    exact h2n.mul ℓ hPi
  · rw [h] at hk
    have : deltaK n = -(2 ^ lenSum n * ∏ a ∈ labels n, (DK - hT (a.1 : ℤ) (a.2 : ℤ) tK) ^
        Fintype.card (Nat.Partition (n - a.lvl))) := by
      apply mul_right_cancel₀ hd0
      rw [heq, hk]
      push_cast
      ring
    rw [this]
    exact unit_neg ℓ (h2n.mul ℓ hPi)

/-- `P_M^{(ν)}(t,Y) ∏_n det B_n det B'_n` (paper.tex l.1285–1287). -/
noncomputable def NK (ν : Fin 2) (M : ℕ) : K0 :=
  (∏ u ∈ Finset.Icc 1 M, (tK ^ 2 * (2 * DK - 2 * hT (u : ℤ) 1 tK))) *
    ∑ j ∈ Finset.range (M + 1), (eta j : K0) *
      ((M.factorial / (M - j).factorial : ℕ) : K0) * NFK ν (M - j) *
      ∏ i ∈ (Finset.range (M + 1)).erase j, deltaK (M - i)

theorem NK_mem (ν : Fin 2) (M : ℕ) : NK ν M ∈ S0 := by
  refine S0.mul_mem (S0.prod_mem fun u _ => ?_) (S0.sum_mem fun j _ => ?_)
  · exact S0.mul_mem (S0.pow_mem tK_mem 2)
      (S0.sub_mem (S0.mul_mem two_mem DK_mem) (S0.mul_mem two_mem (hT_mem _ _)))
  · exact S0.mul_mem (S0.mul_mem (S0.mul_mem (intCast_mem S0 _) (natCast_mem S0 _))
      (NFK_mem ν _)) (S0.prod_mem fun i _ => deltaK_mem _)

/-- The value of `P_M^{(ν)}` at the point, times the determinants of the `B`'s
(paper.tex l.1285–1287). -/
theorem value_eq (hL : Stmt_sub_h13_lagrange) {ν : Fin 2} {M : ℕ} {P : MvPolynomial (Fin 2) ℚ}
    (hQ : clearedH ν M = psi (thetaInv P)) :
    MvPolynomial.aeval (![tK, YK] : Fin 2 → K0) P *
      ∏ j ∈ Finset.range (M + 1), deltaK (M - j) = NK ν M := by
  have hspec := specK (K := K0) hQ tK_ne_zero DK
  rw [sigK_thetaInv] at hspec
  set X : K0 := MvPolynomial.aeval (![tK, tK ^ 2 * DK] : Fin 2 → K0) P with hX
  set Dall : K0 := ∏ j ∈ Finset.range (M + 1), (dprod (M - j) : K0) with hDall
  have hD0 : Dall ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => Int.cast_ne_zero.2 (dprod_ne_zero hL _)
  have hl : ∏ j ∈ Finset.range (M + 1), (gram (cT tK) DK (M - j)).det =
      (∏ j ∈ Finset.range (M + 1), deltaK (M - j)) * Dall := by
    rw [hDall, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => gramK_det _
  have hterm : ∀ j ∈ Finset.range (M + 1),
      (M.factorial : K0) * ((eta j : K0) * AK ν tK DK (M - j) *
          ∏ i ∈ (Finset.range (M + 1)).erase j, (gram (cT tK) DK (M - i)).det) =
        Dall * ((eta j : K0) * ((M.factorial / (M - j).factorial : ℕ) : K0) * NFK ν (M - j) *
          ∏ i ∈ (Finset.range (M + 1)).erase j, deltaK (M - i)) := by
    intro j hj
    have h1 : ∏ i ∈ (Finset.range (M + 1)).erase j, (gram (cT tK) DK (M - i)).det =
        (∏ i ∈ (Finset.range (M + 1)).erase j, deltaK (M - i)) *
          ∏ i ∈ (Finset.range (M + 1)).erase j, (dprod (M - i) : K0) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => gramK_det _
    have h2 : Dall = (dprod (M - j) : K0) *
        ∏ i ∈ (Finset.range (M + 1)).erase j, (dprod (M - i) : K0) := by
      rw [hDall, Finset.mul_prod_erase _ (fun i => (dprod (M - i) : K0)) hj]
    have h3 : (M.factorial : K0) =
        ((M.factorial / (M - j).factorial : ℕ) : K0) * ((M - j).factorial : K0) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.sub_le M j))]
    have hF := fact_AK hL ν (M - j)
    rw [h1, h2, h3]
    linear_combination ((eta j : K0) * ((M.factorial / (M - j).factorial : ℕ) : K0) *
      (∏ i ∈ (Finset.range (M + 1)).erase j, deltaK (M - i)) *
      ∏ i ∈ (Finset.range (M + 1)).erase j, (dprod (M - i) : K0)) * hF
  have hsum : (M.factorial : K0) * ∑ j ∈ Finset.range (M + 1), (eta j : K0) *
        AK ν tK DK (M - j) * ∏ i ∈ (Finset.range (M + 1)).erase j, (gram (cT tK) DK (M - i)).det =
      Dall * ∑ j ∈ Finset.range (M + 1), (eta j : K0) *
        ((M.factorial / (M - j).factorial : ℕ) : K0) * NFK ν (M - j) *
        ∏ i ∈ (Finset.range (M + 1)).erase j, deltaK (M - i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  rw [hl] at hspec
  apply mul_right_cancel₀ hD0
  show X * _ * Dall = NK ν M * Dall
  unfold NK
  linear_combination hspec +
    (∏ u ∈ Finset.Icc 1 M, (tK ^ 2 * (2 * DK - 2 * hT (u : ℤ) 1 tK))) * hsum

/-- Proposition 6.8(i), integrality (paper.tex l.1261–1291), from the two combinatorial
statements `Stmt_sub_h13_lagrange` (l.1283–1285) and `Stmt_sub_h13_detD` (l.1270–1271). -/
theorem sub_h13_integral_of (hK : Cited_KacDeterminant) (hL : Stmt_sub_h13_lagrange)
    (hS : Stmt_sub_h13_detD) : Stmt_sub_h13_integral := by
  intro P hP ν M _ e
  apply two_pow_of_odd
  intro ℓ hℓ h2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hQ : clearedH ν M = psi (thetaInv (P ν M)) := by
    have h1 := aeval_thetaMv (thetaInv (P ν M))
    rw [thetaMv_thetaInv, hP] at h1
    exact h1
  exact local_integral ℓ h2 (P ν M)
    (Unit0.prod ℓ _ _ fun j _ => unit_deltaK hK hL hS ℓ h2 (M - j)) (NK_mem ν M)
    (value_eq hL hQ) e

/-- Proposition 6.8 from clause (ii) (`Stmt_sub_h13_degree`, l.1293–1378) and the two
combinatorial statements of clause (i) (l.1270–1271, l.1283–1285). -/
theorem prop_h13_nonvanishing_of_comb (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hL : Stmt_sub_h13_lagrange) (hS : Stmt_sub_h13_detD) (h2 : Stmt_sub_h13_degree) :
    Stmt_prop_h13_nonvanishing :=
  prop_h13_nonvanishing_of_two hK hH (sub_h13_integral_of hK hL hS) h2

end Virasoro
