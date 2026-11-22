import Virasoro.Proofs.P2Sec9GenRC
import Virasoro.Sphere.Proofs.RegEval

/-!
# Theorem 9.3: the identity (9.3), regularity at the orbit, and part (a) (paper.tex l.1926–1950,
l.3040–3078)
-/

namespace Virasoro.P2

open Virasoro Polynomial

open scoped Matrix

theorem regAt_of_poleOrder {f : RatFunc ℂ} {a : ℂ} (h : poleOrder f a = 0) : RegAt a f := by
  have hord : OrdGE (expandHom a f) 0 := by
    rw [ordGE_iff]
    intro n hn
    by_contra hne
    have h1 : (expandAt f a).order ≤ n := HahnSeries.order_le_of_coeff_ne_zero hne
    unfold poleOrder at h
    rw [Int.toNat_eq_zero] at h
    omega
  exact Sphere.regAt_of_mem_regRing hord

theorem muOrb_true_zero {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) :
    muOrb p p' r s true 0 = kacH r s b := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  rw [kacH_momWt (by omega) (by omega) hb, muOrb]
  congr 1
  simp [nOrb]

theorem ellOrb_zero' (p p' r s : ℕ) (ε : Bool) : ellOrb p p' r s ε 0 = 0 := by simp [ellOrb]

theorem orbit_descends (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) {k m : ℕ} (hk : k < min r (p - r))
    (hm : m < min s (p' - s)) (ε : Bool) (j : ℕ) :
    TorusDescends (kacC b) (muOrb p p' r s ε j) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) :=
  torusDescends_of_radical fun T hT =>
    sub_vertex_radical_zero hJ hH hU hF p p' r s b hset ε j k m hk hm T hT

/-- The identity (9.3) at the level `N` (l.3040–3075). -/
theorem gen_rc_main (hK : Cited_KacDeterminant) (hE : Cited_TwoWeightPairingExists)
    (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hLau : Cited_SingularFamilyLaurent) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    {k m : ℕ} (hk : k < min r (p - r)) (hm : m < min s (p' - s)) (N : ℕ) :
    (∃ T : ℂ, IsIrrTrace (kacC b) (kacH r s b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N T) ∧
      ∀ T : ℂ, IsIrrTrace (kacC b) (kacH r s b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N T →
        T = FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N (kacH r s b) +
          ∑ j ∈ Finset.Icc 1 N, (-1 : ℂ) ^ j *
            ((if ellOrb p p' r s true j ≤ N then
                (Omega p p' r s k m true 0 true j : ℂ) *
                  FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
                    (N - ellOrb p p' r s true j) (muOrb p p' r s true j) else 0) +
              (if ellOrb p p' r s false j ≤ N then
                (Omega p p' r s k m true 0 false j : ℂ) *
                  FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
                    (N - ellOrb p p' r s false j) (muOrb p p' r s false j) else 0)) := by
  classical
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have h131 := lem_degenerate_quotient_t_of_cited hK hE hH hU hF hLau hJ hI
  have hd := orbit_descends hJ hH hU hF hset hk hm
  choose tv htv using fun ε j M => (irrTrace_existsUnique (hd ε j) M).exists
  have hμ0 := muOrb_true_zero hset
  refine ⟨⟨tv true 0 N, by rw [← hμ0]; exact htv true 0 N⟩, fun T hT => ?_⟩
  have hT' : IsIrrTrace (kacC b) (muOrb p p' r s true 0)
      (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N T := by rw [hμ0]; exact hT
  have hTe : T = tv true 0 N := (irrTrace_existsUnique (hd true 0) N).unique hT' (htv true 0 N)
  have hstep : ∀ j, Tsh p p' r s k m N tv (sig j) j + Tsh p p' r s k m N tv (sig (j + 1)) (j + 1) =
      Fsh p p' r s k m b N (sig j) j - Fsh p p' r s k m b N (sig j) (j + 1) := by
    intro j
    rw [sig_succ]
    refine scaled_step h131 hset hk hm N tv htv (sig j) j ?_ (sig j)
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact Or.inr sig_zero
    · exact Or.inl (by omega)
  have hL := telescope_left (fun j => Tsh p p' r s k m N tv (sig j) j)
    (fun j => Fsh p p' r s k m b N (sig j) j) (fun j => Fsh p p' r s k m b N (sig j) (j + 1))
    hstep N
  have hR := telescope_right (Fsh p p' r s k m b N) N
  have hge := ellOrb_ge hp hp' hr0 hr hs0 hs
  have hA : Tsh p p' r s k m N tv (sig (N + 1)) (N + 1) = 0 := by
    unfold Tsh
    rw [if_neg (by have := hge (N + 1) (sig (N + 1)); omega)]
  have hC : Fsh p p' r s k m b N (sig N) (N + 1) = 0 := by
    unfold Fsh
    rw [if_neg (by have := hge (N + 1) (sig N); omega)]
  have hA0 : Tsh p p' r s k m N tv (sig 0) 0 = tv true 0 N := by
    simp [Tsh, sig_zero, ellOrb_zero', Omega]
  have hF0 : Fsh p p' r s k m b N true 0 =
      FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) N (kacH r s b) := by
    simp [Fsh, ellOrb_zero', Omega, hμ0]
  rw [hR, hA, hC, mul_zero, sub_zero, add_zero, hA0, hF0] at hL
  rw [hTe, ← hL]
  rfl

/-- Regularity of `F_M(c⋆,Δ,d)` at the orbit weights (Theorem 9.1). -/
theorem gen_rc_regular (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hJ : Cited_JantzenLayersOrbit)
    (hI : Cited_VermaHomInjective) {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b)
    {k m : ℕ} (hk : k < min r (p - r)) (hm : m < min s (p' - s)) (ε : Bool) (j M : ℕ) :
    RegAt (muOrb p p' r s ε j)
      (Frat (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) M) := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  have h91 := (thm_descent_regularity_of_cited hJ hH hU hF hK hI p p' r s b hp2 hp2' hcop hbsq hr0
    hr hs0 hs).2.2 k m true hk hm (muOrb p p' r s ε j) ⟨ε, j, rfl⟩ M
  exact regAt_of_poleOrder h91.1

theorem cMM_zero (p p' : ℕ) (R S : ℤ) : cMM p p' R S 0 0 = 1 := by
  have h : boxShift R S 0 0 = boxSet R S := by simp [boxShift, boxSet]
  simp [cMM, h]

theorem pathProd_zero (p p' r s : ℕ) : ∀ (ε : Bool) (j : ℕ) (l : List Bool),
    pathProd p p' r s 0 0 ε j l = 1
  | _, _, [] => rfl
  | ε, j, x :: l => by rw [pathProd, pathProd_zero p p' r s x (j + 1) l, cArrow, cMM_zero, one_mul]

theorem Frat_d_zero (c : ℂ) (N : ℕ) : Frat c 0 N = (Fintype.card (Nat.Partition N) : RatFunc ℂ) := by
  have hT : torusPoly c 0 N = gramPoly c N := by
    rw [torusPoly, map_zero, torus_zero]
    rfl
  have hnum : Fnum c 0 N = (Fintype.card (Nat.Partition N) : ℂ[X]) * (gramPoly c N).det := by
    have hsym : (gramPoly c N)ᵀ = gramPoly c N := gram_transpose _ _ _
    have h1 : ∀ Y, (∑ Y', (gramPoly c N).adjugate Y Y' * gramPoly c N Y Y') =
        ((gramPoly c N).adjugate * gramPoly c N) Y Y := by
      intro Y
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun Y' _ => ?_
      congr 1
      have := congrFun (congrFun hsym Y') Y
      rw [Matrix.transpose_apply] at this
      exact this
    rw [Fnum, hT]
    simp only [h1, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hdet : algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det ≠ 0 :=
    RatFunc.algebraMap_ne_zero (gramPoly_det_ne_zero c N)
  rw [Frat, hnum, map_mul, mul_div_cancel_right₀ _ hdet, map_natCast]

/-- Part (a) (l.1946–1948, 3077–3078). -/
theorem gen_rc_a {p p' r s : ℕ} (b : ℂ) (hb : b ≠ 0) :
    kacH (2 * ((0 : ℕ) : ℤ) + 1) (2 * ((0 : ℕ) : ℤ) + 1) b = 0 ∧
      (∀ (ε : Bool) (j : ℕ), Omega p p' r s 0 0 true 0 ε j = 1) ∧
      ∀ (ε : Bool) (j N : ℕ),
        FvalAt (kacC b) (kacH (2 * ((0 : ℕ) : ℤ) + 1) (2 * ((0 : ℕ) : ℤ) + 1) b) N
          (muOrb p p' r s ε j) = (Fintype.card (Nat.Partition N) : ℂ) := by
  have hd : kacH (2 * ((0 : ℕ) : ℤ) + 1) (2 * ((0 : ℕ) : ℤ) + 1) b = 0 := by
    simp [kacH]
  refine ⟨hd, fun ε j => ?_, fun ε j N => ?_⟩
  · unfold Omega
    split_ifs
    · rfl
    · exact pathProd_zero p p' r s _ _ _
  · rw [hd, FvalAt, Frat_d_zero, show ((Fintype.card (Nat.Partition N) : ℕ) : RatFunc ℂ) =
        algebraMap ℂ[X] (RatFunc ℂ) ((Fintype.card (Nat.Partition N) : ℕ) : ℂ[X]) from
        (map_natCast _ _).symm]
    exact (evalAt_algebraMap _ _).trans (by simp)

end Virasoro.P2
