import Virasoro.Proofs.P2Sec13TauDepth
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Lemma 13.1, Step 2: Laurent families in `b` (paper.tex l.2906–2910)

"`χ_{R₁,S₁}(b(τ))` has regular coefficients in `ℂ[[τ]]`" (Proposition 10.2(i)): the PBW
coefficients are Laurent polynomials in `b`.  The ring `Lam = ℂ[b,b⁻¹]` carries `c(b)`,
`h_{u,v}(b)` and these coefficients; it maps to `ℂ` by evaluation at each `b' ≠ 0` (`evLam`)
and to `ℂ⟦X⟧` by `b ↦ b⋆ + X` (`locLam`).  An element that vanishes at infinitely many points
is zero, which turns the pointwise statements of Step 1 into identities over `ℂ⟦X⟧`.
-/

namespace Virasoro.P2

open Virasoro Verma Polynomial

open scoped PowerSeries

/-- Laurent polynomials in `b`. -/
abbrev Lam : Type := Localization.Away (X : ℂ[X])

/-- `b`. -/
noncomputable def lamX : Lam := algebraMap ℂ[X] Lam X

/-- `b⁻¹`. -/
noncomputable def lamXi : Lam := IsLocalization.Away.invSelf (X : ℂ[X])

theorem lamX_mul_lamXi : lamX * lamXi = 1 := IsLocalization.Away.mul_invSelf _

/-- Evaluation at `b ≠ 0`. -/
noncomputable def evLam (b : ℂ) (hb : b ≠ 0) : Lam →+* ℂ :=
  IsLocalization.Away.lift (X : ℂ[X]) (g := evalRingHom b) (by
    rw [coe_evalRingHom, eval_X]
    exact isUnit_iff_ne_zero.2 hb)

variable {b : ℂ} (hb : b ≠ 0)

theorem evLam_algebraMap (q : ℂ[X]) : evLam b hb (algebraMap ℂ[X] Lam q) = q.eval b :=
  IsLocalization.Away.lift_eq _ _ q

theorem evLam_lamX : evLam b hb lamX = b := by rw [lamX, evLam_algebraMap, eval_X]

theorem evLam_lamXi : evLam b hb lamXi = b⁻¹ := by
  have h := congrArg (evLam b hb) lamX_mul_lamXi
  rw [map_mul, map_one, evLam_lamX] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The expansion `b ↦ b⋆ + X` at `b⋆ ≠ 0`. -/
noncomputable def locLam (b : ℂ) (hb : b ≠ 0) : Lam →+* ℂ⟦X⟧ :=
  IsLocalization.Away.lift (X : ℂ[X])
    (g := eval₂RingHom (PowerSeries.C : ℂ →+* ℂ⟦X⟧) (bLoc b)) (by
      rw [coe_eval₂RingHom, eval₂_X, PowerSeries.isUnit_iff_constantCoeff, constantCoeff_bLoc]
      exact isUnit_iff_ne_zero.2 hb)

theorem locLam_algebraMap (q : ℂ[X]) :
    locLam b hb (algebraMap ℂ[X] Lam q) = q.eval₂ (PowerSeries.C : ℂ →+* ℂ⟦X⟧) (bLoc b) :=
  IsLocalization.Away.lift_eq _ _ q

theorem locLam_lamX : locLam b hb lamX = bLoc b := by rw [lamX, locLam_algebraMap, eval₂_X]

theorem bLoc_mul_inv {b : ℂ} (hb : b ≠ 0) : bLoc b * (bLoc b)⁻¹ = 1 :=
  PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_bLoc]; exact hb)

theorem locLam_lamXi : locLam b hb lamXi = (bLoc b)⁻¹ := by
  have h := congrArg (locLam b hb) lamX_mul_lamXi
  rw [map_mul, map_one, locLam_lamX] at h
  have h' : locLam b hb lamXi * bLoc b = 1 := by rw [mul_comm]; exact h
  exact left_inv_eq_right_inv h' (bLoc_mul_inv hb)

/-- The value at `X = 0` of the expansion at `b⋆` is the value at `b⋆`. -/
theorem constantCoeff_locLam (a : Lam) :
    PowerSeries.constantCoeff (locLam b hb a) = evLam b hb a := by
  have h : (PowerSeries.constantCoeff (R := ℂ)).comp (locLam b hb) = evLam b hb := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (X : ℂ[X])) ?_
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp only [RingHom.comp_apply, locLam_algebraMap, evLam_algebraMap, eval₂_C, eval_C,
        PowerSeries.constantCoeff_C]
    · simp only [RingHom.comp_apply, locLam_algebraMap, evLam_algebraMap, eval₂_X, eval_X,
        constantCoeff_bLoc]
  exact RingHom.congr_fun h a

/-- A Laurent polynomial with infinitely many zeros is zero. -/
theorem lam_eq_zero_of_infinite {a : Lam} {G : Set ℂ} (hG : G.Infinite)
    (h : ∀ (b : ℂ) (hb : b ≠ 0), b ∈ G → evLam b hb a = 0) : a = 0 := by
  obtain ⟨n, q, hq⟩ := IsLocalization.Away.surj (X : ℂ[X]) a
  have hq0 : q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot q
      ((hG.sdiff (Set.finite_singleton (0 : ℂ))).mono fun b hbG => ?_)
    have hb0 : b ≠ 0 := hbG.2
    have h1 := congrArg (evLam b hb0) hq
    rw [map_mul, h b hb0 hbG.1, zero_mul, evLam_algebraMap] at h1
    exact h1.symm
  rw [hq0, map_zero] at hq
  have hu : IsUnit (algebraMap ℂ[X] Lam X ^ n) :=
    (IsUnit.pow n ⟨⟨lamX, lamXi, lamX_mul_lamXi, by rw [mul_comm]; exact lamX_mul_lamXi⟩, rfl⟩)
  exact (hu.mul_left_eq_zero).1 hq

/-- `c(b)` as a Laurent polynomial. -/
noncomputable def cLam : Lam := 1 + 6 * (lamX + lamXi) ^ 2

/-- `h_{u,v}(b)` as a Laurent polynomial. -/
noncomputable def hLam (u v : ℤ) : Lam :=
  algebraMap ℂ[X] Lam (C (1 / 4 : ℂ)) *
    ((lamX + lamXi) ^ 2 - ((u : Lam) * lamX + (v : Lam) * lamXi) ^ 2)

theorem evLam_cLam : evLam b hb cLam = kacC b := by
  simp only [cLam, kacC, map_add, map_mul, map_pow, map_one, map_ofNat, evLam_lamX, evLam_lamXi]

theorem evLam_hLam (u v : ℤ) : evLam b hb (hLam u v) = kacH u v b := by
  simp only [hLam, kacH, map_mul, map_sub, map_pow, map_add, evLam_lamX, evLam_lamXi,
    evLam_algebraMap, eval_C, map_intCast]
  ring

theorem locLam_cLam : locLam b hb cLam = cLoc b := by
  simp only [cLam, cLoc, map_add, map_mul, map_pow, map_one, map_ofNat, locLam_lamX,
    locLam_lamXi]

theorem locLam_hLam (u v : ℤ) : locLam b hb (hLam u v) = hLoc u v b := by
  simp only [hLam, hLoc, map_mul, map_sub, map_pow, map_add, locLam_lamX, locLam_lamXi,
    locLam_algebraMap, eval₂_C, map_intCast]

section BaseChange

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (f : R →+* S)
  {c h : R} {c' h' : S} (hc : f c = c') (hh : f h = h')

/-- The level coordinates commute with a change of coefficient ring. -/
theorem comp_baseChange (N : ℕ) (W : Verma R c h) (Y : Nat.Partition N) :
    Verma.comp N (Verma.baseChange f hc hh W) Y = f (Verma.comp N W Y) := by
  classical
  have hW : W ∈ Submodule.span R (Set.range fun Y : (Σ N : ℕ, Nat.Partition N) =>
      neg (c := c) (h := h) Y.2.word) := by
    rw [span_neg_word_eq_top]; trivial
  refine Submodule.span_induction (p := fun W _ =>
    Verma.comp N (Verma.baseChange f hc hh W) Y = f (Verma.comp N W Y)) ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨Z, rfl⟩
    rw [Verma.baseChange_neg, comp_neg_word, comp_neg_word]
    split_ifs <;> simp
  · simp
  · intro U V _ _ hU hV
    simp only [map_add, Pi.add_apply, hU, hV]
  · intro a U _ hU
    rw [LinearMap.map_smulₛₗ, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, hU, smul_eq_mul,
      smul_eq_mul, map_mul]

/-- A change of coefficient ring maps `U(Vir_-)χ` into `U(Vir_-)` of the image of `χ`. -/
theorem baseChange_mem_negSpan {χ W : Verma R c h} (hW : W ∈ negSpan χ) :
    Verma.baseChange f hc hh W ∈ negSpan (Verma.baseChange f hc hh χ) := by
  unfold negSpan at hW
  refine Submodule.span_induction
    (p := fun W _ => Verma.baseChange f hc hh W ∈ negSpan (Verma.baseChange f hc hh χ))
    ?_ ?_ ?_ ?_ hW
  · rintro _ ⟨w, rfl⟩
    dsimp only
    rw [Verma.baseChange_negOp_smul]
    exact Submodule.subset_span ⟨w, rfl⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro U V _ _ hU hV
    rw [map_add]
    exact Submodule.add_mem _ hU hV
  · intro a U _ hU
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ hU

end BaseChange

end Virasoro.P2
