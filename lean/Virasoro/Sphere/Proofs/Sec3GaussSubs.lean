import Virasoro.Sphere.Proofs.Sec3LamSubs
import Virasoro.Sphere.Proofs.Sec3GaussLimit
import Virasoro.Sphere.Proofs.Sec3PolyH
import Virasoro.Sphere.Proofs.RegEval

/-!
# Sphere paper Lemma 3.3(iii) (`sphere/paper.tex` l.637–711): reduction to algebra over `ℂ(λ)`

The limit (3.5) is taken coefficient by coefficient in `z`.  Each coefficient of
`e^{-λ²𝓘₀(z)} ℬ(z)` is a rational function of `λ`: by Lemma 3.2(ii), `ℬ_N` is the Fock pairing of
the Ward solutions, whose coefficients are rational in `λ` (Lemma 3.3(i)).  The limit along real
`λ → +∞` is therefore the value at `λ = ∞` of a rational function regular there, and the
statement becomes one about the expansion in `λ⁻¹` (`Stmt_sub_lam_gauss`), the form in which the
paper carries out the Gaussian evaluation ("`λ⁻¹`-extractions", l.680–682).
-/

namespace Virasoro.Sphere

open MvPolynomial Filter Topology

local notation "KK" => RatFunc ℂ

/-- Complex conjugation of the coefficients of a rational function of `λ` (`i ↦ -i` at real
`λ`). -/
theorem conj_nzd : nonZeroDivisors (Polynomial ℂ) ≤
    Submonoid.comap (Polynomial.mapRingHom (starRingEnd ℂ)) (nonZeroDivisors (Polynomial ℂ)) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ (starRingEnd ℂ).injective)

noncomputable def conjK : KK →+* KK :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (starRingEnd ℂ)) conj_nzd

theorem constantCoeff_map_zero {A B : Type*} [CommSemiring A] [CommSemiring B] (f : A →+* B)
    {g : PowerSeries A} (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.constantCoeff (g.map f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, map_zero]

theorem conjK_div (p q : Polynomial ℂ) :
    conjK (algebraMap _ KK p / algebraMap _ KK q) =
      algebraMap _ KK (p.map (starRingEnd ℂ)) / algebraMap _ KK (q.map (starRingEnd ℂ)) :=
  RatFunc.map_apply_div (Polynomial.mapRingHom (starRingEnd ℂ)) conj_nzd p q

theorem eval_map_conj (p : Polynomial ℂ) (a : ℝ) :
    (p.map (starRingEnd ℂ)).eval (a : ℂ) = (starRingEnd ℂ) (p.eval (a : ℂ)) := by
  rw [Polynomial.eval_map]
  conv_lhs => rw [← Complex.conj_ofReal a]
  exact Polynomial.eval₂_at_apply _ _

/-- At real `λ = a`, `conjK` conjugates the value. -/
theorem regAt_conjK {a : ℝ} {x : KK} (h : RegAt (a : ℂ) x) :
    RegAt (a : ℂ) (conjK x) ∧ evalAt (a : ℂ) (conjK x) = (starRingEnd ℂ) (evalAt (a : ℂ) x) := by
  have hq : (x.denom.map (starRingEnd ℂ)).eval (a : ℂ) ≠ 0 := by
    rw [eval_map_conj]
    exact (map_ne_zero _).2 h
  have hx : conjK x = algebraMap _ KK (x.num.map (starRingEnd ℂ)) /
      algebraMap _ KK (x.denom.map (starRingEnd ℂ)) := by
    conv_lhs => rw [← RatFunc.num_div_denom x]
    exact conjK_div _ _
  rw [hx]
  refine ⟨regAt_div _ _ hq, ?_⟩
  rw [evalAt_div _ _ hq, eval_map_conj, eval_map_conj, ← map_div₀]
  rfl

/-- The Fock pairing `⟨F̃_n, F_n⟩` of Lemma 3.2(ii) over `ℂ(λ)`: `F` is the Ward solution for
`(Δ₁,Δ₂)` and `F̃` the one for `(Δ₄,Δ₃)` with conjugated coefficients. -/
noncomputable def pairK (μ : ℝ) (Δe : Fin 4 → ℝ) (n : ℕ) : KK :=
  ∑ α ∈ (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) n).support,
    conjK (coeff α (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ) n)) *
      coeff α (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) n) * RatFunc.C (fockNorm α)

/-- The coefficient of `z^n` of `e^{-λ²𝓘₀(z)} ∑_j ℬ_j z^j` as a rational function of `λ`. -/
noncomputable def gaussCoeff (I0 : PowerSeries ℂ) (μ : ℝ) (Δe : Fin 4 → ℝ) (n : ℕ) : KK :=
  PowerSeries.coeff n
    ((PowerSeries.exp KK).subst
        (PowerSeries.C (-(RatFunc.X : KK) ^ 2) * I0.map (algebraMap ℂ KK)) *
      PowerSeries.mk (pairK μ Δe))

/-- Lemma 3.3(iii), membership in `zℚ[[z]]` (sphere/paper.tex l.541–545, l.705–708):
`Φ_c^raw = 2S_c^{(2)}(σ_*) + Ψ₁` and `Φ_j = S_j^{(2)}(σ_*)` lie in `zℚ[[z]]`. -/
def Stmt_sub_lam_rational : Prop :=
  ∀ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ, IsExpansionData S1t S2c S21 S22 →
    ∀ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb →
      InZQ (PhiCraw S1t S2c σ σb) ∧ InZQ (MvPowerSeries.subst σ S21) ∧
      InZQ (MvPowerSeries.subst σ S22)

/-- Lemma 3.3(iii), the Gaussian evaluation in `λ⁻¹` (sphere/paper.tex l.637–711): every
coefficient in `z` of `e^{-λ²𝓘₀(z)} ℬ(z)`, a rational function of `λ`, is regular at `λ = ∞`, and
its value there is the coefficient of
`det(I - M(z)²)^{-1/2} exp(μ²Φ_c^raw + (Δ₁+Δ₄-1/8)Φ₁ + (Δ₂+Δ₃-1/8)Φ₂)`. -/
def Stmt_sub_lam_gauss : Prop :=
  ∀ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ, IsExpansionData S1t S2c S21 S22 →
    ∀ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb →
      ∀ μ : ℝ, 0 < μ → ∀ (Δe : Fin 4 → ℝ) (n : ℕ),
        RegularAtInfty (gaussCoeff (I0def σ σb) μ Δe n) ∧
        inftyCoeff (gaussCoeff (I0def σ σb) μ Δe n) 0 =
          PowerSeries.coeff n
            (detInvSqrt.map (algebraMap ℚ ℂ) *
              (PowerSeries.exp ℂ).subst
                ((μ : ℂ) ^ 2 • PhiCraw S1t S2c σ σb +
                  ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • MvPowerSeries.subst σ S21 +
                  ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • MvPowerSeries.subst σ S22))

section Eval

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
/-- At real `λ > 0` the pairing over `ℂ(λ)` has no pole and its value is `ℬ_n(λ² + μ²)`
(Lemma 3.2(ii)). -/
theorem pairK_eval (μ : ℝ) (hμ : 0 < μ) (Δe : Fin 4 → ℝ) (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    RegAt (lam : ℂ) (pairK μ Δe n) ∧
      evalAt (lam : ℂ) (pairK μ Δe n) =
        RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
          (Bsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) n) := by
  classical
  have hW1 := (sub_lam_ward hF hK μ hμ (Δe 0) (Δe 1)).2 _
    (wardRat_isWard hF hK μ hμ (Δe 0 : ℂ) (Δe 1 : ℂ)) lam hlam
  have hW2 := (sub_lam_ward hF hK μ hμ (Δe 3) (Δe 2)).2 _
    (wardRat_isWard hF hK μ hμ (Δe 3 : ℂ) (Δe 2 : ℂ)) lam hlam
  have hfv := (lem_fock_verma_of_cited hF hK).1 μ hμ lam hlam
  dsimp only at hfv
  have hB := (hfv.2 Δe).2 _ _ hW1.2 hW2.2 n
  have hreg : ∀ α ∈ (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) n).support,
      RegAt (lam : ℂ) (conjK (coeff α (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ) n)) *
        coeff α (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) n) * RatFunc.C (fockNorm α)) := fun α _ =>
    ((regAt_conjK (hW2.1 n α)).1.mul (hW1.1 n α)).mul (regAt_C _ _)
  refine ⟨RegAt.sum hreg, ?_⟩
  rw [hB, pairK, evalAt_sum hreg, fockBil]
  have hsub : (specialize (lam : ℂ) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) n)).support ⊆
      (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) n).support := by
    intro α hα
    rw [mem_support_iff, coeff_specialize] at hα
    rw [mem_support_iff]
    intro h0
    rw [h0] at hα
    exact hα (by simp [RatFunc.eval])
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [evalAt_mul ((regAt_conjK (hW2.1 n α)).1.mul (hW1.1 n α)) (regAt_C _ _),
      evalAt_mul (regAt_conjK (hW2.1 n α)).1 (hW1.1 n α), (regAt_conjK (hW2.1 n α)).2, evalAt_C,
      coeff_map, coeff_specialize, coeff_specialize]
  · intro α _ hα
    rw [evalAt_mul ((regAt_conjK (hW2.1 n α)).1.mul (hW1.1 n α)) (regAt_C _ _),
      evalAt_mul (regAt_conjK (hW2.1 n α)).1 (hW1.1 n α)]
    have h0 : evalAt (lam : ℂ) (coeff α (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) n)) = 0 := by
      have h1 := coeff_specialize (lam : ℂ) (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) n) α
      rw [notMem_support_iff.1 hα] at h1
      exact h1.symm
    rw [h0, mul_zero, zero_mul]

/-- The exponential prefactor over `ℂ[λ]`. -/
noncomputable def expPoly (I0 : PowerSeries ℂ) : PowerSeries (Polynomial ℂ) :=
  (PowerSeries.exp (Polynomial ℂ)).subst
    (PowerSeries.C (-(Polynomial.X : Polynomial ℂ) ^ 2) * I0.map Polynomial.C)

theorem expPoly_map {A : Type*} [CommRing A] [Algebra ℚ A] (I0 : PowerSeries ℂ)
    (h0 : PowerSeries.constantCoeff I0 = 0) (h : Polynomial ℂ →+* A) :
    (expPoly I0).map h =
      (PowerSeries.exp A).subst
        (PowerSeries.C (-(h Polynomial.X) ^ 2) * I0.map (h.comp Polynomial.C)) := by
  have hs : PowerSeries.HasSubst
      (PowerSeries.C (-(Polynomial.X : Polynomial ℂ) ^ 2) * I0.map Polynomial.C) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      rw [map_mul, constantCoeff_map_zero _ h0, mul_zero])
  refine (PowerSeries.map_subst hs (h := h) _).trans ?_
  rw [PowerSeries.map_exp]
  congr 1
  change PowerSeries.map h _ = _
  have e : PowerSeries.map h (PowerSeries.map Polynomial.C I0) =
      PowerSeries.map (h.comp Polynomial.C) I0 := by
    ext k
    simp [PowerSeries.coeff_map]
  rw [map_mul, PowerSeries.map_C, e]
  simp

include hF hK in
/-- At real `λ > 0`, the value of `gaussCoeff` is the coefficient in the limit (3.5). -/
theorem gaussCoeff_eval (I0 : PowerSeries ℂ) (h0 : PowerSeries.constantCoeff I0 = 0) (μ : ℝ)
    (hμ : 0 < μ) (Δe : Fin 4 → ℝ) (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    evalAt (lam : ℂ) (gaussCoeff I0 μ Δe n) =
      PowerSeries.coeff n
        ((PowerSeries.exp ℂ).subst (PowerSeries.C (-(lam : ℂ) ^ 2) * I0) *
          PowerSeries.mk fun j =>
            RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
              (Bsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) j)) := by
  have hK1 := expPoly_map I0 h0 (algebraMap (Polynomial ℂ) KK)
  have hC1 := expPoly_map I0 h0 (Polynomial.evalRingHom (lam : ℂ))
  have e1 : (algebraMap (Polynomial ℂ) KK).comp Polynomial.C = algebraMap ℂ KK := by
    ext x
    simp
  have e2 : (Polynomial.evalRingHom (lam : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
    ext x
    simp
  rw [e1, RatFunc.algebraMap_X] at hK1
  rw [e2, PowerSeries.map_id] at hC1
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_X, RingHom.id_apply, id_eq] at hC1
  rw [gaussCoeff, ← hK1, ← hC1, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  have hreg : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      RegAt (lam : ℂ) (PowerSeries.coeff p.1 ((expPoly I0).map (algebraMap (Polynomial ℂ) KK)) *
        PowerSeries.coeff p.2 (PowerSeries.mk (pairK μ Δe))) := fun p _ => by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
    exact (regAt_algebraMap _ _).mul (pairK_eval hF hK μ hμ Δe lam hlam p.2).1
  rw [evalAt_sum hreg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    evalAt_mul (regAt_algebraMap _ _) (pairK_eval hF hK μ hμ Δe lam hlam p.2).1,
    evalAt_algebraMap, (pairK_eval hF hK μ hμ Δe lam hlam p.2).2]
  rfl

include hF hK in
/-- Lemma 3.3(iii) from the membership statement and the Gaussian evaluation in `λ⁻¹`. -/
theorem sub_lam_limit_of_gauss (hJ2 : Cited_JacobiIdentities2) (h1 : Stmt_sub_lam_rational)
    (h2 : Stmt_sub_lam_gauss) : Stmt_sub_lam_limit := by
  intro S1t S2c S21 S22 hE σ σb hs
  obtain ⟨hc, hp1, hp2⟩ := h1 S1t S2c S21 S22 hE σ σb hs
  refine ⟨hc, hp1, hp2, fun μ hμ Δe n => ?_⟩
  obtain ⟨hreg, hval⟩ := h2 S1t S2c S21 S22 hE σ σb hs μ hμ Δe n
  have h0 : PowerSeries.constantCoeff (I0def σ σb) = 0 := by
    obtain ⟨e1, e2⟩ := hs.eq_sigmaStar
    rw [e1, e2]
    obtain ⟨g, hg, hg'⟩ := inZQ_I0 hJ2
    rw [hg']
    exact constantCoeff_map_zero _ hg
  have ht := tendsto_evalAt_of_regularAtInfty _ hreg
  rw [hval] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with lam hlam
  exact gaussCoeff_eval hF hK _ h0 μ hμ Δe lam hlam n

end Eval

end Virasoro.Sphere
