import Virasoro.Sphere.Proofs.Sec3LamRat
import Virasoro.Sphere.Proofs.Sec3SaddleI0e
import Virasoro.Sphere.Statements.Sec3c

/-!
# Sphere paper Lemma 3.3 (`sphere/paper.tex` l.506–711): the steps of the proof

The proof of Lemma 3.3 is divided along the paper's steps into the statements below.  The first
(the Ward solution over `ℂ(λ)`) is proved here; `lem_lambda_expansion_of_steps` assembles the
lemma from all of them and Lemma 3.4.
-/

namespace Virasoro.Sphere

open MvPolynomial

/-- Step (i-a), sphere/paper.tex l.513–514 with Lemma 3.2(ii) and l.569–588: for `μ > 0` and
real `Δ₁, Δ₂` the Ward equations have exactly one solution over `ℂ(λ)`; at every real `λ > 0`
its coefficients have no pole and their values solve the Ward equations over `ℂ`. -/
def Stmt_sub_lam_ward : Prop :=
  ∀ μ : ℝ, 0 < μ → ∀ Δ1 Δ2 : ℝ,
    (∃! F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
      IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F) ∧
    ∀ F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
      IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F →
      ∀ lam : ℝ, 0 < lam →
        (∀ (m : ℕ) (α : ℕ+ →₀ ℕ), ((F m).coeff α).denom.eval (lam : ℂ) ≠ 0) ∧
        IsWardSeries (μ : ℂ) (lam : ℂ) (Δ1 : ℂ) (Δ2 : ℂ) fun m => specialize (lam : ℂ) (F m)

/-- Step (i-b), sphere/paper.tex l.559–600: every coefficient of `S(σ;λ) = λ⁻² log F(λσ;λ)` is
regular at `λ = ∞` (equation (3.3), injectivity of `𝒟_m(∞)`, induction on `m`). -/
def Stmt_sub_lam_regular : Prop :=
  ∀ μ : ℝ, 0 < μ → ∀ Δ1 Δ2 : ℝ, ∀ F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
    IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F →
      ∀ α : ℕ+ →₀ ℕ, RegularAtInfty (Slam F α)

/-- Step (ii-a), sphere/paper.tex l.602–612: the order-`λ⁰` part of (3.3) determines `S^{(0)}`,
and it is the quadratic `S^{(0)}` of (3.4) by Lemma 3.4(i). -/
def Stmt_sub_lam_order_zero : Prop :=
  ∀ μ : ℝ, 0 < μ → ∀ Δ1 Δ2 : ℝ, ∀ F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
    IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F →
      Sord F 0 = S0

/-- Step (ii-b), sphere/paper.tex l.612–635: the orders `λ⁻¹` and `λ⁻²` of (3.3).
`S^{(1)} = μ S̃^{(1)}` with `S̃^{(1)}` `ι`-odd; `S^{(2)} = μ² S_c^{(2)} + (Δ₂ - 1/16) S_2^{(2)}
+ (Δ₁ - 1/16) S_1^{(2)}` is `ι`-even, with `L_k^{(0)} S_2^{(2)} = k`, `L_k^{(0)} S_1^{(2)} = -1`. -/
def Stmt_sub_lam_orders : Prop :=
  ∃ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ,
    IsExpansionData S1t S2c S21 S22 ∧
    iota S1t = -S1t ∧
    (∀ k : ℕ, 1 ≤ k → L0 k S22 = MvPowerSeries.C (k : ℂ) ∧ L0 k S21 = -1) ∧
    ∀ μ : ℝ, 0 < μ → ∀ Δ1 Δ2 : ℝ, ∀ F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
      IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
          (RatFunc.C (Δ2 : ℂ)) F →
        iota (Sord F 2) = Sord F 2

/-- Step (iii), sphere/paper.tex l.637–711: the Gaussian evaluation of the Fock pairing at the
saddle point.  For the universal series of (ii) and a saddle point `(σ_*, σ̄_*)`, the series
`Φ_c^raw = 2S_c^{(2)}(σ_*) + Ψ₁` and `Φ_j = S_j^{(2)}(σ_*)` lie in `zℚ[[z]]` and the limit (3.5)
holds coefficient by coefficient in `z`, with `𝓘₀` the saddle value. -/
def Stmt_sub_lam_limit : Prop :=
  ∀ S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ, IsExpansionData S1t S2c S21 S22 →
    ∀ σ σb : ℕ+ → PowerSeries ℂ, IsSaddle σ σb →
      InZQ (PhiCraw S1t S2c σ σb) ∧ InZQ (MvPowerSeries.subst σ S21) ∧
      InZQ (MvPowerSeries.subst σ S22) ∧
      ∀ μ : ℝ, 0 < μ → ∀ (Δe : Fin 4 → ℝ) (n : ℕ),
        Filter.Tendsto
          (fun lam : ℝ => PowerSeries.coeff n
            ((PowerSeries.exp ℂ).subst (PowerSeries.C (-(lam : ℂ) ^ 2) * I0def σ σb) *
              PowerSeries.mk fun j =>
                RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
                  (Bsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) j)))
          Filter.atTop
          (nhds (PowerSeries.coeff n
            (detInvSqrt.map (algebraMap ℚ ℂ) *
              (PowerSeries.exp ℂ).subst
                ((μ : ℂ) ^ 2 • PhiCraw S1t S2c σ σb +
                  ((Δe 0 : ℂ) + (Δe 3 : ℂ) - 1 / 8) • MvPowerSeries.subst σ S21 +
                  ((Δe 1 : ℂ) + (Δe 2 : ℂ) - 1 / 8) • MvPowerSeries.subst σ S22))))

/-- Step (i-a): the Ward solution over `ℂ(λ)`, from Lemma 3.2 and the leading part of the
operators at `λ = ∞`. -/
theorem sub_lam_ward (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant) :
    Stmt_sub_lam_ward := by
  intro μ hμ Δ1 Δ2
  have hW := wardRat_isWard hF hK μ hμ (Δ1 : ℂ) (Δ2 : ℂ)
  have huniq : ∀ F : ℕ → MvPolynomial ℕ+ (RatFunc ℂ),
      IsWardSeries (RatFunc.C (μ : ℂ)) (RatFunc.X : RatFunc ℂ) (RatFunc.C (Δ1 : ℂ))
        (RatFunc.C (Δ2 : ℂ)) F → F = wardRat μ (Δ1 : ℂ) (Δ2 : ℂ) := fun F h =>
    funext fun m => ward_unique_ratFunc (μ : ℂ) (Δ1 : ℂ) (Δ2 : ℂ) F _ h hW m
  refine ⟨⟨_, hW, huniq⟩, fun F h lam hlam => ?_⟩
  rw [huniq F h]
  refine ⟨fun m α => (wardRat_specialize hF hK μ hμ (Δ1 : ℂ) (Δ2 : ℂ) lam hlam m).1 α, ?_⟩
  have e : (fun m => specialize (lam : ℂ) (wardRat μ (Δ1 : ℂ) (Δ2 : ℂ) m)) =
      fun m => gammaVec hF hK μ lam hμ hlam (Δ1 : ℂ) (Δ2 : ℂ) m :=
    funext fun m => (wardRat_specialize hF hK μ hμ (Δ1 : ℂ) (Δ2 : ℂ) lam hlam m).2
  rw [e]
  exact ⟨gammaVec_zero hF hK μ lam hμ hlam _ _, fun m => gammaVec_mem hF hK μ lam hμ hlam _ _ m,
    fun k hk m => gammaVec_ward hF hK μ lam hμ hlam _ _ k hk m⟩

theorem inIZQ_sigmaStar (m : ℕ+) : InIZQ (sigmaStar m) := by
  refine ⟨PowerSeries.C (1 / ((m : ℕ) : ℚ)) * (aSer m * PowerSeries.X ^ (m : ℕ)), ?_, ?_⟩
  · simp [m.pos.ne']
  · rw [sigmaStar, PowerSeries.smul_eq_C_mul (a := (1 / ((m : ℕ) : ℂ)))]
    simp

theorem inZQ_I0 (hJ2 : Cited_JacobiIdentities2) :
    InZQ (I0def sigmaStar (fun m => -sigmaStar m)) := by
  refine ⟨I0Q, ?_, ?_⟩
  · rw [I0Q_eq hJ2]
    have h0 : PowerSeries.constantCoeff (R0 - 1) = 0 := by
      rw [map_sub, constantCoeff_R0, map_one, sub_self]
    exact PowerSeries.constantCoeff_subst_eq_zero h0 _ PowerSeries.constantCoeff_log
  · ext k
    rw [coeff_I0def_sigmaStar, PowerSeries.coeff_map, I0Q, PowerSeries.coeff_mk]
    rfl

/-- Lemma 3.3 from the steps of its proof. -/
theorem lem_lambda_expansion_of_steps (hJ2 : Cited_JacobiIdentities2)
    (h1 : Stmt_sub_lam_ward) (h2 : Stmt_sub_lam_regular) (h3 : Stmt_sub_lam_order_zero)
    (h4 : Stmt_sub_lam_orders) (h5 : Stmt_sub_lam_limit) : Stmt_lem_lambda_expansion := by
  obtain ⟨S1t, S2c, S21, S22, hE, hι, hL, hev⟩ := h4
  refine ⟨fun μ hμ Δ1 Δ2 => ⟨(h1 μ hμ Δ1 Δ2).1, fun F hFw =>
    ⟨(h1 μ hμ Δ1 Δ2).2 F hFw, h2 μ hμ Δ1 Δ2 F hFw, h3 μ hμ Δ1 Δ2 F hFw,
      hev μ hμ Δ1 Δ2 F hFw⟩⟩, S1t, S2c, S21, S22, hE, hι, hL, ?_⟩
  have hs := isSaddle_sigmaStar
  obtain ⟨hc, hp1, hp2, hlim⟩ := h5 S1t S2c S21 S22 hE _ _ hs
  exact ⟨I0def sigmaStar (fun m => -sigmaStar m), PhiCraw S1t S2c sigmaStar _,
    MvPowerSeries.subst sigmaStar S21, MvPowerSeries.subst sigmaStar S22, inZQ_I0 hJ2, hc, hp1,
    hp2, sigmaStar, _, hs, fun σ' σb' h' => h'.eq_sigmaStar, inIZQ_sigmaStar, rfl, rfl, hlim⟩

end Virasoro.Sphere
