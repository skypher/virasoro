import Virasoro.Sphere.Proofs.Sec3ExpLog

/-!
# Lemma 3.7, Step 4: the limit of the `c = 2` decomposition (sphere paper)

sphere/paper.tex l.1013–1181.  Steps 1–3 of the proof (l.1029–1156) produce the decomposition
(3.8) of `G_charged G_neutral` into `c = 2` blocks, the limits `c_n^∞` of its coefficients and
their generating function; they are the frozen statement `Stmt_sub_c2_decomp`.  Step 4
(l.1158–1180) divides (3.8) by `(16q/z)^{λ²}` and lets `λ → ∞` at each order in `z`, using
Lemma 3.3(iii) at `c = 2`.  This file carries out the limit.
-/

namespace Virasoro.Sphere

open PowerSeries Filter Topology

/-- Lemma 3.7, Steps 1–3 (sphere/paper.tex l.1029–1156): the `c = 2` decomposition (3.8),
`G_charged(λ;z) G_neutral(z) = ∑_n c_n(λ²) z^n ℬ(2, λ²+n, 1/8; z)` in `ℂ[[z]]`, the limits
`c_n^∞ = lim_{λ→∞} c_n(λ²)`, and `∑_n 16^n c_n^∞ q^n = ∏_m (1 - q^{2m})^{-1/2}`.

Demand sheet.
- (3.8) coefficient by coefficient in `z`, the sum over `n` being finite at each order
  (l.1159–1160); the paper has it for every real `λ > 0` (l.1026), Step 4 uses it as
  `λ → ∞` at each fixed order (l.1158–1159), so it is stated for all sufficiently large `λ`
  at each order;
- `G_charged = det(I - M²)^{-1/2} (16q/z)^{λ²}`, `G_neutral = det(I - M²)^{-1/2}` are entered by
  their values (l.1038–1045), with `(16q/z)^{λ²} = e^{λ²𝓘₀}` (Lemma 3.4(iii));
- `ℬ(2, λ²+n, 1/8; z)`: the block at `c = 2`, internal weight `λ² + n`, all four external
  weights `1/8` (l.1047–1049), the value of the rational function `ℬ_j` at `Δ = λ² + n`, where
  it has no pole (l.1050–1053; for `λ² + n ≥ 1/24` this is Lemma 3.2(i) at `μ² = 1/24`);
- `c_n(λ²)`: a function of `λ` for each `n`, existential (it is determined by (3.8), `ℬ_0 = 1`);
  the limit along real `λ → +∞` at each fixed `n` (l.1106–1109);
- the generating function (l.1150–1156) without the fractional power:
  `(∑_n 16^n c_n^∞ q^n)² ∏_m (1 - q^{2m}) = 1`, which is all that Step 4 uses. -/
def Stmt_sub_c2_decomp : Prop :=
  ∃ (c : ℕ → ℝ → ℂ) (cinf : ℕ → ℂ),
    (∀ N : ℕ, ∀ᶠ lam : ℝ in atTop,
      coeff N (detInvSqrt.map (algebraMap ℚ ℂ) *
          (exp ℂ).subst (C ((lam : ℂ) ^ 2) * I0def sigmaStar (fun m => -sigmaStar m)) *
          detInvSqrt.map (algebraMap ℚ ℂ)) =
        ∑ n ∈ Finset.range (N + 1), c n lam *
          RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (n : ℂ))
            (Bsph (2 : ℂ) (fun _ => (1 / 8 : ℂ)) (N - n))) ∧
    (∀ n : ℕ, Tendsto (c n) atTop (𝓝 (cinf n))) ∧
    (mk fun n => (16 : ℂ) ^ n * cinf n) ^ 2 * (etaSqPow 1).map (algebraMap ℚ ℂ) = 1

/-- `e^{a𝓘₀(z)}`. -/
noncomputable def EI (a : ℂ) : PowerSeries ℂ :=
  (exp ℂ).subst (C a * I0def sigmaStar (fun m => -sigmaStar m))

/-- `ℬ(2, Δ, 1/8; z)` at a value `Δ`. -/
noncomputable def Bser2 (Δ : ℂ) : PowerSeries ℂ :=
  mk fun j => RatFunc.eval (RingHom.id ℂ) Δ (Bsph (2 : ℂ) (fun _ => (1 / 8 : ℂ)) j)

theorem constantCoeff_I0s (hJ2 : Cited_JacobiIdentities2) :
    constantCoeff (I0def sigmaStar (fun m => -sigmaStar m)) = 0 := by
  obtain ⟨g, hg, hg'⟩ := inZQ_I0 hJ2
  rw [hg']
  exact constantCoeff_map_zero _ hg

theorem EI_add (hJ2 : Cited_JacobiIdentities2) (a b : ℂ) : EI (a + b) = EI a * EI b := by
  have h0 := constantCoeff_I0s hJ2
  rw [EI, EI, EI, map_add, add_mul]
  exact exp_subst_add _ _ (by rw [map_mul, h0, mul_zero]) (by rw [map_mul, h0, mul_zero])

theorem EI_zero : EI 0 = 1 := by
  rw [EI, map_zero, zero_mul, exp_subst_zero]

theorem coeff_EI_shift (hJ2 : Cited_JacobiIdentities2) (a s2 n : ℂ) (m : ℕ)
    (hs : s2 = a + (n - 1 / 24)) :
    coeff m (EI (-a) * Bser2 (a + n)) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, coeff p.1 (EI (n - 1 / 24)) *
        coeff p.2 (EI (-s2) * Bser2 (s2 + 1 / 24)) := by
  subst hs
  have e1 : (n - 1 / 24) + -(a + (n - 1 / 24)) = -a := by ring
  have e2 : a + (n - 1 / 24) + 1 / 24 = a + n := by ring
  rw [← coeff_mul, ← mul_assoc, ← EI_add hJ2, e1, e2]

section Limit

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
set_option maxHeartbeats 1600000 in
/-- Step 4 of Lemma 3.7, the limit (sphere/paper.tex l.1158–1175): at each order in `z`,
`det(I - M²)^{-1} = ∑_n c_n^∞ z^n e^{(n - 1/24)𝓘₀} det(I - M²)^{-1/2}
exp(Φ_c^raw/24 + (Φ₁ + Φ₂)/8)`. -/
theorem c2_limit (hJ2 : Cited_JacobiIdentities2) {S1t S2c S21 S22 : MvPowerSeries ℕ+ ℂ}
    (hE : IsExpansionData S1t S2c S21 S22) (c : ℕ → ℝ → ℂ) (cinf : ℕ → ℂ)
    (hdec : ∀ N : ℕ, ∀ᶠ lam : ℝ in atTop,
      coeff N (detInvSqrt.map (algebraMap ℚ ℂ) * EI ((lam : ℂ) ^ 2) *
          detInvSqrt.map (algebraMap ℚ ℂ)) =
        ∑ n ∈ Finset.range (N + 1), c n lam * coeff (N - n) (Bser2 ((lam : ℂ) ^ 2 + (n : ℂ))))
    (hlim : ∀ n : ℕ, Tendsto (c n) atTop (𝓝 (cinf n))) (N : ℕ) :
    coeff N (detInvSqrt.map (algebraMap ℚ ℂ) * detInvSqrt.map (algebraMap ℚ ℂ)) =
      ∑ n ∈ Finset.range (N + 1), cinf n * coeff (N - n) (EI ((n : ℂ) - 1 / 24) *
        (detInvSqrt.map (algebraMap ℚ ℂ) * (exp ℂ).subst
          ((1 / 24 : ℂ) • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
            (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
            (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22))) := by
  set D := detInvSqrt.map (algebraMap ℚ ℂ) with hD
  set Linf := D * (exp ℂ).subst
    ((1 / 24 : ℂ) • PhiCraw S1t S2c sigmaStar (fun m => -sigmaStar m) +
      (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S21 +
      (1 / 8 : ℂ) • MvPowerSeries.subst sigmaStar S22) with hLinf
  -- Lemma 3.3(iii) at `c = 2`, `Δ_i = 1/8`
  have hμ : 0 < Real.sqrt (1 / 24) := Real.sqrt_pos.2 (by norm_num)
  have hμ2 : ((Real.sqrt (1 / 24) : ℝ) : ℂ) ^ 2 = 1 / 24 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    push_cast
    ring
  have hT : ∀ j : ℕ, Tendsto
      (fun l : ℝ => coeff j (EI (-(l : ℂ) ^ 2) * Bser2 ((l : ℂ) ^ 2 + 1 / 24)))
      atTop (𝓝 (coeff j Linf)) := by
    intro j
    have h := lam_limit hF hK hJ2 hE (Real.sqrt (1 / 24)) hμ (fun _ => (1 / 8 : ℝ)) j
    have h8 : (((1 / 8 : ℝ)) : ℂ) = 1 / 8 := by
      push_cast
      ring
    have e1 : (1 : ℂ) + 24 * (1 / 24) = 2 := by norm_num
    have e3 : (1 / 8 : ℂ) + 1 / 8 - 1 / 8 = 1 / 8 := by norm_num
    simp only [hμ2, h8, e1, e3] at h
    exact h
  -- the shifted `λ`
  have hsq : ∀ n : ℕ, Tendsto (fun l : ℝ => Real.sqrt (l ^ 2 + ((n : ℝ) - 1 / 24))) atTop atTop :=
    fun n => Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero))
  have hshift : ∀ (l : ℝ), 1 ≤ l → ∀ n : ℕ,
      ((Real.sqrt (l ^ 2 + ((n : ℝ) - 1 / 24)) : ℝ) : ℂ) ^ 2 = (l : ℂ) ^ 2 + ((n : ℂ) - 1 / 24) := by
    intro l hl n
    have h0 : (0 : ℝ) ≤ l ^ 2 + ((n : ℝ) - 1 / 24) := by
      have h1 : (1 : ℝ) ≤ l ^ 2 := one_le_pow₀ hl
      have h2 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    rw [← Complex.ofReal_pow, Real.sq_sqrt h0]
    push_cast
    ring
  have hkey : ∀ (l : ℝ), 1 ≤ l → ∀ n m : ℕ,
      coeff m (EI (-(l : ℂ) ^ 2) * Bser2 ((l : ℂ) ^ 2 + (n : ℂ))) =
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal m, coeff p.1 (EI ((n : ℂ) - 1 / 24)) *
          coeff p.2 (EI (-((Real.sqrt (l ^ 2 + ((n : ℝ) - 1 / 24)) : ℝ) : ℂ) ^ 2) *
            Bser2 (((Real.sqrt (l ^ 2 + ((n : ℝ) - 1 / 24)) : ℝ) : ℂ) ^ 2 + 1 / 24)) :=
    fun l hl n m => coeff_EI_shift hJ2 _ _ _ m (hshift l hl n)
  have hev : ∀ᶠ l : ℝ in atTop, coeff N (D * D) =
      ∑ n ∈ Finset.range (N + 1), c n l *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (N - n), coeff p.1 (EI ((n : ℂ) - 1 / 24)) *
          coeff p.2 (EI (-((Real.sqrt (l ^ 2 + ((n : ℝ) - 1 / 24)) : ℝ) : ℂ) ^ 2) *
            Bser2 (((Real.sqrt (l ^ 2 + ((n : ℝ) - 1 / 24)) : ℝ) : ℂ) ^ 2 + 1 / 24)) := by
    have hall : ∀ᶠ l : ℝ in atTop, ∀ k ∈ Finset.range (N + 1),
        coeff k (D * EI ((l : ℂ) ^ 2) * D) =
          ∑ n ∈ Finset.range (k + 1), c n l * coeff (k - n) (Bser2 ((l : ℂ) ^ 2 + (n : ℂ))) :=
      (Filter.eventually_all_finset _).2 fun k _ => hdec k
    filter_upwards [eventually_ge_atTop 1, hall] with l hl hk'
    have ha : D * D = EI (-(l : ℂ) ^ 2) * (D * EI ((l : ℂ) ^ 2) * D) := by
      rw [show EI (-(l : ℂ) ^ 2) * (D * EI ((l : ℂ) ^ 2) * D) =
        (EI (-(l : ℂ) ^ 2) * EI ((l : ℂ) ^ 2)) * (D * D) by ring, ← EI_add hJ2, neg_add_cancel,
        EI_zero, one_mul]
    have hb : ∀ k ≤ N, coeff k (D * EI ((l : ℂ) ^ 2) * D) =
        coeff k (∑ n ∈ Finset.range (N + 1),
          C (c n l) * (X ^ n * Bser2 ((l : ℂ) ^ 2 + (n : ℂ)))) := by
      intro k hk
      rw [hk' k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hk)), map_sum]
      calc ∑ n ∈ Finset.range (k + 1), c n l * coeff (k - n) (Bser2 ((l : ℂ) ^ 2 + (n : ℂ)))
          = ∑ n ∈ Finset.range (k + 1), c n l *
              (if n ≤ k then coeff (k - n) (Bser2 ((l : ℂ) ^ 2 + (n : ℂ))) else 0) :=
            Finset.sum_congr rfl fun n hn => by
              rw [if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))]
        _ = ∑ n ∈ Finset.range (N + 1), c n l *
              (if n ≤ k then coeff (k - n) (Bser2 ((l : ℂ) ^ 2 + (n : ℂ))) else 0) :=
            Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk)) fun n _ hn => by
              rw [if_neg (fun h => hn (Finset.mem_range.2 (Nat.lt_succ_iff.2 h))), mul_zero]
        _ = _ := Finset.sum_congr rfl fun n _ => by rw [coeff_C_mul, coeff_X_pow_mul']
    rw [ha, coeff_mul_congr_le _ hb, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [show EI (-(l : ℂ) ^ 2) * (C (c n l) * (X ^ n * Bser2 ((l : ℂ) ^ 2 + (n : ℂ)))) =
      C (c n l) * (X ^ n * (EI (-(l : ℂ) ^ 2) * Bser2 ((l : ℂ) ^ 2 + (n : ℂ)))) by ring,
      coeff_C_mul, coeff_X_pow_mul', if_pos hn', hkey l hl n (N - n)]
  have hlimit : Tendsto (fun l : ℝ => ∑ n ∈ Finset.range (N + 1), c n l *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (N - n), coeff p.1 (EI ((n : ℂ) - 1 / 24)) *
          coeff p.2 (EI (-((Real.sqrt (l ^ 2 + ((n : ℝ) - 1 / 24)) : ℝ) : ℂ) ^ 2) *
            Bser2 (((Real.sqrt (l ^ 2 + ((n : ℝ) - 1 / 24)) : ℝ) : ℂ) ^ 2 + 1 / 24))) atTop
      (𝓝 (∑ n ∈ Finset.range (N + 1), cinf n *
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (N - n), coeff p.1 (EI ((n : ℂ) - 1 / 24)) *
          coeff p.2 Linf)) :=
    tendsto_finset_sum _ fun n _ => (hlim n).mul
      (tendsto_finset_sum _ fun p _ => tendsto_const_nhds.mul ((hT p.2).comp (hsq n)))
  have huniq := tendsto_nhds_unique (tendsto_const_nhds.congr' hev) hlimit
  rw [huniq]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_mul]

end Limit

end Virasoro.Sphere
