import Virasoro.Sphere.Proofs.Sec3GaussStepOne
import Virasoro.Sphere.Proofs.Sec3GaussSaddleCov
import Virasoro.Sphere.Proofs.Sec3SaddleI0d

/-!
# The shift `C J = λ(σ_*, σ̄_*)` and the saddle value (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.663–668 and l.684.  Completing the square shifts the variables to the saddle
point: `C J = λ (σ_*, σ̄_*)` in `ℂ((t))[[z]]/(z^{N+1})`, by the saddle-point equations and the
uniqueness of their solution; and `½ J·CJ = λ² 𝓘₀(z)`, the saddle value.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩

theorem sum_Icc_fin {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Icc 1 N, f n = ∑ j : Fin N, f ((j : ℕ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Fin.sum_univ_castSucc]
    simp

/-- The coefficient of `z^k` in the truncation `PhiK K` does not depend on `K ≥ k`. -/
theorem coeff_PhiK_stable (k K : ℕ) (h : k ≤ K) :
    PowerSeries.coeff k (PhiK K) = PowerSeries.coeff k (PhiK k) := by
  have hX : ∀ (c : ℚ) (e : ℕ) (f : PowerSeries ℚ), k < e →
      PowerSeries.coeff k (PowerSeries.C c * (PowerSeries.X ^ e * f)) = 0 := fun c e f he => by
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega), mul_zero]
  induction K, h using Nat.le_induction with
  | base => rfl
  | succ K hK ih =>
    rw [← ih, PhiK, PhiK]
    simp only [map_add, PowerSeries.coeff_C_mul]
    have h1 : PowerSeries.coeff k (∑ n ∈ Icc 1 (K + 1),
        PowerSeries.C (1 / (n : ℚ)) * (PowerSeries.X ^ n * (aSer n * aSer n))) =
        PowerSeries.coeff k (∑ n ∈ Icc 1 K,
          PowerSeries.C (1 / (n : ℚ)) * (PowerSeries.X ^ n * (aSer n * aSer n))) := by
      rw [Finset.sum_Icc_succ_top (by omega), map_add, hX _ _ _ (by omega), add_zero]
    have h2 : PowerSeries.coeff k (∑ n ∈ Icc 1 (K + 1),
        PowerSeries.C (2 * halfBinom n * (1 / (n : ℚ))) * (PowerSeries.X ^ n * aSer n)) =
        PowerSeries.coeff k (∑ n ∈ Icc 1 K,
          PowerSeries.C (2 * halfBinom n * (1 / (n : ℚ))) * (PowerSeries.X ^ n * aSer n)) := by
      rw [Finset.sum_Icc_succ_top (by omega), map_add, hX _ _ _ (by omega), add_zero]
    have h3 : PowerSeries.coeff k (∑ m ∈ Icc 1 (K + 1), ∑ n ∈ Icc 1 (K + 1),
        PowerSeries.C (-(Bcoef m n * (1 / (m : ℚ)) * (1 / (n : ℚ)))) *
          (PowerSeries.X ^ (m + n) * (aSer m * aSer n))) =
        PowerSeries.coeff k (∑ m ∈ Icc 1 K, ∑ n ∈ Icc 1 K,
          PowerSeries.C (-(Bcoef m n * (1 / (m : ℚ)) * (1 / (n : ℚ)))) *
            (PowerSeries.X ^ (m + n) * (aSer m * aSer n))) := by
      rw [Finset.sum_Icc_succ_top (by omega), map_add, map_sum, map_sum, map_sum]
      rw [Finset.sum_eq_zero (s := Icc 1 (K + 1)) fun n _ => hX _ _ _ (by omega), add_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_Icc_succ_top (by omega), map_add, hX _ _ _ (by omega), add_zero]
    rw [h1, h2, h3]

section Val

variable (N : ℕ)

/-- `ℂ[[z]] → ℂ((t))[[z]]/(z^{N+1})`. -/
noncomputable def iotaZ : PowerSeries ℂ →+* TR N LL :=
  (mkT N LL).comp (PowerSeries.map HahnSeries.C)

theorem iotaZ_map (p : PowerSeries ℚ) : iotaZ N (p.map (algebraMap ℚ ℂ)) = phiL N p := by
  rw [iotaZ, phiL, RingHom.comp_apply, RingHom.comp_apply]
  congr 1

theorem iotaZ_C (c : ℂ) : iotaZ N (PowerSeries.C c) = psiL N (HahnSeries.C c) := by
  rw [iotaZ, psiL, RingHom.comp_apply, RingHom.comp_apply, PowerSeries.map_C]

theorem iotaZ_X : iotaZ N PowerSeries.X = phiL N PowerSeries.X := by
  rw [iotaZ, RingHom.comp_apply, PowerSeries.map_X, phiL_X]

/-- `a_m(z)` in `ℂ((t))[[z]]/(z^{N+1})`, for the mode `m = i + 1`. -/
noncomputable def aT (i : Fin N) : TR N LL := phiL N (aSer ((i : ℕ) + 1))

/-- The imaginary unit in `ℂ((t))[[z]]/(z^{N+1})`. -/
noncomputable def iT : TR N LL := psiL N (HahnSeries.C Complex.I)

theorem iT_sq : iT N * iT N = -1 := by
  rw [iT, ← map_mul, ← map_mul, Complex.I_mul_I]
  simp

theorem psiL_ratCast (q : ℚ) : psiL N (HahnSeries.C (q : ℂ)) = algebraMap ℚ (TR N LL) q :=
  RingHom.congr_fun (Subsingleton.elim (((psiL N).comp HahnSeries.C).comp (algebraMap ℚ ℂ))
    (algebraMap ℚ (TR N LL))) q

theorem psiL_Acoef (m : ℕ) :
    psiL N (HahnSeries.C (Acoef m)) = -2 * iT N * algebraMap ℚ (TR N LL) (halfBinom m) := by
  simp only [Acoef, map_mul, map_neg, map_ofNat, psiL_ratCast, iT]

/-- `1/m` for the mode `m = i + 1`. -/
noncomputable def qT (i : Fin N) : TR N LL :=
  algebraMap ℚ (TR N LL) (1 / (((i : ℕ) + 1 : ℕ) : ℚ))

/-- The saddle-point equation for `a_m`, modulo `z^{N+1}` (sphere/paper.tex l.666–668). -/
theorem delta_TR (m : ℕ) :
    phiL N (aSer m) = algebraMap ℚ (TR N LL) (halfBinom m) -
      ∑ j : Fin N, algebraMap ℚ (TR N LL) (Bcoef m ((j : ℕ) + 1)) * qT N j *
        (phiL N PowerSeries.X ^ ((j : ℕ) + 1) * aT N j) := by
  obtain ⟨g, hg⟩ := Delta_dvd m N
  have h := congrArg (phiL N) hg
  rw [map_mul, map_pow, phiL_X_pow, zero_mul, map_add, map_sub, map_sum, sum_Icc_fin] at h
  simp only [map_mul, map_pow, phi_C] at h
  simp only [qT, aT]
  linear_combination h

/-- `σ_{*,m}` in `ℂ((t))[[z]]/(z^{N+1})`: `i a_m z^m/m`, `m = i + 1`. -/
noncomputable def sgL (i : Fin N) : TR N LL :=
  iT N * qT N i * aT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1)

/-- The saddle point `(σ_*, σ̄_*)`, `σ̄_* = -σ_*`. -/
noncomputable def sgT : Modes N → TR N LL := Sum.elim (sgL N) (fun i => -sgL N i)

theorem iotaZ_sigmaStar (i : Fin N) : iotaZ N (sigmaStar (modeEmb N i)) = sgL N i := by
  simp only [sigmaStar_eq, map_mul, map_pow, iotaZ_C, iotaZ_map, iotaZ_X, modeEmb_coe, sgL, iT,
    qT, aT]
  have e : (1 / (((i : ℕ) + 1 : ℕ) : ℂ)) = ((1 / (((i : ℕ) + 1 : ℕ) : ℚ) : ℚ) : ℂ) := by
    push_cast
    rfl
  rw [e, psiL_ratCast]
  ring

theorem two_mul_half : (2 : TR N LL) * algebraMap ℚ (TR N LL) (1 / 2) = 1 := by
  rw [← map_ofNat (algebraMap ℚ (TR N LL)) 2, ← map_mul]
  norm_num

theorem e0_eq (i : Fin N) :
    e0 (phiL N) i = algebraMap ℚ (TR N LL) (1 / 2) * qT N i *
      phiL N PowerSeries.X ^ ((i : ℕ) + 1) := by
  rw [e0, qT, ← map_mul]
  congr 2
  rw [one_div, one_div, one_div, mul_inv]

theorem MR_eq (i j : Fin N) :
    MR N (phiL N) i j = algebraMap ℚ (TR N LL) (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1)) * qT N i *
      phiL N PowerSeries.X ^ ((i : ℕ) + 1) := by
  rw [MR_apply, qT, ← map_mul]
  congr 2
  rw [div_eq_mul_one_div]

/-- Step 2 of Lemma 3.3(iii) (sphere/paper.tex l.663–668): `C J = λ (σ_*, σ̄_*)`. -/
theorem CJ_eq (a : Modes N) :
    ∑ b, covN N (phiL N) N a b * JL N (psiL N) b = psiL N tL⁻¹ * sgT N a := by
  refine covN_mulVec_unique (phiL_X_pow N) (JL N (psiL N)) (fun a => psiL N tL⁻¹ * sgT N a)
    ?_ ?_ a
  · intro i
    show psiL N tL⁻¹ * sgT N (Sum.inl i) = e0 (phiL N) i * JL N (psiL N) (Sum.inr i) +
      ∑ j, MR N (phiL N) i j * (psiL N tL⁻¹ * sgT N (Sum.inr j))
    have hd := delta_TR N ((i : ℕ) + 1)
    have hs : ∀ j : Fin N, MR N (phiL N) i j * (psiL N tL⁻¹ * sgT N (Sum.inr j)) =
        (-(psiL N tL⁻¹ * iT N * qT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1))) *
          (algebraMap ℚ (TR N LL) (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1)) * qT N j *
            (phiL N PowerSeries.X ^ ((j : ℕ) + 1) * aT N j)) := fun j => by
      rw [MR_eq, sgT, Sum.elim_inr, sgL]
      ring
    rw [Finset.sum_congr rfl fun j _ => hs j, ← Finset.mul_sum, e0_eq, sgT, JL, Sum.elim_inl,
      Sum.elim_inr, psiL_Acoef, sgL]
    have hh := two_mul_half N
    rw [show aT N i = phiL N (aSer ((i : ℕ) + 1)) from rfl]
    linear_combination (psiL N tL⁻¹ * iT N * qT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1)) * hd
      - (psiL N tL⁻¹ * iT N * qT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1) *
        algebraMap ℚ (TR N LL) (halfBinom ((i : ℕ) + 1))) * hh
  · intro i
    show psiL N tL⁻¹ * sgT N (Sum.inr i) = e0 (phiL N) i * JL N (psiL N) (Sum.inl i) +
      ∑ j, MR N (phiL N) i j * (psiL N tL⁻¹ * sgT N (Sum.inl j))
    have hd := delta_TR N ((i : ℕ) + 1)
    have hs : ∀ j : Fin N, MR N (phiL N) i j * (psiL N tL⁻¹ * sgT N (Sum.inl j)) =
        (psiL N tL⁻¹ * iT N * qT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1)) *
          (algebraMap ℚ (TR N LL) (Bcoef ((i : ℕ) + 1) ((j : ℕ) + 1)) * qT N j *
            (phiL N PowerSeries.X ^ ((j : ℕ) + 1) * aT N j)) := fun j => by
      rw [MR_eq, sgT, Sum.elim_inl, sgL]
      ring
    rw [Finset.sum_congr rfl fun j _ => hs j, ← Finset.mul_sum, e0_eq, sgT, JL, Sum.elim_inl,
      Sum.elim_inr, psiL_Acoef, sgL]
    have hh := two_mul_half N
    rw [show aT N i = phiL N (aSer ((i : ℕ) + 1)) from rfl]
    linear_combination
      (-(psiL N tL⁻¹ * iT N * qT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1))) * hd
      + (psiL N tL⁻¹ * iT N * qT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1) *
        algebraMap ℚ (TR N LL) (halfBinom ((i : ℕ) + 1))) * hh

end Val

end Virasoro.Sphere
