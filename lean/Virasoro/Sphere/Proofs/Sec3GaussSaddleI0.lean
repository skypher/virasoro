import Virasoro.Sphere.Proofs.Sec3GaussSaddleVal

/-!
# The saddle value `½ J·CJ = λ² 𝓘₀(z)` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.684: "The `λ²` saddle value factors out as `e^{λ²𝓘₀(z)}`."  With
`C J = λ(σ_*, σ̄_*)`, `½ J·CJ = λ² ∑_m A_m σ_{*,m}`, and by the saddle-point equations this is
`λ²` times the saddle value `𝓘₀ = -2∑ m z^{-m} σ_m σ̄_m + S⁽⁰⁾(σ_*) + S̃⁽⁰⁾(σ̄_*)`, modulo
`z^{N+1}`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset

local notation "LL" => ℂ⸨X⸩

section I0

variable (N : ℕ)

theorem phiL_PhiK :
    phiL N (PhiK N) =
      algebraMap ℚ (TR N LL) (-2) * ∑ m : Fin N,
          qT N m * (phiL N PowerSeries.X ^ ((m : ℕ) + 1) * (aT N m * aT N m)) +
        algebraMap ℚ (TR N LL) 2 *
          (∑ m : Fin N, algebraMap ℚ (TR N LL)
              (2 * halfBinom ((m : ℕ) + 1) * (1 / (((m : ℕ) + 1 : ℕ) : ℚ))) *
              (phiL N PowerSeries.X ^ ((m : ℕ) + 1) * aT N m) +
            ∑ m : Fin N, ∑ n : Fin N, algebraMap ℚ (TR N LL)
              (-(Bcoef ((m : ℕ) + 1) ((n : ℕ) + 1) * (1 / (((m : ℕ) + 1 : ℕ) : ℚ)) *
                (1 / (((n : ℕ) + 1 : ℕ) : ℚ)))) *
              (phiL N PowerSeries.X ^ (((m : ℕ) + 1) + ((n : ℕ) + 1)) *
                (aT N m * aT N n))) := by
  rw [PhiK]
  simp only [map_add, map_mul, map_sum, map_pow, phi_C, sum_Icc_fin]
  rfl

/-- The saddle value modulo `z^{N+1}`: `𝓘₀ ≡ ∑_{m≤N} 2 h_m a_m z^m/m = ∑_m A_m σ_{*,m}`. -/
theorem phiL_I0Q :
    phiL N I0Q = ∑ m : Fin N, 2 * (qT N m * phiL N PowerSeries.X ^ ((m : ℕ) + 1) * aT N m *
      algebraMap ℚ (TR N LL) (halfBinom ((m : ℕ) + 1))) := by
  have h1 : phiL N I0Q = phiL N (PhiK N) := by
    rw [phiL, RingHom.comp_apply, RingHom.comp_apply, mkT_eq_iff]
    intro k hk
    rw [PowerSeries.coeff_map, PowerSeries.coeff_map, I0Q, PowerSeries.coeff_mk,
      coeff_PhiK_stable k N hk]
  have key : ∀ m : Fin N,
      qT N m * (phiL N PowerSeries.X ^ ((m : ℕ) + 1) * (aT N m * aT N m)) -
        ∑ n : Fin N, algebraMap ℚ (TR N LL)
          (-(Bcoef ((m : ℕ) + 1) ((n : ℕ) + 1) * (1 / (((m : ℕ) + 1 : ℕ) : ℚ)) *
            (1 / (((n : ℕ) + 1 : ℕ) : ℚ)))) *
          (phiL N PowerSeries.X ^ (((m : ℕ) + 1) + ((n : ℕ) + 1)) * (aT N m * aT N n)) =
      qT N m * phiL N PowerSeries.X ^ ((m : ℕ) + 1) * aT N m *
        algebraMap ℚ (TR N LL) (halfBinom ((m : ℕ) + 1)) := by
    intro m
    have hd := delta_TR N ((m : ℕ) + 1)
    have hs : ∀ n : Fin N, algebraMap ℚ (TR N LL)
          (-(Bcoef ((m : ℕ) + 1) ((n : ℕ) + 1) * (1 / (((m : ℕ) + 1 : ℕ) : ℚ)) *
            (1 / (((n : ℕ) + 1 : ℕ) : ℚ)))) *
          (phiL N PowerSeries.X ^ (((m : ℕ) + 1) + ((n : ℕ) + 1)) * (aT N m * aT N n)) =
        (-(qT N m * phiL N PowerSeries.X ^ ((m : ℕ) + 1) * aT N m)) *
          (algebraMap ℚ (TR N LL) (Bcoef ((m : ℕ) + 1) ((n : ℕ) + 1)) * qT N n *
            (phiL N PowerSeries.X ^ ((n : ℕ) + 1) * aT N n)) := fun n => by
      rw [map_neg, map_mul, map_mul, pow_add, qT, qT]
      ring
    rw [Finset.sum_congr rfl fun n _ => hs n, ← Finset.mul_sum]
    have ha : aT N m = phiL N (aSer ((m : ℕ) + 1)) := rfl
    linear_combination (qT N m * phiL N PowerSeries.X ^ ((m : ℕ) + 1) * aT N m) * hd +
      (qT N m * phiL N PowerSeries.X ^ ((m : ℕ) + 1) * aT N m) * ha
  have hT2 : ∀ m : Fin N, algebraMap ℚ (TR N LL)
        (2 * halfBinom ((m : ℕ) + 1) * (1 / (((m : ℕ) + 1 : ℕ) : ℚ))) *
        (phiL N PowerSeries.X ^ ((m : ℕ) + 1) * aT N m) =
      2 * (qT N m * phiL N PowerSeries.X ^ ((m : ℕ) + 1) * aT N m *
        algebraMap ℚ (TR N LL) (halfBinom ((m : ℕ) + 1))) := fun m => by
    rw [map_mul, map_mul, map_ofNat, qT]
    ring
  have hkeysum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin N))) rfl fun m _ => key m
  rw [Finset.sum_sub_distrib] at hkeysum
  rw [h1, phiL_PhiK, map_neg, map_ofNat, Finset.sum_congr rfl fun m _ => hT2 m]
  simp only [← Finset.mul_sum]
  linear_combination (-2) * hkeysum

theorem iotaZ_I0 : iotaZ N (I0def sigmaStar (fun m => -sigmaStar m)) = phiL N I0Q := by
  have h : I0def sigmaStar (fun m => -sigmaStar m) = I0Q.map (algebraMap ℚ ℂ) := by
    ext k
    rw [coeff_I0def_sigmaStar, PowerSeries.coeff_map, I0Q, PowerSeries.coeff_mk]
    rfl
  rw [h, iotaZ_map]

/-- Step 2 of Lemma 3.3(iii), the saddle value (sphere/paper.tex l.684): `½ J·CJ = λ² 𝓘₀(z)`
modulo `z^{N+1}`. -/
theorem JCJ_eq :
    (1 / 2 : ℚ) • ∑ a, ∑ b, JL N (psiL N) a * covN N (phiL N) N a b * JL N (psiL N) b =
      psiL N tL⁻¹ ^ 2 * iotaZ N (I0def sigmaStar (fun m => -sigmaStar m)) := by
  have h1 : ∀ a, ∑ b, JL N (psiL N) a * covN N (phiL N) N a b * JL N (psiL N) b =
      JL N (psiL N) a * (psiL N tL⁻¹ * sgT N a) := fun a => by
    rw [← CJ_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hsm : ∀ x : TR N LL, (1 / 2 : ℚ) • x = algebraMap ℚ (TR N LL) (1 / 2) * x := fun x =>
    Algebra.smul_def (1 / 2 : ℚ) x
  rw [Finset.sum_congr rfl fun a _ => h1 a, Fintype.sum_sum_type, iotaZ_I0, phiL_I0Q,
    hsm, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [JL, sgT, Sum.elim_inl, Sum.elim_inr, psiL_Acoef, sgL]
  linear_combination
    (-4 * algebraMap ℚ (TR N LL) (1 / 2) * psiL N tL⁻¹ ^ 2 *
      (qT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1) * aT N i *
        algebraMap ℚ (TR N LL) (halfBinom ((i : ℕ) + 1)))) * iT_sq N +
    (2 * psiL N tL⁻¹ ^ 2 * (qT N i * phiL N PowerSeries.X ^ ((i : ℕ) + 1) * aT N i *
        algebraMap ℚ (TR N LL) (halfBinom ((i : ℕ) + 1)))) * two_mul_half N

end I0

end Virasoro.Sphere
