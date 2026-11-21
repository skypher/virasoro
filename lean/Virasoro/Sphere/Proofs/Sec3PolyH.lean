import Virasoro.Sphere.Proofs.Sec3PolyDet
import Virasoro.Sphere.Proofs.Sec3FockVerma

/-!
# Sphere paper Lemma 3.2: the polynomial form of `H_N` and the lemma

sphere/paper.tex l.495–499: `Φ̃⁻¹` has polynomial coefficients in `(c,Δ,Δ_i)` and
`det G_m ∣ det G_N` for `m ≤ N`, so `H_N det G_N = P_N ∈ ℚ[c,Δ,Δ_1,…,Δ_4]`.
-/

namespace Virasoro.Sphere

open Polynomial

theorem isPolyFam_zero : IsPolyFam fun _ _ => (0 : RatFunc ℂ) :=
  ⟨0, fun _ _ => by rw [map_zero]⟩

/-- The coefficients of `Φ̃⁻¹` are polynomials over `ℚ` in `(c,Δ,Δ_i)`. -/
theorem isPolyFam_PhiTilde_inv (n : ℕ) :
    IsPolyFam fun c Δe => PowerSeries.coeff n (PhiTilde c Δe)⁻¹ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hcc : ∀ (c : ℂ) (Δe : Fin 4 → ℂ),
        PowerSeries.constantCoeff (PhiTilde c Δe) = 1 := fun c Δe => by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PhiTilde_coeff_zero]
    rcases n.eq_zero_or_pos with rfl | hn
    · refine ⟨1, fun c Δe => ?_⟩
      beta_reduce
      rw [PowerSeries.coeff_inv, if_pos rfl, hcc, inv_one, map_one]
    · have hterm : ∀ x : ℕ × ℕ, IsPolyFam fun c Δe =>
          if x.2 < n then PowerSeries.coeff x.1 (PhiTilde c Δe) *
            PowerSeries.coeff x.2 (PhiTilde c Δe)⁻¹ else 0 := by
        intro x
        by_cases hx : x.2 < n
        · simp only [if_pos hx]
          exact (isPolyFam_PhiTilde x.1).mul (ih x.2 hx)
        · simp only [if_neg hx]
          exact isPolyFam_zero
      obtain ⟨Q, hQ⟩ := (IsPolyFam.const (-1)).mul
        (IsPolyFam.sum (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)) fun x _ => hterm x)
      refine ⟨Q, fun c Δe => ?_⟩
      rw [← hQ]
      beta_reduce
      rw [PowerSeries.coeff_inv, if_neg hn.ne', hcc, inv_one, map_neg, map_one]

theorem coeff_zq_pow_rat (j m : ℕ) :
    PowerSeries.coeff j (zq (RatFunc ℂ) ^ m) =
      algebraMap ℚ (RatFunc ℂ) (PowerSeries.coeff j (zq ℚ ^ m)) := by
  rw [← map_zq (algebraMap ℚ (RatFunc ℂ)), ← map_pow, PowerSeries.coeff_map]

/-- `H_N det G_N ∈ ℚ[c,Δ,Δ_1,…,Δ_4]`. -/
theorem isPolyFam_Hsph_det (hK : Cited_KacDeterminant) (N : ℕ) :
    IsPolyFam fun c Δe => Hsph c Δe N * algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det := by
  have hBz : ∀ j ≤ N, IsPolyFam fun c Δe =>
      PowerSeries.coeff j (BzSeries c Δe) * algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det := by
    intro j hj
    obtain ⟨Q, hQ⟩ := IsPolyFam.sum (Finset.range (j + 1))
      (F := fun m c Δe => (Bsph c Δe m * algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det) *
        algebraMap ℚ (RatFunc ℂ) (PowerSeries.coeff j (zq ℚ ^ m)))
      fun m hm => (isPolyFam_Bsph_det hK (by have := Finset.mem_range.mp hm; omega)).mul
        (IsPolyFam.const _)
    refine ⟨Q, fun c Δe => ?_⟩
    rw [← hQ]
    beta_reduce
    unfold BzSeries
    rw [PowerSeries.coeff_mk, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [coeff_zq_pow_rat]
    ring
  obtain ⟨Q, hQ⟩ := (IsPolyFam.const (1 / 16 ^ N)).mul
    (IsPolyFam.sum (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ))
      (F := fun p c Δe => PowerSeries.coeff p.1 (PhiTilde c Δe)⁻¹ *
        (PowerSeries.coeff p.2 (BzSeries c Δe) *
          algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det))
      fun p hp => (isPolyFam_PhiTilde_inv p.1).mul
        (hBz p.2 (by have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega)))
  refine ⟨Q, fun c Δe => ?_⟩
  have e : (∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)), PowerSeries.coeff p.1 (PhiTilde c Δe)⁻¹ *
      PowerSeries.coeff p.2 (BzSeries c Δe)) *
        algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det =
      ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        PowerSeries.coeff p.1 (PhiTilde c Δe)⁻¹ *
        (PowerSeries.coeff p.2 (BzSeries c Δe) *
          algebraMap ℂ[X] (RatFunc ℂ) (gramPoly c N).det) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _
  have h16 : algebraMap ℚ (RatFunc ℂ) (1 / 16 ^ N) = 1 / 16 ^ N := by
    simp
  rw [← hQ]
  beta_reduce
  rw [← e, h16, Hsph, Hseries, PowerSeries.coeff_mul]
  ring

/-- Lemma 3.2 of the sphere paper (Fock–Verma equivalence and polynomial extension), from the
Feigin–Fuchs operators cited at sphere/paper.tex l.428, l.443–444 and the Kac determinant formula
used at l.472–480 and l.495.
Paper label: lem:fock-verma -/
theorem lem_fock_verma_of_cited (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant) :
    Stmt_lem_fock_verma :=
  lem_fock_verma_of_iii hF hK fun N hyp => by
    obtain ⟨Q, hQ⟩ := isPolyFam_Hsph_det hK N
    exact largeDeltaAt_of_poly N Q hQ hyp

example (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant) : Stmt_lem_fock_verma :=
  lem_fock_verma_of_cited hF hK

end Virasoro.Sphere
