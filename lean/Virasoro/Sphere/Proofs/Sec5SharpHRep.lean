import Virasoro.Sphere.Proofs.Sec5SharpB
import Virasoro.Sphere.Proofs.Sec4PolyU

/-!
# Theorem 5.5: the summand of `H_N` as a polynomial in the external weights

sphere/paper.tex l.1703–1789.  The value `H_M(c,μ,Δ_i)` at a point `μ` where `ℬ_m(c,·,Δ_i)`,
`m ≤ M`, are regular is `[q^M](Φ̃(c,μ,Δ_i)⁻¹ ∑_m ℬ_m(c,μ,Δ_i) z(q)^m)/16^M`; the coefficients of
`Φ̃⁻¹` are one polynomial over `ℚ` in `(c,Δ,Δ_i)` over every field (`isPolyFamU_PhiTilde_inv`).
Hence over `K4 = ℂ(Δ₁,…,Δ₄)` the value is the image of one polynomial `HR c μ M` in
`ℂ[Δ₁,…,Δ₄]`, and the value of `HR c μ M` at a complex point `v` is `H_M(c,μ,v)`.
-/

namespace Virasoro.Sphere

open Polynomial Finset

/-- The universal polynomial over `ℚ` in `(c,Δ,Δ₁,…,Δ₄)` of `[q^n] Φ̃⁻¹`. -/
noncomputable def QPhiInv (n : ℕ) : MvPolynomial (Fin 6) ℚ := (isPolyFamU_PhiTilde_inv n).choose

theorem QPhiInv_spec (n : ℕ) (𝔽 : Type) [Field 𝔽] [CharZero 𝔽] (c : 𝔽) (Δe : Fin 4 → 𝔽) :
    PowerSeries.coeff n (PhiTilde c Δe)⁻¹ = MvPolynomial.aeval (vec6U c Δe) (QPhiInv n) :=
  (isPolyFamU_PhiTilde_inv n).choose_spec 𝔽 c Δe

section Field

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

/-- The point `(c, Δ, Δ₁, …, Δ₄)` of `𝔽[X]⁶`. -/
noncomputable abbrev vec6P (c : 𝔽) (Δe : Fin 4 → 𝔽) : Fin 6 → 𝔽[X] :=
  ![C c, X, C (Δe 0), C (Δe 1), C (Δe 2), C (Δe 3)]

/-- The point `(c, μ, Δ₁, …, Δ₄)` of `𝔽⁶`. -/
noncomputable abbrev vec6At (c μ : 𝔽) (Δe : Fin 4 → 𝔽) : Fin 6 → 𝔽 :=
  ![c, μ, Δe 0, Δe 1, Δe 2, Δe 3]

theorem vec6U_eq (c : 𝔽) (Δe : Fin 4 → 𝔽) :
    vec6U c Δe = algebraMap 𝔽[X] (RatFunc 𝔽) ∘ vec6P c Δe := by
  ext i
  fin_cases i <;> simp [vec6U, vec6P, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

theorem eval_aeval_vec6P (c μ : 𝔽) (Δe : Fin 4 → 𝔽) (Q : MvPolynomial (Fin 6) ℚ) :
    (MvPolynomial.aeval (vec6P c Δe) Q).eval μ = MvPolynomial.aeval (vec6At c μ Δe) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, Polynomial.algebraMap_apply, eval_C]
  | add p q hp hq => rw [map_add, map_add, eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    congr 1
    fin_cases i <;> simp [vec6P, vec6At]

/-- `[q^n] Φ̃(c,μ,Δ_i)⁻¹ = Q_n(c,μ,Δ_i)`. -/
theorem coeff_PhiAt_inv (c μ : 𝔽) (Δe : Fin 4 → 𝔽) (n : ℕ) :
    PowerSeries.coeff n (PhiAt c μ Δe)⁻¹ = MvPolynomial.aeval (vec6At c μ Δe) (QPhiInv n) := by
  rw [← evS_PhiTilde_inv c μ Δe, evS, PowerSeries.coeff_mk, QPhiInv_spec n 𝔽 c Δe,
    vec6U_eq, MvPolynomial.aeval_algebraMap_apply, evalAt_algebraMap, eval_aeval_vec6P]

/-- `H_M` at a point `μ` where `ℬ_m`, `m ≤ M`, are regular, as a finite sum. -/
theorem evalAt_Hsph_sum (c μ : 𝔽) (Δe : Fin 4 → 𝔽) (M : ℕ)
    (hreg : ∀ m ≤ M, RegAt μ (Bsph c Δe m)) :
    evalAt μ (Hsph c Δe M) =
      (∑ x ∈ antidiagonal M, MvPolynomial.aeval (vec6At c μ Δe) (QPhiInv x.1) *
        ∑ m ∈ range (x.2 + 1), evalAt μ (Bsph c Δe m) *
          algebraMap ℚ 𝔽 (PowerSeries.coeff x.2 (zq ℚ ^ m))) * ((16 : 𝔽) ^ M)⁻¹ := by
  rw [evalAt_Hsph c μ Δe M hreg, div_eq_mul_inv, PowerSeries.coeff_mul]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [coeff_PhiAt_inv, compS, PowerSeries.coeff_mk]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  rw [← map_zq (algebraMap ℚ 𝔽), ← map_pow, PowerSeries.coeff_map]

end Field

/-! ### The representative in `ℂ[Δ₁,…,Δ₄]` -/

/-- `Q_n(c,μ,Δ₁,…,Δ₄)` in `ℂ[Δ₁,…,Δ₄]`. -/
noncomputable def QP (c μ : ℂ) (n : ℕ) : MvPolynomial (Fin 4) ℂ :=
  MvPolynomial.aeval (![MvPolynomial.C c, MvPolynomial.C μ, MvPolynomial.X 0, MvPolynomial.X 1,
    MvPolynomial.X 2, MvPolynomial.X 3] : Fin 6 → MvPolynomial (Fin 4) ℂ) (QPhiInv n)

/-- `H_M(c,μ,Δ_i)` as a polynomial in `Δ₁,…,Δ₄`. -/
noncomputable def HR (c μ : ℂ) (M : ℕ) : MvPolynomial (Fin 4) ℂ :=
  (∑ x ∈ antidiagonal M, QP c μ x.1 *
    ∑ m ∈ range (x.2 + 1), BR c μ m *
      MvPolynomial.C (algebraMap ℚ ℂ (PowerSeries.coeff x.2 (zq ℚ ^ m))))
    * MvPolynomial.C (((16 : ℂ) ^ M)⁻¹)

/-- A ring hom commutes with `aeval` over `ℚ`. -/
theorem ringHom_aeval6 {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →+* B) (w : Fin 6 → A) (Q : MvPolynomial (Fin 6) ℚ) :
    f (MvPolynomial.aeval w Q) = MvPolynomial.aeval (f ∘ w) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
    exact RingHom.congr_fun (RingHom.ext_rat (f.comp (algebraMap ℚ A)) (algebraMap ℚ B)) r
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, Function.comp_apply]

theorem ratK4 (q : ℚ) : algebraMap ℚ K4 q = cK (algebraMap ℚ ℂ q) :=
  RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ K4) ((algebraMap ℂ K4).comp (algebraMap ℚ ℂ))) q

theorem algebraMap_QP (c μ : ℂ) (n : ℕ) :
    algebraMap (MvPolynomial (Fin 4) ℂ) K4 (QP c μ n) =
      MvPolynomial.aeval (vec6At (cK c) (cK μ) ΔK) (QPhiInv n) := by
  rw [QP, ringHom_aeval6]
  congr 1
  ext i
  fin_cases i <;> simp [vec6At, algebraMap_C_K4, ΔK]

theorem eval_QP (c μ : ℂ) (n : ℕ) (v : Fin 4 → ℂ) :
    MvPolynomial.eval v (QP c μ n) = MvPolynomial.aeval (vec6At c μ v) (QPhiInv n) := by
  rw [QP, ringHom_aeval6]
  congr 1
  ext i
  fin_cases i <;> simp [vec6At]

/-- (H1): over `K4`, the value of `H_M` at `μ` is the image of `HR c μ M`. -/
theorem evalHsph_K4 {c μ : ℂ} {M : ℕ} (h : ∀ m ≤ M, (gram c μ m).det ≠ 0) :
    RatFunc.eval (RingHom.id K4) (cK μ) (Hsph (cK c) ΔK M) =
      algebraMap (MvPolynomial (Fin 4) ℂ) K4 (HR c μ M) := by
  have hdetK : ∀ m ≤ M, (gram (cK c) (cK μ) m).det ≠ 0 := by
    intro m hm
    rw [gram_map (algebraMap ℂ K4) c μ m, show ((gram c μ m).map cK).det = cK (gram c μ m).det
      from (RingHom.map_det (algebraMap ℂ K4) _).symm]
    exact (_root_.map_ne_zero _).2 (h m hm)
  have := evalAt_Hsph_sum (cK c) (cK μ) ΔK M fun m hm => regAt_Bsph ΔK (hdetK m hm)
  unfold evalAt at this
  rw [this, HR, map_mul, map_sum, algebraMap_C_K4]
  congr 1
  swap
  · simp only [cK, map_inv₀, map_pow]
    congr 2
    exact (map_ofNat (algebraMap ℂ K4) 16).symm
  refine sum_congr rfl fun x hx => ?_
  rw [map_mul, algebraMap_QP, map_sum]
  congr 1
  refine sum_congr rfl fun m hm => ?_
  have hmM : m ≤ M := by
    have := (mem_antidiagonal.1 hx)
    have := mem_range.1 hm
    omega
  rw [map_mul, algebraMap_C_K4, ← evalBsph_K4 (h m hmM), ← ratK4]

/-- (H2): the value of `HR c μ M` at a complex point `v` is `H_M(c,μ,v)`. -/
theorem eval_HR {c μ : ℂ} {M : ℕ} (h : ∀ m ≤ M, (gram c μ m).det ≠ 0) (v : Fin 4 → ℂ) :
    MvPolynomial.eval v (HR c μ M) = evalAt μ (Hsph c v M) := by
  rw [evalAt_Hsph_sum c μ v M fun m hm => regAt_Bsph v (h m hm), HR, map_mul, map_sum,
    MvPolynomial.eval_C]
  refine congrArg (fun t => t * ((16 : ℂ) ^ M)⁻¹) (sum_congr rfl fun x hx => ?_)
  rw [map_mul, eval_QP, map_sum]
  refine congrArg (fun t => MvPolynomial.aeval (vec6At c μ v) (QPhiInv x.1) * t)
    (sum_congr rfl fun m hm => ?_)
  have hmM : m ≤ M := by
    have := (mem_antidiagonal.1 hx)
    have := mem_range.1 hm
    omega
  rw [map_mul, MvPolynomial.eval_C, eval_BR (h m hmM)]
  rfl

end Virasoro.Sphere
