import Virasoro.Sphere.Proofs.Sec3Ward

/-!
# The operators (3.2) over a commutative `ℂ`-algebra

Toward sphere paper Lemma 3.3(i) (sphere/paper.tex l.513–514): the coefficients of the Ward
solution are rational functions of `λ`.  The operators (3.2) are written over a commutative
`ℂ`-algebra `R` (here `ℂ[λ]`), and they commute with base change along `ℂ`-algebra maps
(`ℂ[λ] → ℂ(λ)` and the evaluations `ℂ[λ] → ℂ`).
-/

namespace Virasoro.Sphere

open MvPolynomial

section Ring

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The operator `l_k` of (3.2) on the monomial `u^α`, over a commutative `ℂ`-algebra. -/
noncomputable def ffOpMonoR (μ lam : R) (k : ℤ) (α : ℕ+ →₀ ℕ) : MvPolynomial ℕ+ R :=
  let f : MvPolynomial ℕ+ R := monomial α 1
  let B : ℕ := α.support.sup fun m => (m : ℕ)
  let i : R := algebraMap ℂ R Complex.I
  if k = 0 then
    ∑ n ∈ Finset.Icc 1 B, (n : R) • (X n.toPNat' * pderiv n.toPNat' f) + C (lam ^ 2 + μ ^ 2) * f
  else if 0 < k then
    ∑ n ∈ Finset.Icc 1 B, (n : R) • (X n.toPNat' * pderiv (n + k.toNat).toPNat' f)
      - (1 / 4 : ℂ) • ∑ n ∈ Finset.Icc 1 (k.toNat - 1),
          pderiv n.toPNat' (pderiv (k.toNat - n).toPNat' f)
      + C (μ * (k.toNat : R) + i * lam) * pderiv k.toNat.toPNat' f
  else
    ∑ n ∈ Finset.Icc 1 B, ((n + (-k).toNat : ℕ) : R) •
        (X (n + (-k).toNat).toPNat' * pderiv n.toPNat' f)
      - (∑ n ∈ Finset.Icc 1 ((-k).toNat - 1),
          ((n * ((-k).toNat - n) : ℕ) : R) • (X n.toPNat' * X ((-k).toNat - n).toPNat')) * f
      + C (2 * ((-k).toNat : R) * (μ * ((-k).toNat : R) - i * lam)) * X (-k).toNat.toPNat' * f

/-- The operator `l_k` of (3.2) over a commutative `ℂ`-algebra. -/
noncomputable def ffOpR (μ lam : R) (k : ℤ) : MvPolynomial ℕ+ R →ₗ[R] MvPolynomial ℕ+ R :=
  (basisMonomials ℕ+ R).constr R (ffOpMonoR μ lam k)

/-- `l_{-Y} 1` over a commutative `ℂ`-algebra. -/
noncomputable def fockWordR (μ lam : R) : List ℕ → MvPolynomial ℕ+ R
  | [] => 1
  | y :: w => ffOpR μ lam (-(y : ℤ)) (fockWordR μ lam w)

theorem ffOpR_monomial (μ lam : R) (k : ℤ) (α : ℕ+ →₀ ℕ) (r : R) :
    ffOpR μ lam k (monomial α r) = r • ffOpMonoR μ lam k α := by
  have h := (basisMonomials ℕ+ R).constr_basis R (ffOpMonoR μ lam k) α
  rw [coe_basisMonomials] at h
  rw [show monomial α r = r • monomial α (1 : R) by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul]
  exact congrArg _ h

variable {R' : Type*} [CommRing R'] [Algebra ℂ R'] (φ : R →ₐ[ℂ] R')

theorem map_smulR (r : R) (p : MvPolynomial ℕ+ R) :
    map (φ : R →+* R') (r • p) = φ r • map (φ : R →+* R') p := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  rfl

theorem map_smulC (z : ℂ) (p : MvPolynomial ℕ+ R) :
    map (φ : R →+* R') (z • p) = z • map (φ : R →+* R') p := by
  rw [← algebraMap_smul R z p, ← algebraMap_smul R' z (map (φ : R →+* R') p), map_smulR,
    AlgHom.commutes]

theorem map_ffOpMonoR (μ lam : R) (k : ℤ) (α : ℕ+ →₀ ℕ) :
    map (φ : R →+* R') (ffOpMonoR μ lam k α) = ffOpMonoR (φ μ) (φ lam) k α := by
  have hI : φ (algebraMap ℂ R Complex.I) = algebraMap ℂ R' Complex.I := φ.commutes _
  have hm : map (φ : R →+* R') (monomial α (1 : R)) = monomial α (1 : R') := by
    rw [map_monomial]
    simp
  unfold ffOpMonoR
  split_ifs
  · simp only [map_add, map_sum, map_smulR, map_mul, map_X, map_C, ← pderiv_map, hm,
      RingHom.coe_coe, map_natCast, map_pow]
  · simp only [map_add, map_sub, map_sum, map_smulR, map_smulC, map_mul, map_X, map_C,
      ← pderiv_map, hm, RingHom.coe_coe, map_natCast, hI]
  · simp only [map_add, map_sub, map_sum, map_smulR, map_mul, map_X, map_C,
      ← pderiv_map, hm, RingHom.coe_coe, map_natCast, hI, map_ofNat]

theorem map_ffOpR (μ lam : R) (k : ℤ) (f : MvPolynomial ℕ+ R) :
    map (φ : R →+* R') (ffOpR μ lam k f) = ffOpR (φ μ) (φ lam) k (map (φ : R →+* R') f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial α r =>
    rw [ffOpR_monomial, map_smulR, map_ffOpMonoR, map_monomial, ffOpR_monomial]
    rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]

theorem map_fockWordR (μ lam : R) (w : List ℕ) :
    map (φ : R →+* R') (fockWordR μ lam w) = fockWordR (φ μ) (φ lam) w := by
  induction w with
  | nil => simp [fockWordR]
  | cons y w ih => rw [fockWordR, fockWordR, map_ffOpR, ih]

end Ring

/-- Over a field the operators are those of `Sphere/Fock.lean`. -/
theorem ffOp_eq_ffOpR {K : Type*} [Field K] [Algebra ℂ K] (μ lam : K) (k : ℤ) :
    ffOp μ lam k = ffOpR μ lam k := by
  unfold ffOp ffOpR
  congr 1
  funext α
  unfold ffOpMono ffOpMonoR uVar dVar
  simp only [Derivation.coeFn_coe, one_div]
  split_ifs
  · rfl
  · congr 2
    rw [← algebraMap_smul K (4⁻¹ : ℂ), map_inv₀, map_ofNat]
  · rfl

theorem fockWord_eq_fockWordR {K : Type*} [Field K] [Algebra ℂ K] (μ lam : K) (w : List ℕ) :
    fockWord μ lam w = fockWordR μ lam w := by
  induction w with
  | nil => rfl
  | cons y w ih => rw [fockWord, fockWordR, ih, ffOp_eq_ffOpR]

end Virasoro.Sphere
