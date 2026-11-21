import Virasoro.Sphere.Proofs.Sec3BergmanOde
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Sphere paper Lemma 3.5: the series `W(x₁,x₂)` and Steps 2–3 (`sphere/paper.tex` l.837–966)

Objects of the proof: the infinite matrices `B`, `B^{(z)}`, `M₁`, `M₂` over `ℚ[[z]]`, the Neumann
series `K₁₂`, `K₂₁`, the blocks `A₊₊`, `A₋₋`, `A₋₊`, `A₊₋`, and for each order `z^j` the complex
function `[z^j] W(x₁,x₂)` on `0 < |x₁|, |x₂| < 1`.

The trace formula `Stmt_sub_bergman_trace` is reduced to three sub-statements, one for each part
of the paper's argument:
* `Stmt_sub_bergman_liouville` (l.867–929, Steps 1–2);
* `Stmt_sub_bergman_zero_mode` (l.931–941, Step 3, first half);
* `Stmt_sub_bergman_residue` (l.943–966, Step 3, second half).

Consumer: `Stmt_sub_bergman_trace`.
-/

namespace Virasoro.Sphere

open PowerSeries Finset

/-- Infinite matrices over `ℚ[[z]]`, indexed by `m, n ≥ 1`; row `0` and column `0` are not
used. -/
abbrev IMat : Type := ℕ → ℕ → PowerSeries ℚ

/-- The product `(AB)_{m,n} = ∑_k A_{m,k} B_{k,n}`, for factors such that the coefficient of
`z^j` of `A_{m,k} B_{k,n}` vanishes for `k > m + n + j`.  This holds for every product below:
in each of them either `A_{m,k} B_{k,n} = O(z^k)`, or this holds apart from the terms `k = m`
or `k = n` of an identity matrix. -/
noncomputable def imul (A B : IMat) : IMat := fun m n =>
  PowerSeries.mk fun j => ∑ k ∈ range (m + n + j + 1), coeff j (A m k * B k n)

/-- The identity matrix. -/
noncomputable def ione : IMat := fun m n => if m = n then 1 else 0

/-- Powers of an infinite matrix. -/
noncomputable def ipow (A : IMat) : ℕ → IMat
  | 0 => ione
  | r + 1 => imul (ipow A r) A

/-- The Neumann series `∑_{r≥0} A^r` of a matrix with `A^r = O(z^r)`. -/
noncomputable def ineumann (A : IMat) : IMat := fun m n =>
  PowerSeries.mk fun j => ∑ r ∈ range (j + 1), coeff j (ipow A r m n)

/-- `B_{m,n}` (sphere/paper.tex l.837). -/
noncomputable def Binf : IMat := fun m n => C (Bcoef m n)

/-- `B^{(z)}_{m,n} = z^{m+n} B_{m,n}` (l.837). -/
noncomputable def Bzinf : IMat := fun m n => C (Bcoef m n) * X ^ (m + n)

/-- `M₁ = D⁻¹ B^{(z)}` (l.838). -/
noncomputable def M1inf : IMat := fun m n => C (Bcoef m n / (m : ℚ)) * X ^ (m + n)

/-- `M₂ = D⁻¹ B` (l.838). -/
noncomputable def M2inf : IMat := fun m n => C (Bcoef m n / (m : ℚ))

/-- `K₁₂ = ∑_{r≥0} (M₁M₂)^r` (l.839). -/
noncomputable def K12 : IMat := ineumann (imul M1inf M2inf)

/-- `K₂₁ = ∑_{r≥0} (M₂M₁)^r` (l.839). -/
noncomputable def K21 : IMat := ineumann (imul M2inf M1inf)

/-- `A₊₊ = -B^{(z)} K₂₁` (l.876). -/
noncomputable def App : IMat := fun m n => -imul Bzinf K21 m n

/-- `A₋₋ = -B K₁₂` (l.876). -/
noncomputable def Amm : IMat := fun m n => -imul Binf K12 m n

/-- `A₋₊ = B K₁₂ M₁` (l.877). -/
noncomputable def Amp : IMat := imul (imul Binf K12) M1inf

/-- `A₊₋ = B^{(z)} K₂₁ M₂` (l.877). -/
noncomputable def Apm : IMat := imul (imul Bzinf K21) M2inf

/-- The `(m,n)` term, `m, n ≥ 1` (here `m + 1`, `n + 1`), of the coefficient of `z^j` of
`W_no(x₁,x₂)` (l.872–875). -/
noncomputable def WnoTerm (j : ℕ) (x1 x2 : ℂ) (m n : ℕ) : ℂ :=
  ((coeff j (App (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ (-((m : ℤ) + 2)) * x2 ^ (-((n : ℤ) + 2)) +
    ((coeff j (Amm (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ m * x2 ^ n +
    ((coeff j (Amp (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ m * x2 ^ (-((n : ℤ) + 2)) +
    ((coeff j (Apm (m + 1) (n + 1)) : ℚ) : ℂ) * x1 ^ (-((m : ℤ) + 2)) * x2 ^ n

/-- `W(x₁,x₂) = (x₁-x₂)⁻² + W_no(x₁,x₂)` as a power series in `z` (l.870–875). -/
noncomputable def Wser (x1 x2 : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun j =>
    (if j = 0 then ((x1 - x2) ^ 2)⁻¹ else 0) + ∑' mn : ℕ × ℕ, WnoTerm j x1 x2 mn.1 mn.2

/-- `S(x₁,x₂) = ½[x₁x₂(x₁+x₂) - 2(1+z)x₁x₂ + z(x₁+x₂)]` (l.921). -/
noncomputable def Sser (x1 x2 : ℂ) : PowerSeries ℂ :=
  C (x1 * x2 * (x1 + x2) / 2 - x1 * x2) + C ((x1 + x2) / 2 - x1 * x2) * X

/-- `(1 - z/x)^{-1/2} = ∑_j h_j z^j x^{-j}`. -/
noncomputable def invSqrtZ (x : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun j => (halfBinom j : ℂ) * x ^ (-(j : ℤ))

/-- `1/(Y(x₁)Y(x₂))` coefficientwise in `z`, `Y(x) = √(x(x-z)(x-1))` (l.914):
`Y(x) = x √(x-1) √(1-z/x)` and `√(x₁-1)√(x₂-1) = -√(1-x₁)√(1-x₂)` for either choice of the
branch `√(x-1) = ±i√(1-x)` on the unit disc. -/
noncomputable def YYinv (x1 x2 : ℂ) : PowerSeries ℂ :=
  C (-(x1 * x2 * (1 - x1) ^ (1 / 2 : ℂ) * (1 - x2) ^ (1 / 2 : ℂ))⁻¹) *
    invSqrtZ x1 * invSqrtZ x2

/-- The conclusion of Step 2 for a series `C(z)` (l.925–929): at every order in `z` the series
of `W_no` converges on `0 < |x₁|, |x₂| < 1` and, for `x₁ ≠ x₂`,
`W(x₁,x₂) = S(x₁,x₂)/(Y(x₁)Y(x₂)(x₁-x₂)²) + 2C(z)/(Y(x₁)Y(x₂))`. -/
def IsWFormula (Cz : PowerSeries ℂ) : Prop :=
  ∀ x1 x2 : ℂ, 0 < ‖x1‖ → ‖x1‖ < 1 → 0 < ‖x2‖ → ‖x2‖ < 1 → x1 ≠ x2 →
    (∀ j : ℕ, Summable fun mn : ℕ × ℕ => WnoTerm j x1 x2 mn.1 mn.2) ∧
    Wser x1 x2 = YYinv x1 x2 * (C (((x1 - x2) ^ 2)⁻¹) * Sser x1 x2 + 2 * Cz)

/-- Sub-statement of Lemma 3.5, Steps 1–2 (sphere/paper.tex l.867–929): coefficientwise
meromorphic continuation and Liouville's theorem give the formula for `W` with some `C(z)`. -/
def Stmt_sub_bergman_liouville : Prop := ∃ Cz : PowerSeries ℂ, IsWFormula Cz

/-- Sub-statement of Lemma 3.5, Step 3, zero-mode condition (sphere/paper.tex l.931–941):
`2C(z) = -z/2 + z(1-z)F₀'(z)/F₀(z)`, here multiplied by `2`. -/
def Stmt_sub_bergman_zero_mode : Prop :=
  ∀ Cz : PowerSeries ℂ, IsWFormula Cz →
    4 * Cz = (2 * (X * (1 - X) * derivative ℚ hyp2F1 * hyp2F1⁻¹) - X).map (algebraMap ℚ ℂ)

/-- Sub-statement of Lemma 3.5, Step 3, trace and residues (sphere/paper.tex l.943–966):
`Tr(D M² (I - M²)⁻¹) = Tr(B K₁₂ M₁) = z/(8(z-1)) + 2C(z)/(2(z-1))`, here multiplied by
`8(z-1)`. -/
def Stmt_sub_bergman_residue : Prop :=
  ∀ Cz : PowerSeries ℂ, IsWFormula Cz →
    8 * traceDM.map (algebraMap ℚ ℂ) * (X - 1) = X + 8 * Cz

/-- The trace formula from the three steps of the paper's argument. -/
theorem bergman_trace_of_steps (hL : Stmt_sub_bergman_liouville)
    (hZ : Stmt_sub_bergman_zero_mode) (hR : Stmt_sub_bergman_residue) :
    Stmt_sub_bergman_trace := by
  obtain ⟨Cz, hC⟩ := hL
  have h1 := hR Cz hC
  have h2 := hZ Cz hC
  set F := hyp2F1
  set dF := derivative ℚ F
  set G := 2 * (X * (1 - X) * dF * F⁻¹) - X with hG
  have e : 8 * traceDM * (X - 1) = X + 2 * G := by
    have hinj : Function.Injective (PowerSeries.map (algebraMap ℚ ℂ)) := by
      intro f g hfg
      ext n
      have := congrArg (coeff n) hfg
      rw [coeff_map, coeff_map] at this
      exact (algebraMap ℚ ℂ).injective this
    apply hinj
    rw [map_add, map_mul (PowerSeries.map (algebraMap ℚ ℂ)) 2 G, ← h2]
    simp only [map_mul, map_sub, map_ofNat, map_one, PowerSeries.map_X]
    linear_combination h1
  have i1 : C (8 : ℚ) * (1 - X) * (C (8 : ℚ) * (1 - X))⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by
      rw [map_mul, constantCoeff_C, constantCoeff_one_sub_X]; norm_num)
  have h8 : (C (8 : ℚ) : PowerSeries ℚ) = 8 := map_ofNat _ 8
  have hh : (2 : PowerSeries ℚ) * C (1 / 2 : ℚ) = 1 := by
    rw [← map_ofNat (C (R := ℚ)) 2, ← map_mul]
    norm_num
  rw [h8] at i1
  have hne : (8 : PowerSeries ℚ) * (X - 1) ≠ 0 := by
    intro h
    have := congrArg constantCoeff h
    rw [map_mul, map_sub, constantCoeff_X, map_one, map_ofNat, map_zero] at this
    norm_num at this
  show traceDM = X * (C (8 : ℚ) * (1 - X))⁻¹ - C (1 / 2 : ℚ) * (X * dF * F⁻¹)
  rw [h8]
  refine mul_left_cancel₀ hne ?_
  linear_combination e + X * i1 - (4 * (X * (1 - X) * dF * F⁻¹)) * hh

end Virasoro.Sphere
