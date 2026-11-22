import Virasoro.Proofs.Sec6LimGr
import Virasoro.Proofs.Naturality
import Virasoro.Proofs.Sec6H13IntA

/-!
# Proposition 6.7, the chain limit (b): the graded objects (paper.tex l.1141–1146)

`b = b⋆ + S X` with inverse `∑_i (−S)^i/b⋆^{i+1} X^i`, the central charge `c(b)`, the weights
`h_a(b)`, `Δ = λ + W X`, `d = Y X`; all entries of `G_M(c(b),Δ)` and `ρ_M(c(b),Δ,d)`, their
determinants and adjugates are graded.
-/

namespace Virasoro.ChainLim

open PowerSeries

section Objects

variable (bs : ℂ)

/-- `b = b⋆ + S X`. -/
noncomputable def Bb : PS := PowerSeries.C (MvPolynomial.C bs) +
  PowerSeries.C (MvPolynomial.X 0) * PowerSeries.X

/-- `b⁻¹ = ∑_i (−S)^i/b⋆^{i+1} X^i`. -/
noncomputable def Binv : PS :=
  PowerSeries.mk fun i => MvPolynomial.C ((-1) ^ i / bs ^ (i + 1)) * (MvPolynomial.X 0) ^ i

theorem Bb_mul_Binv (hbs : bs ≠ 0) : Bb bs * Binv bs = 1 := by
  refine PowerSeries.ext fun n => ?_
  rw [Bb, add_mul, map_add, mul_assoc, coeff_C_mul, coeff_C_mul, coeff_one]
  rcases n with _ | n
  · rw [coeff_zero_X_mul, mul_zero, add_zero, if_pos rfl]
    have e : coeff 0 (Binv bs) = MvPolynomial.C (1 / bs) := by simp [Binv]
    rw [e, ← map_mul, mul_one_div_cancel hbs, MvPolynomial.C_1]
  · rw [coeff_succ_X_mul, if_neg (Nat.succ_ne_zero n)]
    simp only [Binv, coeff_mk]
    have h0 : bs * ((-1) ^ (n + 1) / bs ^ (n + 1 + 1)) + (-1) ^ n / bs ^ (n + 1) = 0 := by
      field_simp
      ring
    calc _ = MvPolynomial.C (bs * ((-1) ^ (n + 1) / bs ^ (n + 1 + 1)) +
          (-1) ^ n / bs ^ (n + 1)) * (MvPolynomial.X 0 : R3) ^ (n + 1) := by
          rw [map_add, map_mul]
          ring
      _ = 0 := by rw [h0, map_zero, zero_mul]

theorem isGr_Bb : IsGr (Bb bs) := (isGr_Cc bs).add (isGr_var 0)

theorem isGr_Binv : IsGr (Binv bs) := by
  intro i
  rw [Binv, coeff_mk]
  have := (MvPolynomial.isHomogeneous_X_pow (R := ℂ) (0 : Fin 3) i).C_mul ((-1) ^ i / bs ^ (i + 1))
  simpa using this

/-- `Δ = λ + W X`. -/
noncomputable def DR (lam : ℂ) : PS := PowerSeries.C (MvPolynomial.C lam) +
  PowerSeries.C (MvPolynomial.X 1) * PowerSeries.X

/-- `d = Y X`. -/
noncomputable def dR : PS := PowerSeries.C (MvPolynomial.X 2) * PowerSeries.X

/-- `c(b) = 1 + 6(b + b⁻¹)²`. -/
noncomputable def cR : PS := 1 + 6 * (Bb bs + Binv bs) ^ 2

/-- `h_a(b) = ((b + b⁻¹)² − (a₁ b + a₂ b⁻¹)²)/4`. -/
noncomputable def hR (a : Label) : PS :=
  algebraMap ℚ PS (1 / 4) * ((Bb bs + Binv bs) ^ 2 -
    ((a.1 : PS) * Bb bs + (a.2 : PS) * Binv bs) ^ 2)

end Objects

theorem Bb_mem (bs : ℂ) : Bb bs ∈ grSub := isGr_Bb bs
theorem Binv_mem (bs : ℂ) : Binv bs ∈ grSub := isGr_Binv bs
theorem DR_mem (lam : ℂ) : DR lam ∈ grSub := (isGr_Cc lam).add (isGr_var 1)
theorem dR_mem : dR ∈ grSub := isGr_var 2

theorem cR_mem (bs : ℂ) : cR bs ∈ grSub := by
  unfold cR
  have h6 : (6 : PS) ∈ grSub := by
    have := grSub.algebraMap_mem (6 : ℚ)
    simpa using this
  exact grSub.add_mem grSub.one_mem
    (grSub.mul_mem h6 (grSub.pow_mem (grSub.add_mem (Bb_mem bs) (Binv_mem bs)) 2))

theorem natCast_mem (n : ℕ) : (n : PS) ∈ grSub := by
  have := grSub.algebraMap_mem (n : ℚ)
  simpa using this

theorem hR_mem (bs : ℂ) (a : Label) : hR bs a ∈ grSub := by
  unfold hR
  refine grSub.mul_mem (grSub.algebraMap_mem _) (grSub.sub_mem ?_ ?_)
  · exact grSub.pow_mem (grSub.add_mem (Bb_mem bs) (Binv_mem bs)) 2
  · exact grSub.pow_mem (grSub.add_mem (grSub.mul_mem (natCast_mem _) (Bb_mem bs))
      (grSub.mul_mem (natCast_mem _) (Binv_mem bs))) 2

/-- Every polynomial over `ℚ` in graded elements is graded. -/
theorem aeval_mem (A : Subalgebra ℚ PS) {n : ℕ} (v : Fin n → PS) (hv : ∀ i, v i ∈ A)
    (P : MvPolynomial (Fin n) ℚ) : MvPolynomial.aeval v P ∈ A := by
  induction P using MvPolynomial.induction_on with
  | C q =>
    rw [MvPolynomial.aeval_C]
    exact A.algebraMap_mem q
  | add P Q hP hQ =>
    rw [map_add]
    exact A.add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul, MvPolynomial.aeval_X]
    exact A.mul_mem hP (hv i)

theorem gram_mem (A : Subalgebra ℚ PS) {c h : PS} (hc : c ∈ A) (hh : h ∈ A) (M : ℕ) (i j : Nat.Partition M) :
    gram c h M i j ∈ A := by
  let v : Fin 2 → PS := ![c, h]
  have hv : ∀ k, v k ∈ A := by
    intro k
    fin_cases k
    · exact hc
    · exact hh
  have e := gram_map (MvPolynomial.aeval v).toRingHom
    (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℚ) (MvPolynomial.X 1) M
  have e0 : (MvPolynomial.aeval v).toRingHom
      (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℚ) = c := by simp [v]
  have e1 : (MvPolynomial.aeval v).toRingHom
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℚ) = h := by simp [v]
  rw [e0, e1] at e
  rw [e, Matrix.map_apply]
  exact aeval_mem A v hv _

theorem torus_mem (A : Subalgebra ℚ PS) {c h d : PS} (hc : c ∈ A) (hh : h ∈ A) (hd : d ∈ A) (M : ℕ)
    (i j : Nat.Partition M) : torus c h d M i j ∈ A := by
  let v : Fin 3 → PS := ![c, h, d]
  have hv : ∀ k, v k ∈ A := by
    intro k
    fin_cases k
    · exact hc
    · exact hh
    · exact hd
  have e := torus_map (MvPolynomial.aeval v).toRingHom
    (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℚ) (MvPolynomial.X 1) (MvPolynomial.X 2) M
  have e0 : (MvPolynomial.aeval v).toRingHom
      (MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℚ) = c := by simp [v]
  have e1 : (MvPolynomial.aeval v).toRingHom
      (MvPolynomial.X (1 : Fin 3) : MvPolynomial (Fin 3) ℚ) = h := by simp [v]
  have e2 : (MvPolynomial.aeval v).toRingHom
      (MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) ℚ) = d := by simp [v]
  rw [e0, e1, e2] at e
  rw [e, Matrix.map_apply]
  exact aeval_mem A v hv _

/-- `Fn M = ∑ adj(G_M) ρ_M` and `Dn M = det G_M` over `PS` are graded. -/
theorem fnum_mem (A : Subalgebra ℚ PS) {c h d : PS} (hc : c ∈ A) (hh : h ∈ A) (hd : d ∈ A) (M : ℕ) :
    (∑ i, ∑ j, (gram c h M).adjugate i j * torus c h d M i j) ∈ A := by
  refine A.toSubring.sum_mem fun i _ => A.toSubring.sum_mem fun j _ => ?_
  exact A.mul_mem (adjugate_mem A.toSubring _ (gram_mem A hc hh M) i j)
    (torus_mem A hc hh hd M i j)

theorem det_mem' (A : Subalgebra ℚ PS) {c h : PS} (hc : c ∈ A) (hh : h ∈ A) (M : ℕ) :
    (gram c h M).det ∈ A :=
  det_mem A.toSubring _ (gram_mem A hc hh M)

end Virasoro.ChainLim
