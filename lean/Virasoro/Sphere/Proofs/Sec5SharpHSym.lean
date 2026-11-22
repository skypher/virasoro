import Virasoro.Sphere.Proofs.Sec5SharpHHerm
import Virasoro.Sphere.Proofs.Sec3FpowExp
import Virasoro.Sphere.Proofs.FpowBinom

/-!
# Theorem 5.5, step (3): the leading coefficient in `v` (sphere/paper.tex l.1744–1757)

For a `q`-series `F` whose coefficients are polynomials in `w`, `Fil F` says that `[q^n]F` has
degree at most `n` in `w` ("every monomial `w^a q^b` has `a ≤ b`", l.1748–1750); the symbol
`sym F = ∑_n [w^n][q^n]F tⁿ` keeps the monomials with `a = b`.  `Fil` is closed under products
and under `exp`, and `sym` is multiplicative, so for `S = s₀ + w s₁ + w² s₂` with
`s₁ = O(q)`, `s₂ = O(q²)`, `[w^M][q^M] exp(S) = [t^M] exp(c₁ t + c₂ t²)`,
`c₁ = [q]s₁`, `c₂ = [q²]s₂` (l.1752–1757).  Then `M! [t^M] exp(-bt - gt²) = k_M`.
-/

namespace Virasoro.Sphere

open Polynomial

/-! ### The filtration and the symbol -/

/-- `deg_w [q^n] F ≤ n` for every `n`. -/
def Fil (F : PowerSeries ℂ[X]) : Prop := ∀ n, (PowerSeries.coeff n F).natDegree ≤ n

/-- The symbol `∑_n [w^n][q^n]F tⁿ`. -/
noncomputable def sym (F : PowerSeries ℂ[X]) : PowerSeries ℂ :=
  PowerSeries.mk fun n => (PowerSeries.coeff n F).coeff n

theorem Fil.mul {F G : PowerSeries ℂ[X]} (hF : Fil F) (hG : Fil G) :
    Fil (F * G) ∧ sym (F * G) = sym F * sym G := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_mul]
    refine natDegree_sum_le_of_forall_le _ _ fun x hx => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have h1 := hF x.1
    have h2 := hG x.2
    exact natDegree_mul_le.trans (by omega)
  · ext n
    rw [sym, PowerSeries.coeff_mk, PowerSeries.coeff_mul, PowerSeries.coeff_mul, finset_sum_coeff]
    refine Finset.sum_congr rfl fun x hx => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [sym, sym, PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← h,
      coeff_mul_add_eq_of_natDegree_le (hF x.1) (hG x.2)]

theorem Fil.one : Fil (1 : PowerSeries ℂ[X]) ∧ sym 1 = 1 := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_one]
    split_ifs <;> simp
  · ext n
    rw [sym, PowerSeries.coeff_mk, PowerSeries.coeff_one, PowerSeries.coeff_one]
    split_ifs with h
    · rw [h, coeff_one_zero]
    · rw [coeff_zero]

theorem Fil.pow {F : PowerSeries ℂ[X]} (hF : Fil F) (k : ℕ) :
    Fil (F ^ k) ∧ sym (F ^ k) = sym F ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact Fil.one
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih.1.mul hF
    rw [pow_succ, pow_succ, ← ih.2]
    exact ⟨h1, h2⟩

/-- `∑_k b_k S^k`, truncated coefficientwise as in `compS`, over `ℂ[w]`. -/
noncomputable def compR (b : ℕ → ℂ) (S : PowerSeries ℂ[X]) : PowerSeries ℂ[X] :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1), C (b k) * PowerSeries.coeff n (S ^ k)

theorem Fil.compR {S : PowerSeries ℂ[X]} (hS : Fil S) (b : ℕ → ℂ) :
    Fil (compR b S) ∧ sym (compR b S) = compS b (sym S) := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [Sphere.compR, PowerSeries.coeff_mk]
    exact natDegree_sum_le_of_forall_le _ _ fun k _ =>
      (natDegree_C_mul_le _ _).trans ((hS.pow k).1 n)
  · ext n
    rw [sym, PowerSeries.coeff_mk, Sphere.compR, PowerSeries.coeff_mk, compS,
      PowerSeries.coeff_mk, finset_sum_coeff]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_C_mul, ← (hS.pow k).2, sym, PowerSeries.coeff_mk]

/-- Evaluation at `w = w₀` of `compR`. -/
theorem eval_coeff_compR (b : ℕ → ℂ) (S : PowerSeries ℂ[X]) (n : ℕ) (w₀ : ℂ) :
    (PowerSeries.coeff n (compR b S)).eval w₀ =
      PowerSeries.coeff n (compS b (PowerSeries.map (evalRingHom w₀) S)) := by
  rw [compR, PowerSeries.coeff_mk, compS, PowerSeries.coeff_mk, eval_finset_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, ← map_pow, PowerSeries.coeff_map, coe_evalRingHom]

/-! ### The exponent `s₀ + w s₁ + w² s₂` -/

/-- `s₀ + w s₁ + w² s₂` as a `q`-series over `ℂ[w]`. -/
noncomputable def quadS (s₀ s₁ s₂ : PowerSeries ℂ) : PowerSeries ℂ[X] :=
  PowerSeries.map C s₀ + PowerSeries.C (X : ℂ[X]) * PowerSeries.map C s₁ +
    PowerSeries.C (X ^ 2 : ℂ[X]) * PowerSeries.map C s₂

theorem coeff_quadS (s₀ s₁ s₂ : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (quadS s₀ s₁ s₂) =
      C (PowerSeries.coeff n s₀) + X * C (PowerSeries.coeff n s₁) +
        X ^ 2 * C (PowerSeries.coeff n s₂) := by
  simp only [quadS, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_map]

theorem map_quadS (s₀ s₁ s₂ : PowerSeries ℂ) (w₀ : ℂ) :
    PowerSeries.map (evalRingHom w₀) (quadS s₀ s₁ s₂) = s₀ + w₀ • s₁ + w₀ ^ 2 • s₂ := by
  ext n
  rw [PowerSeries.coeff_map, coeff_quadS]
  simp [PowerSeries.coeff_smul]
  ring

theorem Fil_quadS {s₀ s₁ s₂ : PowerSeries ℂ} (h10 : PowerSeries.coeff 0 s₁ = 0)
    (h20 : PowerSeries.coeff 0 s₂ = 0) (h21 : PowerSeries.coeff 1 s₂ = 0) :
    Fil (quadS s₀ s₁ s₂) ∧
      sym (quadS s₀ s₁ s₂) = PowerSeries.C (PowerSeries.coeff 0 s₀) +
        PowerSeries.C (PowerSeries.coeff 1 s₁) * PowerSeries.X +
        PowerSeries.C (PowerSeries.coeff 2 s₂) * PowerSeries.X ^ 2 := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [coeff_quadS]
    rcases n with _ | _ | n
    · simp [h10, h20]
    · rw [h21, map_zero, mul_zero, add_zero]
      exact (natDegree_add_le _ _).trans (max_le (by simp)
        ((natDegree_mul_le).trans (by simp)))
    · refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)
      · simp
      · exact (natDegree_mul_le).trans (by simp)
      · exact (natDegree_mul_le).trans (by simp)
  · ext n
    rw [sym, PowerSeries.coeff_mk, coeff_quadS]
    rcases n with _ | _ | _ | n
    · simp [h10, h20]
    · simp [h21, coeff_X, PowerSeries.coeff_X_pow]
    · simp [coeff_X, PowerSeries.coeff_X_pow, coeff_X_pow]
    · simp [coeff_X, PowerSeries.coeff_X_pow, coeff_X_pow, PowerSeries.coeff_X]

/-- The leading coefficient: `[w^M][q^M] ∑_k b_k S^k = [t^M] ∑_k b_k (sym S)^k`. -/
theorem coeff_coeff_compR_quadS {s₀ s₁ s₂ : PowerSeries ℂ} (h10 : PowerSeries.coeff 0 s₁ = 0)
    (h20 : PowerSeries.coeff 0 s₂ = 0) (h21 : PowerSeries.coeff 1 s₂ = 0) (b : ℕ → ℂ) (M : ℕ) :
    (PowerSeries.coeff M (compR b (quadS s₀ s₁ s₂))).coeff M =
      PowerSeries.coeff M (compS b (PowerSeries.C (PowerSeries.coeff 0 s₀) +
        PowerSeries.C (PowerSeries.coeff 1 s₁) * PowerSeries.X +
        PowerSeries.C (PowerSeries.coeff 2 s₂) * PowerSeries.X ^ 2)) := by
  obtain ⟨hF, hsym⟩ := Fil_quadS (s₀ := s₀) h10 h20 h21
  have := ((hF.compR b).2)
  rw [hsym] at this
  rw [← this, sym, PowerSeries.coeff_mk]

/-! ### `M! [t^M] exp(c₁ t + c₂ t²)` -/

theorem derivative_quad (c₁ c₂ : ℂ) :
    PowerSeries.derivative ℂ (PowerSeries.C c₁ * PowerSeries.X + PowerSeries.C c₂ * PowerSeries.X ^ 2) =
      PowerSeries.C c₁ + PowerSeries.C (2 * c₂) * PowerSeries.X := by
  ext n
  rw [PowerSeries.coeff_derivative]
  rcases n with _ | _ | n
  · simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_C]
  · simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_C]
    ring
  · simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_C]

/-- With `c₁ = -b`, `c₂ = -g`: `n! [t^n] exp(c₁ t + c₂ t²) = k_n`. -/
theorem coeff_exp_quad (b g : ℚ) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp ℂ).subst
        (PowerSeries.C (-(b : ℂ)) * PowerSeries.X + PowerSeries.C (-(g : ℂ)) * PowerSeries.X ^ 2)) *
      (n.factorial : ℂ) = (kseq b g n : ℂ) := by
  set u : PowerSeries ℂ :=
    PowerSeries.C (-(b : ℂ)) * PowerSeries.X + PowerSeries.C (-(g : ℂ)) * PowerSeries.X ^ 2 with hu
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    rw [hu]
    simp
  set G := (PowerSeries.exp ℂ).subst u with hG
  have hd := deriv_exp_subst u hu0
  rw [← hG, hu, derivative_quad] at hd
  -- the recurrence `(n+1) G_{n+1} = c₁ G_n + 2 c₂ G_{n-1}`
  have hrec : ∀ m : ℕ, PowerSeries.coeff (m + 1) G * ((m : ℂ) + 1) =
      -(b : ℂ) * PowerSeries.coeff m G +
        (if m = 0 then 0 else 2 * -(g : ℂ) * PowerSeries.coeff (m - 1) G) := by
    intro m
    have := congrArg (PowerSeries.coeff m) hd
    rw [PowerSeries.coeff_derivative] at this
    rw [this, mul_add, map_add, PowerSeries.coeff_mul_C,
      show G * (PowerSeries.C (2 * -(g : ℂ)) * PowerSeries.X) =
        G * PowerSeries.X * PowerSeries.C (2 * -(g : ℂ)) by ring, PowerSeries.coeff_mul_C]
    rcases m with _ | m
    · simp
      ring
    · rw [PowerSeries.coeff_succ_mul_X]
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      ring
  have hG0 : PowerSeries.coeff 0 G = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hG]
    exact constantCoeff_exp_subst u hu0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · rw [hG0]; simp [kseq]
    · have := hrec 0
      simp only [Nat.cast_zero, zero_add, mul_one, if_pos rfl, add_zero, hG0] at this
      rw [this]
      simp [kseq]
    · have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      have := hrec (n + 1)
      rw [if_neg (by omega), show n + 1 - 1 = n from rfl] at this
      rw [kseq.eq_3]
      push_cast
      rw [Nat.factorial_succ, Nat.cast_mul, ← h1, ← h0, Nat.factorial_succ, Nat.cast_mul]
      push_cast at this ⊢
      linear_combination ((n : ℂ) + 1) * (n.factorial : ℂ) * this

end Virasoro.Sphere
