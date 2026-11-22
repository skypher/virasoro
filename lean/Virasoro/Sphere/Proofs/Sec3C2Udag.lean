import Virasoro.Sphere.Proofs.Sec3C2Fam
import Virasoro.Sphere.Proofs.Sec3C2Wick

/-!
# Lemma 3.7, Step 3: the adjoint family `U(W)^†` (sphere paper)

sphere/paper.tex l.1102–1105, 1111–1114.  `U(W)` is the family `β ↦ U_β` of its coefficients
of `W^β`; `U_β` lowers the level by `|β|`.  `U(W)^†` is the family `β ↦ U_β^†` of the adjoints
for the form (3.1).  Taking the adjoint of `D_k U(W) = -l_k^{(2)} U(W)` gives
`D_k(U(W)^†) = -U(W)^† l_{-k}^{(2)}` with `U(0)^† = id`.
-/

namespace Virasoro.Sphere

open MvPolynomial Finset TensorProduct

/-! ### The form (3.1): symmetry and nondegeneracy -/

theorem fockForm_conj (f g : Fock) : fockForm g f = (starRingEnd ℂ) (fockForm f g) := by
  classical
  rw [fockForm_eq g f (f.support ∪ g.support) Finset.subset_union_left,
    fockForm_eq f g (f.support ∪ g.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_mul, conj_fockNorm, Complex.conj_conj]
  ring

theorem fockForm_monomial_right (x : Fock) (α : ℕ+ →₀ ℕ) :
    fockForm x (monomial α 1) = (starRingEnd ℂ) (coeff α x) * fockNorm α := by
  rw [fockForm_conj, fockForm_monomial_left, map_mul, conj_fockNorm]

theorem fockForm_neg_left (x b : Fock) : fockForm (-x) b = -fockForm x b := by
  have h := fockForm_add_left (-x) x b
  rw [neg_add_cancel, fockForm_zero_left] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem fockForm_ext_left {x y : Fock} (h : ∀ b, fockForm x b = fockForm y b) : x = y := by
  ext α
  have h1 := h (monomial α 1)
  rw [fockForm_monomial_right, fockForm_monomial_right] at h1
  have h2 := mul_right_cancel₀ (fockNorm_ne_zero α) h1
  exact (starRingEnd ℂ).injective h2

theorem op_ext_form {S T : Fock →ₗ[ℂ] Fock} (h : ∀ a b, fockForm (S a) b = fockForm (T a) b) :
    S = T :=
  LinearMap.ext fun a => fockForm_ext_left (h a)

/-! ### The coefficients of `U(W)` -/

/-- The coefficient of `W^β`: `P(W,u) ↦ [W^β] P`. -/
noncomputable def cfW (β : ℕ+ →₀ ℕ) : HH →ₗ[ℂ] Fock :=
  (TensorProduct.lid ℂ Fock).toLinearMap ∘ₗ
    TensorProduct.map (MvPolynomial.lcoeff ℂ β) LinearMap.id

theorem cfW_tmul (β : ℕ+ →₀ ℕ) (a b : Fock) : cfW β (a ⊗ₜ[ℂ] b) = coeff β a • b := by
  simp only [cfW, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, lcoeff_apply]

theorem coeff_cfW (β γ : ℕ+ →₀ ℕ) (y : HH) : coeff γ (cfW β y) = hhBasis.repr y (β, γ) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [map_add, coeff_add, hy, hz, map_add, Finsupp.add_apply]
  | tmul a b => rw [hhBasis_repr_tmul, cfW_tmul, coeff_smul, smul_eq_mul]

theorem cfW_zero (y : HH) : cfW 0 y = evAt 0 y := by
  ext γ
  rw [coeff_cfW, coeff_evAt_zero]

theorem DkF_add' {E : Type*} [AddCommMonoid E] (k : ℕ) (Φ Φ' : (ℕ+ →₀ ℕ) → E) (β : ℕ+ →₀ ℕ) :
    DkF k (fun β => Φ β + Φ' β) β = DkF k Φ β + DkF k Φ' β := by
  simp only [DkF, pdN, smul_add, Finset.sum_add_distrib]
  abel

theorem DkF_zero' {E : Type*} [AddCommMonoid E] (k : ℕ) (β : ℕ+ →₀ ℕ) :
    DkF k (fun _ => (0 : E)) β = 0 := by
  simp [DkF, pdN]

theorem cfW_Dop (k : ℕ) (β : ℕ+ →₀ ℕ) (y : HH) :
    cfW β (TensorProduct.map (Dop k) LinearMap.id y) = DkF k (fun β' => cfW β' y) β := by
  induction y using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    exact (DkF_zero' k β).symm
  | add y z hy hz =>
    simp only [map_add]
    rw [hy, hz, DkF_add']
  | tmul a b =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, cfW_tmul, coeff_Dop_eq]
    have h := DkF_map (LinearMap.toSpanSingleton ℂ Fock b).toAddMonoidHom k
      (fun β' => coeff β' a) β
    simp only [LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply] at h
    rw [h]
    simp only [cfW_tmul]

theorem cfW_map_right (L : Fock →ₗ[ℂ] Fock) (β : ℕ+ →₀ ℕ) (y : HH) :
    cfW β (TensorProduct.map LinearMap.id L y) = L (cfW β y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul a b => rw [TensorProduct.map_tmul, LinearMap.id_apply, cfW_tmul, cfW_tmul, map_smul]

/-- `U_β`, the coefficient of `W^β` in `U(W)`. -/
noncomputable def Ucf (U : Fock →ₗ[ℂ] HH) (β : ℕ+ →₀ ℕ) : Fock →ₗ[ℂ] Fock := cfW β ∘ₗ U

theorem Ucf_apply (U : Fock →ₗ[ℂ] HH) (β : ℕ+ →₀ ℕ) (w : Fock) : Ucf U β w = cfW β (U w) := rfl

section Diffeo

variable {U : Fock →ₗ[ℂ] HH} (hU : IsDiffeoU U)

include hU

/-- `D_k U(W) = -l_k^{(2)} U(W)` on coefficients. -/
theorem Ucf_ode (k : ℕ) (hk : 1 ≤ k) (β : ℕ+ →₀ ℕ) (w : Fock) :
    DkF k (fun β' => Ucf U β' w) β = -ffOp (0 : ℂ) 0 (k : ℤ) (Ucf U β w) := by
  have h := congrArg (cfW β) (hU.1 k hk w)
  rw [map_add, cfW_Dop, cfW_map_right, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem Ucf_zero (w : Fock) : Ucf U 0 w = w := by
  rw [Ucf_apply, cfW_zero, hU.2]

/-- `U_β` lowers the level by `|β|`. -/
theorem Ucf_graded (α β γ : ℕ+ →₀ ℕ) (h : lvl β + lvl γ ≠ lvl α) :
    coeff γ (Ucf U β (monomial α 1)) = 0 := by
  refine fam_unique (ι := (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ))
    (fun i β => coeff i.2 (Ucf U β (monomial i.1 1)))
    (fun i w => w + lvl i.2 ≠ lvl i.1) ?_ ?_ (lvl β) (α, γ) h β rfl
  · rintro ⟨α, γ⟩ hZ
    simp only at hZ ⊢
    rw [Ucf_zero hU, coeff_monomial, if_neg]
    rintro rfl
    exact hZ (by omega)
  · rintro ⟨α, γ⟩ w hZ k hk δ hδ ih
    simp only at hZ ⊢
    have h1 := DkF_map (MvPolynomial.lcoeff ℂ γ).toAddMonoidHom k
      (fun β' => Ucf U β' (monomial α 1)) δ
    simp only [LinearMap.toAddMonoidHom_coe, lcoeff_apply] at h1
    rw [← h1, Ucf_ode hU k hk, coeff_neg, neg_eq_zero]
    have hv : Ucf U δ (monomial α 1) ∈ levelSub (lvl α - lvl δ) := by
      intro γ' hγ'
      by_contra hne
      refine hγ' (ih (α, γ') (lvl δ) (by omega) ?_ δ rfl)
      show lvl δ + lvl γ' ≠ lvl α
      intro he
      apply hne
      show lvl γ' = lvl α - lvl δ
      omega
    exact coeff_ffOp_pos_of_level 0 0 hk hv γ (by omega)

/-! ### The adjoint family -/

end Diffeo

/-- `U_β^†`, the adjoint of `U_β` for the form (3.1) (sphere/paper.tex l.1102–1105): on `u^γ`
the sum over the `u^α` of level `|γ| + |β|` with the conjugated coefficients. -/
noncomputable def Udg (U : Fock →ₗ[ℂ] HH) (β : ℕ+ →₀ ℕ) : Fock →ₗ[ℂ] Fock :=
  (basisMonomials ℕ+ ℂ).constr ℂ fun γ => ∑ α ∈ (finite_level (lvl γ + lvl β)).toFinset,
    ((starRingEnd ℂ) (coeff γ (Ucf U β (monomial α 1))) * fockNorm γ / fockNorm α) •
      monomial α (1 : ℂ)

theorem Udg_monomial (U : Fock →ₗ[ℂ] HH) (β γ : ℕ+ →₀ ℕ) :
    Udg U β (monomial γ 1) = ∑ α ∈ (finite_level (lvl γ + lvl β)).toFinset,
      ((starRingEnd ℂ) (coeff γ (Ucf U β (monomial α 1))) * fockNorm γ / fockNorm α) •
        monomial α (1 : ℂ) := by
  have h := (basisMonomials ℕ+ ℂ).constr_basis ℂ (fun γ =>
    ∑ α ∈ (finite_level (lvl γ + lvl β)).toFinset,
      ((starRingEnd ℂ) (coeff γ (Ucf U β (monomial α 1))) * fockNorm γ / fockNorm α) •
        monomial α (1 : ℂ)) γ
  rwa [coe_basisMonomials] at h

theorem Udg_mem_level (U : Fock →ₗ[ℂ] HH) (β γ : ℕ+ →₀ ℕ) :
    Udg U β (monomial γ 1) ∈ levelSub (lvl γ + lvl β) := by
  rw [Udg_monomial]
  refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
  have h := monomial_mem_levelSub α
  rwa [(Set.Finite.mem_toFinset _).mp hα] at h

section Diffeo2

variable {U : Fock →ₗ[ℂ] HH} (hU : IsDiffeoU U)

include hU

theorem Udg_adj_monomial (β γ α : ℕ+ →₀ ℕ) :
    fockForm (Udg U β (monomial γ 1)) (monomial α 1) =
      fockForm (monomial γ 1) (Ucf U β (monomial α 1)) := by
  classical
  rw [fockForm_monomial_right, fockForm_monomial_left, Udg_monomial, coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases h : lvl α = lvl γ + lvl β
  · rw [if_pos (show α ∈ (finite_level (lvl γ + lvl β)).toFinset from
      (Set.Finite.mem_toFinset _).mpr h), map_div₀, map_mul, Complex.conj_conj,
      conj_fockNorm, conj_fockNorm]
    have hN := fockNorm_ne_zero α
    field_simp
  · rw [if_neg (fun h' : α ∈ (finite_level (lvl γ + lvl β)).toFinset =>
      h (show α ∈ {α : ℕ+ →₀ ℕ | lvl α = lvl γ + lvl β} from
        (Set.Finite.mem_toFinset _).mp h')), map_zero, zero_mul,
      Ucf_graded hU α β γ (by omega), zero_mul]

/-- `⟨U_β^† a, b⟩ = ⟨a, U_β b⟩`. -/
theorem Udg_adj (β : ℕ+ →₀ ℕ) (a b : Fock) :
    fockForm (Udg U β a) b = fockForm a (Ucf U β b) := by
  induction a using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add, fockForm_add_left, fockForm_add_left, hp, hq]
  | monomial γ c =>
    have hm : monomial γ c = c • monomial γ (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hm, map_smul, fockForm_smul_left, fockForm_smul_left]
    congr 1
    induction b using MvPolynomial.induction_on' with
    | add p q hp hq => rw [map_add, fockForm_add_right, fockForm_add_right, hp, hq]
    | monomial α e =>
      have hm' : monomial α e = e • monomial α (1 : ℂ) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [hm', map_smul, fockForm_smul_right, fockForm_smul_right, Udg_adj_monomial hU]

/-- `⟨a, U_β^† b⟩ = ⟨U_β a, b⟩`. -/
theorem Udg_adj' (β : ℕ+ →₀ ℕ) (a b : Fock) :
    fockForm a (Udg U β b) = fockForm (Ucf U β a) b := by
  rw [fockForm_conj, Udg_adj hU, ← fockForm_conj]

theorem Udg_zero : Udg U 0 = LinearMap.id :=
  op_ext_form fun a b => by rw [Udg_adj hU, Ucf_zero hU, LinearMap.id_apply]

/-- `D_k(U(W)^†) = -U(W)^† l_{-k}^{(2)}` on coefficients (sphere/paper.tex l.1111–1114). -/
theorem Udg_ode (hF : Cited_FeiginFuchsOperators) (k : ℕ) (hk : 1 ≤ k) (β : ℕ+ →₀ ℕ) :
    DkF k (Udg U) β = -(Udg U β ∘ₗ ffOp (0 : ℂ) 0 (-(k : ℤ))) := by
  refine op_ext_form fun a b => ?_
  let φ : (Fock →ₗ[ℂ] Fock) →+ ℂ :=
    { toFun := fun T => fockForm (T a) b
      map_zero' := by simp
      map_add' := fun S T => by rw [LinearMap.add_apply, fockForm_add_left] }
  let ψ : Fock →+ ℂ :=
    { toFun := fun v => fockForm a v
      map_zero' := by simp
      map_add' := fun v w => fockForm_add_right a v w }
  have h1 : φ (DkF k (Udg U) β) = DkF k (fun β' => φ (Udg U β')) β := DkF_map φ k _ β
  have h2 : ψ (DkF k (fun β' => Ucf U β' b) β) = DkF k (fun β' => ψ (Ucf U β' b)) β :=
    DkF_map ψ k _ β
  have h3 : (fun β' => φ (Udg U β')) = fun β' => ψ (Ucf U β' b) := by
    funext β'
    exact Udg_adj hU β' a b
  have h4 : fockForm (DkF k (Udg U) β a) b = fockForm a (DkF k (fun β' => Ucf U β' b) β) := by
    change φ (DkF k (Udg U) β) = ψ (DkF k (fun β' => Ucf U β' b) β)
    rw [h1, h2, h3]
  have h5 := hF.2 0 0 (-(k : ℤ)) a (Ucf U β b)
  simp only [Complex.ofReal_zero, neg_neg] at h5
  rw [h4, Ucf_ode hU k hk, LinearMap.neg_apply, fockForm_neg_left, LinearMap.comp_apply,
    Udg_adj hU, h5]
  have h6 := fockForm_add_right a (-ffOp (0 : ℂ) 0 (k : ℤ) (Ucf U β b))
    (ffOp (0 : ℂ) 0 (k : ℤ) (Ucf U β b))
  rw [neg_add_cancel, fockForm_zero_right] at h6
  exact eq_neg_of_add_eq_zero_left h6.symm

end Diffeo2

end Virasoro.Sphere
