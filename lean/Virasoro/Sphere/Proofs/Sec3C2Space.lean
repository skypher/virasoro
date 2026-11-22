import Virasoro.Sphere.Proofs.Sec3C2Defs
import Virasoro.Sphere.Proofs.Sec3UVirNorm

/-!
# The two-boson space as a unitary `c = 2` representation (sphere paper, Lemma 3.7)

sphere/paper.tex l.1023–1027: `ℋ_λ = ℱ^{(1)}_{0,λ} ⊗ ℱ^{(2)}_{0,0}` carries the diagonal unitary
`c = 2` Virasoro action `L_k^tot = l_k^{(1)} + l_k^{(2)}`.  The Virasoro relations and
`(L_k^tot)† = L_{-k}^tot` follow from the cited properties of the operators (3.2) on each
factor.
-/

namespace Virasoro.Sphere

open MvPolynomial TensorProduct

/-! ### A weighted Hermitian form on coordinates -/

section WForm

variable {I : Type*} (ν : I → ℝ)

/-- `∑_i conj(x_i) y_i ν_i`. -/
noncomputable def wform (x y : I →₀ ℂ) : ℂ :=
  ∑ i ∈ y.support, (starRingEnd ℂ) (x i) * y i * (ν i : ℂ)

theorem wform_eq (x y : I →₀ ℂ) (s : Finset I) (hs : y.support ⊆ s) :
    wform ν x y = ∑ i ∈ s, (starRingEnd ℂ) (x i) * y i * (ν i : ℂ) :=
  Finset.sum_subset hs fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi]
    ring

theorem wform_add_right (x y y' : I →₀ ℂ) :
    wform ν x (y + y') = wform ν x y + wform ν x y' := by
  classical
  rw [wform_eq ν x (y + y') (y.support ∪ y'.support) Finsupp.support_add,
    wform_eq ν x y _ Finset.subset_union_left, wform_eq ν x y' _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.add_apply]
  ring

theorem wform_smul_right (a : ℂ) (x y : I →₀ ℂ) :
    wform ν x (a • y) = a * wform ν x y := by
  rw [wform_eq ν x (a • y) y.support Finsupp.support_smul, wform, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul]
  ring

theorem wform_conj (x y : I →₀ ℂ) : wform ν y x = (starRingEnd ℂ) (wform ν x y) := by
  classical
  rw [wform_eq ν y x (x.support ∪ y.support) Finset.subset_union_left,
    wform_eq ν x y (x.support ∪ y.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem wform_def (hν : ∀ i, 0 < ν i) (x : I →₀ ℂ) (h : wform ν x x = 0) : x = 0 := by
  have hre : ∑ j ∈ x.support, Complex.normSq (x j) * ν j = 0 := by
    have h1 := congrArg Complex.re h
    rw [wform, Complex.re_sum, Complex.zero_re] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]
  ext i
  by_contra hi
  have hmem : i ∈ x.support := Finsupp.mem_support_iff.mpr hi
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (Complex.normSq_nonneg _) (hν j).le)).mp hre i hmem
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact hi (Complex.normSq_eq_zero.mp h3)
  · exact (hν i).ne' h3

end WForm

/-! ### Levels of the Fock space -/

theorem coeff_eq_zero_of_level {M : ℕ} {f : Fock} (hf : f ∈ levelSub M) (δ : ℕ+ →₀ ℕ)
    (h : lvl δ ≠ M) : coeff δ f = 0 := by
  by_contra hne
  exact h (hf hne)

theorem monomial_mem_levelSub (α : ℕ+ →₀ ℕ) : (monomial α (1 : ℂ)) ∈ levelSub (lvl α) :=
  isWeightedHomogeneous_monomial fockWeight α 1 rfl

theorem coeff_ffOp_pos_of_level (μ lam : ℂ) {M k : ℕ} (hk : 1 ≤ k) {f : Fock}
    (hf : f ∈ levelSub M) (γ : ℕ+ →₀ ℕ) (h : lvl γ + k ≠ M) :
    coeff γ (ffOp μ lam (k : ℤ) f) = 0 := by
  have hz : ∀ δ : ℕ+ →₀ ℕ, lvl δ ≠ M → coeff δ f = 0 := coeff_eq_zero_of_level hf
  have hjk : ∀ j : ℕ, 1 ≤ j → ((j.toPNat' : ℕ+) : ℕ) = j := fun j hj => PNat.toPNat'_coe hj
  rw [ffOp_eq_ffOpR, coeff_ffOpR_pos _ _ k hk]
  simp only [coeff_pderiv]
  have e1 : ∀ j ∈ γ.support,
      coeff (γ - Finsupp.single j 1 + Finsupp.single ((j : ℕ) + k).toPNat' 1) f = 0 :=
    fun j hj => hz _ (by
      have e := congrArg lvl (sub_add_single hj)
      rw [lvl_add, lvl_single] at e
      rw [lvl_add, lvl_single, hjk _ (by omega)]
      omega)
  have e2 : ∀ n ∈ Finset.Icc 1 (k - 1),
      coeff (γ + Finsupp.single n.toPNat' 1 + Finsupp.single (k - n).toPNat' 1) f = 0 :=
    fun n hn => hz _ (by
      rw [Finset.mem_Icc] at hn
      rw [lvl_add, lvl_add, lvl_single, lvl_single, hjk _ (by omega), hjk _ (by omega)]
      omega)
  have e3 : coeff (γ + Finsupp.single k.toPNat' 1) f = 0 :=
    hz _ (by rw [lvl_add, lvl_single, hjk _ hk]; omega)
  rw [Finset.sum_eq_zero (fun j hj => by rw [e1 j hj]; ring),
    Finset.sum_eq_zero (fun n hn => by rw [e2 n hn]; ring), e3]
  ring

theorem ffOp_pos_mem_level (μ lam : ℂ) {m k : ℕ} (hk : 1 ≤ k) {f : Fock}
    (hf : f ∈ levelSub (m + k)) : ffOp μ lam (k : ℤ) f ∈ levelSub m := by
  intro γ hγ
  by_contra h
  exact hγ (coeff_ffOp_pos_of_level μ lam hk hf γ (fun h' => h (by
    show lvl γ = m
    omega)))

theorem ffOp_pos_kill (μ lam : ℂ) {m k : ℕ} (hk : m < k) {f : Fock} (hf : f ∈ levelSub m) :
    ffOp μ lam (k : ℤ) f = 0 := by
  ext γ
  rw [coeff_ffOp_pos_of_level μ lam (by omega) hf γ (by omega), coeff_zero]

theorem ffOp_zero_of_level (μ lam : ℂ) {m : ℕ} {f : Fock} (hf : f ∈ levelSub m) :
    ffOp μ lam 0 f = (lam ^ 2 + μ ^ 2 + (m : ℂ)) • f := by
  ext γ
  rw [ffOp_eq_ffOpR, coeff_ffOpR_zero, coeff_smul, smul_eq_mul]
  by_cases h : lvl γ = m
  · rw [h]
    ring
  · rw [coeff_eq_zero_of_level hf γ h]
    ring

theorem fockForm_orth {m n : ℕ} (hmn : m ≠ n) {f g : Fock} (hf : f ∈ levelSub m)
    (hg : g ∈ levelSub n) : fockForm f g = 0 := by
  refine Finset.sum_eq_zero fun α hα => ?_
  have h1 : lvl α = n := hg (mem_support_iff.mp hα)
  rw [coeff_eq_zero_of_level hf α (by omega)]
  simp

/-! ### The form of `ℋ_λ` -/

theorem fockNormQ_pos (α : ℕ+ →₀ ℕ) : 0 < fockNormQ α := by
  unfold fockNormQ Finsupp.prod
  refine Finset.prod_pos fun m _ => ?_
  exact div_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
    (pow_pos (mul_pos two_pos (Nat.cast_pos.mpr m.pos)) _)

/-- The weights of the form of `ℋ_λ` as real numbers. -/
noncomputable def hhNu (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)) : ℝ :=
  (fockNormQ p.1 : ℝ) * (fockNormQ p.2 : ℝ)

theorem hhNu_pos (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)) : 0 < hhNu p :=
  mul_pos (by exact_mod_cast fockNormQ_pos p.1) (by exact_mod_cast fockNormQ_pos p.2)

theorem hhForm_eq_wform (x y : HH) : hhForm x y = wform hhNu (hhBasis.repr x) (hhBasis.repr y) := by
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [fockNorm_eq, fockNorm_eq, hhNu]
  push_cast
  rfl

theorem hhForm_add_right (x y y' : HH) : hhForm x (y + y') = hhForm x y + hhForm x y' := by
  rw [hhForm_eq_wform, hhForm_eq_wform, hhForm_eq_wform, map_add, wform_add_right]

theorem hhForm_smul_right (a : ℂ) (x y : HH) : hhForm x (a • y) = a * hhForm x y := by
  rw [hhForm_eq_wform, hhForm_eq_wform, map_smul, wform_smul_right]

theorem hhForm_conj (x y : HH) : hhForm y x = (starRingEnd ℂ) (hhForm x y) := by
  rw [hhForm_eq_wform, hhForm_eq_wform, wform_conj]

theorem hhForm_def (x : HH) (h : hhForm x x = 0) : x = 0 := by
  rw [hhForm_eq_wform] at h
  exact hhBasis.repr.map_eq_zero_iff.mp (wform_def hhNu hhNu_pos _ h)

theorem hhForm_add_left (x x' y : HH) : hhForm (x + x') y = hhForm x y + hhForm x' y := by
  rw [hhForm_conj y, hhForm_add_right, map_add, ← hhForm_conj, ← hhForm_conj]

theorem hhForm_zero_right (x : HH) : hhForm x 0 = 0 := by
  have h := hhForm_smul_right 0 x 0
  rwa [zero_smul, zero_mul] at h

theorem hhForm_zero_left (x : HH) : hhForm 0 x = 0 := by
  rw [hhForm_conj, hhForm_zero_right, map_zero]

theorem hhBasis_repr_tmul (a b : Fock) (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)) :
    hhBasis.repr (a ⊗ₜ[ℂ] b) p = coeff p.1 a * coeff p.2 b := by
  obtain ⟨i, j⟩ := p
  rw [hhBasis, Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, mul_comm]
  rfl

theorem hhBasis_apply (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)) :
    hhBasis p = monomial p.1 (1 : ℂ) ⊗ₜ[ℂ] monomial p.2 (1 : ℂ) := by
  rw [hhBasis, Module.Basis.tensorProduct_apply']
  rfl

/-- `⟨a ⊗ b, c ⊗ d⟩ = ⟨a, c⟩⟨b, d⟩`. -/
theorem hhForm_tmul (a b c d : Fock) :
    hhForm (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) = fockForm a c * fockForm b d := by
  classical
  have h1 : hhForm (a ⊗ₜ[ℂ] b) (c ⊗ₜ[ℂ] d) = ∑ p ∈ c.support ×ˢ d.support,
      (starRingEnd ℂ) (hhBasis.repr (a ⊗ₜ[ℂ] b) p) * hhBasis.repr (c ⊗ₜ[ℂ] d) p *
        (fockNorm p.1 * fockNorm p.2) := by
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      rw [Finsupp.mem_support_iff, hhBasis_repr_tmul] at hp
      rw [Finset.mem_product, mem_support_iff, mem_support_iff]
      exact ⟨left_ne_zero_of_mul hp, right_ne_zero_of_mul hp⟩
    · intro p _ hp
      rw [Finsupp.notMem_support_iff.mp hp]
      ring
  rw [h1, Finset.sum_product, fockForm, fockForm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hhBasis_repr_tmul, hhBasis_repr_tmul, map_mul]
  ring

/-! ### Levels of `ℋ_λ` -/

theorem tmul_mem_hhLevel {i j : ℕ} {a b : Fock} (ha : a ∈ levelSub i) (hb : b ∈ levelSub j) :
    a ⊗ₜ[ℂ] b ∈ hhLevel (i + j) := by
  rw [hhLevel, Module.Basis.mem_span_image]
  intro p hp
  have hp' := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hp)
  rw [hhBasis_repr_tmul] at hp'
  have h1 : lvl p.1 = i := ha (left_ne_zero_of_mul hp')
  have h2 : lvl p.2 = j := hb (right_ne_zero_of_mul hp')
  show lvl p.1 + lvl p.2 = i + j
  rw [h1, h2]

theorem hhLevel_le_comap (M : ℕ) (T : HH →ₗ[ℂ] HH) (S : Submodule ℂ HH)
    (h : ∀ α β : ℕ+ →₀ ℕ, lvl α + lvl β = M →
      T (monomial α (1 : ℂ) ⊗ₜ[ℂ] monomial β (1 : ℂ)) ∈ S) : ∀ x ∈ hhLevel M, T x ∈ S := by
  intro x hx
  have hle : hhLevel M ≤ S.comap T := Submodule.span_le.mpr (by
    rintro _ ⟨p, hp, rfl⟩
    show T (hhBasis p) ∈ S
    rw [hhBasis_apply]
    exact h p.1 p.2 hp)
  exact hle hx

theorem hhForm_orth (m n : ℕ) (x y : HH) (hmn : m ≠ n) (hx : x ∈ hhLevel m)
    (hy : y ∈ hhLevel n) : hhForm x y = 0 := by
  rw [hhLevel, Module.Basis.mem_span_image] at hx hy
  refine Finset.sum_eq_zero fun p hp => ?_
  have h2 : lvl p.1 + lvl p.2 = n := hy (Finset.mem_coe.mpr hp)
  have h1 : hhBasis.repr x p = 0 := by
    by_contra h
    have h3 : lvl p.1 + lvl p.2 = m := hx (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr h))
    exact hmn (h3.symm.trans h2)
  rw [h1]
  simp

theorem Ltot_tmul (lam : ℂ) (k : ℤ) (a b : Fock) :
    Ltot lam k (a ⊗ₜ[ℂ] b) = ffOp 0 lam k a ⊗ₜ[ℂ] b + a ⊗ₜ[ℂ] ffOp 0 0 k b := by
  simp only [Ltot, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply]

theorem Ltot_zero_level (lam : ℂ) (m : ℕ) (x : HH) (hx : x ∈ hhLevel m) :
    Ltot lam 0 x = (lam ^ 2 + (m : ℂ)) • x := by
  have h := hhLevel_le_comap m (Ltot lam 0 - (lam ^ 2 + (m : ℂ)) • LinearMap.id) ⊥
    (fun α β hαβ => by
      rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Ltot_tmul, ffOp_zero_of_level 0 lam (monomial_mem_levelSub α),
        ffOp_zero_of_level 0 0 (monomial_mem_levelSub β), TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', ← add_smul, sub_eq_zero]
      congr 1
      rw [← hαβ]
      push_cast
      ring) x hx
  rw [Submodule.mem_bot, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at h
  exact h

theorem Ltot_lower (lam : ℂ) (k m : ℕ) (x : HH) (hx : x ∈ hhLevel (m + k)) :
    Ltot lam (k : ℤ) x ∈ hhLevel m := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, Ltot_zero_level lam (m + 0) x hx]
    exact Submodule.smul_mem _ _ hx
  refine hhLevel_le_comap (m + k) _ _ (fun α β hαβ => ?_) x hx
  rw [Ltot_tmul]
  refine Submodule.add_mem _ ?_ ?_
  · by_cases h : k ≤ lvl α
    · have h1 : ffOp 0 lam (k : ℤ) (monomial α 1) ∈ levelSub (lvl α - k) :=
        ffOp_pos_mem_level 0 lam hk (by
          rw [Nat.sub_add_cancel h]
          exact monomial_mem_levelSub α)
      have h2 := tmul_mem_hhLevel h1 (monomial_mem_levelSub β)
      have e : lvl α - k + lvl β = m := by omega
      rwa [e] at h2
    · rw [ffOp_pos_kill 0 lam (by omega) (monomial_mem_levelSub α), TensorProduct.zero_tmul]
      exact Submodule.zero_mem _
  · by_cases h : k ≤ lvl β
    · have h1 : ffOp 0 0 (k : ℤ) (monomial β 1) ∈ levelSub (lvl β - k) :=
        ffOp_pos_mem_level 0 0 hk (by
          rw [Nat.sub_add_cancel h]
          exact monomial_mem_levelSub β)
      have h2 := tmul_mem_hhLevel (monomial_mem_levelSub α) h1
      have e : lvl α + (lvl β - k) = m := by omega
      rwa [e] at h2
    · rw [ffOp_pos_kill 0 0 (by omega) (monomial_mem_levelSub β), TensorProduct.tmul_zero]
      exact Submodule.zero_mem _

theorem Ltot_kill (lam : ℂ) (k m : ℕ) (x : HH) (hk : m < k) (hx : x ∈ hhLevel m) :
    Ltot lam (k : ℤ) x = 0 := by
  have h := hhLevel_le_comap m (Ltot lam (k : ℤ)) ⊥ (fun α β hαβ => by
    rw [Submodule.mem_bot, Ltot_tmul,
      ffOp_pos_kill 0 lam (by omega) (monomial_mem_levelSub α),
      ffOp_pos_kill 0 0 (by omega) (monomial_mem_levelSub β), TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, add_zero]) x hx
  exact (Submodule.mem_bot ℂ).mp h

theorem Ltot_raise (lam : ℂ) (k m : ℕ) (x : HH) (hx : x ∈ hhLevel m) :
    Ltot lam (-(k : ℤ)) x ∈ hhLevel (m + k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Nat.cast_zero, neg_zero, Ltot_zero_level lam m x hx]
    exact Submodule.smul_mem _ _ hx
  refine hhLevel_le_comap m _ _ (fun α β hαβ => ?_) x hx
  rw [Ltot_tmul]
  refine Submodule.add_mem _ ?_ ?_
  · have h1 : ffOp 0 lam (-(k : ℤ)) (monomial α 1) ∈ levelSub (lvl α + k) :=
      ffOp_neg_homog 0 lam k hk _ (monomial_mem_levelSub α)
    have h2 := tmul_mem_hhLevel h1 (monomial_mem_levelSub β)
    have e : lvl α + k + lvl β = m + k := by omega
    rwa [e] at h2
  · have h1 : ffOp 0 0 (-(k : ℤ)) (monomial β 1) ∈ levelSub (lvl β + k) :=
      ffOp_neg_homog 0 0 k hk _ (monomial_mem_levelSub β)
    have h2 := tmul_mem_hhLevel (monomial_mem_levelSub α) h1
    have e : lvl α + (lvl β + k) = m + k := by omega
    rwa [e] at h2

/-! ### The Virasoro relations and the adjoint -/

section Cited

variable (hF : Cited_FeiginFuchsOperators)
include hF

theorem hhForm_adj (lam : ℝ) (k : ℤ) (x y : HH) :
    hhForm (Ltot (lam : ℂ) k x) y = hhForm x (Ltot (lam : ℂ) (-k) y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [hhForm_zero_left]
  | add x x' hx hx' => rw [map_add, hhForm_add_left, hhForm_add_left, hx, hx']
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp [hhForm_zero_right]
    | add y y' hy hy' => rw [map_add, hhForm_add_right, hhForm_add_right, hy, hy']
    | tmul c d =>
      have h1 := hF.2 0 lam k a c
      have h2 := hF.2 0 0 k b d
      simp only [Complex.ofReal_zero] at h1 h2
      rw [Ltot_tmul, Ltot_tmul, hhForm_add_left, hhForm_add_right, hhForm_tmul, hhForm_tmul,
        hhForm_tmul, hhForm_tmul, h1, h2]

theorem Ltot_comm (lam : ℂ) (m n : ℤ) (x : HH) :
    Ltot lam m (Ltot lam n x) = Ltot lam n (Ltot lam m x) +
      ((m - n : ℤ) : ℂ) • Ltot lam (m + n) x +
      (if m + n = 0 then centralTerm (((2 : ℝ) : ℂ)) m • x else 0) := by
  induction x using TensorProduct.induction_on with
  | zero => split_ifs <;> simp
  | add x y hx hy =>
    simp only [map_add, hx, hy, smul_add]
    split_ifs <;> abel
  | tmul a b =>
    have hct : centralTerm (((2 : ℝ) : ℂ)) m =
        centralTerm (1 + 24 * (0 : ℂ) ^ 2) m + centralTerm (1 + 24 * (0 : ℂ) ^ 2) m := by
      simp only [centralTerm]
      push_cast
      ring
    simp only [Ltot_tmul, map_add]
    rw [ffOp_ffOp hF 0 lam m n a, ffOp_ffOp hF 0 0 m n b, hct]
    by_cases h : m + n = 0
    · simp only [if_pos h, TensorProduct.add_tmul, TensorProduct.tmul_add,
        ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
      module
    · simp only [if_neg h, add_zero, TensorProduct.add_tmul, TensorProduct.tmul_add,
        ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]
      module

/-- `ℋ_λ` with `L_k^tot` as a unitary representation at `c = 2`, `h₀ = λ²`. -/
noncomputable def hhUVir (lam : ℝ) : UVir HH where
  c := 2
  h0 := lam ^ 2
  L := Ltot (lam : ℂ)
  form := hhForm
  lev := hhLevel
  form_add_right := hhForm_add_right
  form_smul_right := hhForm_smul_right
  form_conj := hhForm_conj
  form_def := hhForm_def
  comm := Ltot_comm hF (lam : ℂ)
  adj := hhForm_adj hF lam
  lev_fin := fun m => hhLevel_finite m
  L_lower := Ltot_lower (lam : ℂ)
  L_kill := fun k m x hk hx => Ltot_kill (lam : ℂ) k m x hk hx
  L_raise := Ltot_raise (lam : ℂ)
  L_zero := fun m x hx => by
    rw [Ltot_zero_level (lam : ℂ) m x hx]
    push_cast
    rfl
  orth := fun m n x y hmn hx hy => hhForm_orth m n x y hmn hx hy

theorem hhUVir_prim (lam : ℝ) (n : ℕ) : (hhUVir hF lam).prim n = primSpace (lam : ℂ) n := rfl

end Cited

end Virasoro.Sphere
