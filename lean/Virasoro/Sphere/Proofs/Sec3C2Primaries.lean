import Virasoro.Sphere.Proofs.Sec3C2Stacked
import Virasoro.Sphere.Proofs.Sec3C2Perturb

/-!
# Lemma 3.7, Step 2: the large-`λ` primaries and `U(W)` (sphere paper)

sphere/paper.tex l.1084–1093.  The stacked system is injective at `λ^{-2} = 0`, hence for all
sufficiently large `λ`; since `dim 𝒫_n(λ) = p(n) = dim (ℱ^{(2)})_n`, `ev_0` restricted to
`𝒫_n(λ)` is an isomorphism, and its inverse `w ↦ P_w` is regular at `λ^{-2} = 0`:
`P_w(iλW,u) → U(W)w`, where `U(W)` solves `(D_k + l_k^{(2)})U(W) = 0`, `U(0) = id`.
-/

namespace Virasoro.Sphere

open MvPolynomial TensorProduct Filter Topology

theorem mem_primSpace {lam : ℂ} {n : ℕ} {y : HH} :
    y ∈ primSpace lam n ↔ y ∈ hhLevel n ∧ ∀ k : ℕ, 1 ≤ k → k ≤ n → Ltot lam (k : ℤ) y = 0 := by
  simp only [primSpace, Submodule.mem_inf, Submodule.mem_iInf, Finset.mem_Icc, LinearMap.mem_ker,
    and_imp]

theorem repr_rescH (lam : ℂ) (y : HH) (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)) :
    hhBasis.repr (rescH lam y) p = (Complex.I * lam) ^ p.1.degree * hhBasis.repr y p := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz =>
    rw [map_add, map_add, Finsupp.add_apply, hy, hz, map_add, Finsupp.add_apply, mul_add]
  | tmul a b =>
    rw [rescH_tmul, hhBasis_repr_tmul, hhBasis_repr_tmul, coeff_rescW]
    ring

theorem rescH_injective (lam : ℂ) (hlam : lam ≠ 0) : Function.Injective (rescH lam) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  apply hhBasis.repr.map_eq_zero_iff.mp
  ext p
  have h := repr_rescH lam y p
  rw [hy, map_zero, Finsupp.zero_apply] at h
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact absurd h1 (pow_ne_zero _ (mul_ne_zero Complex.I_ne_zero hlam))
  · rw [h1, Finsupp.zero_apply]

theorem rescH_mem_level (lam : ℂ) {n : ℕ} {y : HH} (hy : y ∈ hhLevel n) :
    rescH lam y ∈ hhLevel n := by
  rw [hhLevel, Module.Basis.mem_span_image] at hy ⊢
  intro p hp
  have hp' := Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hp)
  rw [repr_rescH] at hp'
  exact hy (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hp')))

theorem evAt_zero_rescH (lam : ℂ) (y : HH) : evAt 0 (rescH lam y) = evAt 0 y := by
  ext γ
  rw [coeff_evAt_zero, coeff_evAt_zero, repr_rescH]
  simp

theorem evAt_zero_mem_level {n : ℕ} {y : HH} (hy : y ∈ hhLevel n) : evAt 0 y ∈ levelSub n := by
  rw [hhLevel, Module.Basis.mem_span_image] at hy
  intro γ hγ
  rw [coeff_evAt_zero] at hγ
  have h : lvl (0 : ℕ+ →₀ ℕ) + lvl γ = n :=
    hy (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hγ))
  have h0 : lvl (0 : ℕ+ →₀ ℕ) = 0 := by simp [lvl]
  show lvl γ = n
  omega

theorem Tk_eq (s : ℂ) (k : ℕ) (x : HH) :
    Tk s k x = Tk 0 k x + s • TensorProduct.map (lapSum k) LinearMap.id x := by
  simp only [Tk, zero_smul, add_zero, LinearMap.add_apply, TensorProduct.map_add_left,
    TensorProduct.map_smul_left, LinearMap.smul_apply]
  abel

theorem Tk_zero_kill (k m : ℕ) (hmk : m < k) (x : HH) (hx : x ∈ hhLevel m) : Tk 0 k x = 0 := by
  have h := hhLevel_le_comap m (Tk 0 k) ⊥ (fun α β hαβ => by
    have h1 : Dop k (monomial α (1 : ℂ)) = 0 := by
      ext γ
      rw [coeff_Dop_of_level k (by omega) (monomial_mem_levelSub α) γ (by omega), coeff_zero]
    rw [Submodule.mem_bot, Tk_zero_tmul, h1,
      ffOp_pos_kill 0 0 (by omega) (monomial_mem_levelSub β), TensorProduct.zero_tmul,
      TensorProduct.tmul_zero, add_zero]) x hx
  exact (Submodule.mem_bot ℂ).mp h

/-- `r = U(W)w` for `w` of level `n`: `r` has level `n`, `(D_k + l_k^{(2)})r = 0` for
`1 ≤ k ≤ n`, and `r|_{W=0} = w`. -/
def IsDiffeoVec (n : ℕ) (w : Fock) (r : HH) : Prop :=
  r ∈ hhLevel n ∧ (∀ k : ℕ, 1 ≤ k → k ≤ n → Tk 0 k r = 0) ∧ evAt 0 r = w

theorem isDiffeoVec_unique {n : ℕ} {w : Fock} {r r' : HH} (h : IsDiffeoVec n w r)
    (h' : IsDiffeoVec n w r') : r = r' := by
  rw [← sub_eq_zero]
  exact stacked_injective n _ (Submodule.sub_mem _ h.1 h'.1)
    (fun k hk hkn => by rw [map_sub, h.2.1 k hk hkn, h'.2.1 k hk hkn, sub_self])
    (by rw [map_sub, h.2.2, h'.2.2, sub_self])

/-! ### The stacked system on level `n` -/

section Stacked

variable (n : ℕ)

/-- The stacked system at `λ^{-2} = 0`: `x ↦ ((D_k + l_k^{(2)})x)_{1≤k≤n}, x|_{W=0}`. -/
noncomputable def stk0 : hhLevel n →ₗ[ℂ] (Fin n → HH) × Fock :=
  LinearMap.prod (LinearMap.pi fun k : Fin n => Tk 0 ((k : ℕ) + 1) ∘ₗ (hhLevel n).subtype)
    (evAt 0 ∘ₗ (hhLevel n).subtype)

/-- The coefficient of `λ^{-2}/4` in the stacked system. -/
noncomputable def stk1 : hhLevel n →ₗ[ℂ] (Fin n → HH) × Fock :=
  LinearMap.prod (LinearMap.pi fun k : Fin n =>
    TensorProduct.map (lapSum ((k : ℕ) + 1)) LinearMap.id ∘ₗ (hhLevel n).subtype) 0

theorem stk_apply (s : ℂ) (x : hhLevel n) :
    stk0 n x + s • stk1 n x = (fun k : Fin n => Tk s ((k : ℕ) + 1) (x : HH), evAt 0 (x : HH)) := by
  refine Prod.ext (funext fun k => ?_) ?_
  · show Tk 0 ((k : ℕ) + 1) (x : HH) +
      s • TensorProduct.map (lapSum ((k : ℕ) + 1)) LinearMap.id (x : HH) =
        Tk s ((k : ℕ) + 1) (x : HH)
    rw [Tk_eq s]
  · show evAt 0 (x : HH) + s • (0 : Fock) = _
    rw [smul_zero, add_zero]

theorem stk0_ker : LinearMap.ker (stk0 n) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h1 : ∀ k : Fin n, Tk 0 ((k : ℕ) + 1) (x : HH) = 0 :=
    fun k => congrFun (congrArg Prod.fst hx) k
  have h2 : evAt 0 (x : HH) = 0 := congrArg Prod.snd hx
  have h3 := stacked_injective n x x.2 (fun k hk hkn => by
    have h := h1 ⟨k - 1, by omega⟩
    have e : k - 1 + 1 = k := by omega
    simp only [e] at h
    exact h) h2
  exact Subtype.ext h3

/-- `1/(4λ²)`. -/
noncomputable def sig (lam : ℝ) : ℂ := 1 / (4 * (lam : ℂ) ^ 2)

theorem tendsto_sig : Tendsto sig atTop (𝓝 0) := by
  have h1 : Tendsto (fun lam : ℝ => 1 / (4 * lam ^ 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Tendsto.const_mul_atTop (by norm_num) (tendsto_pow_atTop two_ne_zero))
  have h2 : Tendsto (fun lam : ℝ => ((1 / (4 * lam ^ 2) : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp h1
  rw [Complex.ofReal_zero] at h2
  refine h2.congr fun lam => ?_
  rw [sig]
  push_cast
  ring

theorem prim_resc_eq (lam : ℝ) (hlam : 0 < lam) {y : HH} (hy : y ∈ primSpace (lam : ℂ) n)
    (hmem : rescH (lam : ℂ) y ∈ hhLevel n) :
    stk0 n ⟨rescH (lam : ℂ) y, hmem⟩ + sig lam • stk1 n ⟨rescH (lam : ℂ) y, hmem⟩ =
      (0, evAt 0 y) := by
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  rw [stk_apply]
  refine Prod.ext (funext fun k => ?_) (evAt_zero_rescH _ _)
  show Tk (sig lam) ((k : ℕ) + 1) (rescH (lam : ℂ) y) = 0
  rw [sig, ← rescH_Ltot (lam : ℂ) hl ((k : ℕ) + 1) (by omega),
    (mem_primSpace.mp hy).2 ((k : ℕ) + 1) (by omega) (by have := k.2; omega), map_zero]

end Stacked

/-! ### The primaries `P_w` and their limit -/

section Cited

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
set_option maxHeartbeats 1600000 in
theorem primaries_level (n : ℕ) :
    ∃ P : ℝ → (finite_level n).toFinset → HH,
      (∀ᶠ lam : ℝ in atTop,
        ∃ b : Module.Basis (finite_level n).toFinset ℂ (primSpace (lam : ℂ) n),
          ∀ α, (b α : HH) = P lam α) ∧
      ∀ α : (finite_level n).toFinset, ∃ r : HH, IsDiffeoVec n (monomial α.1 1) r ∧
        ∀ p, Tendsto (fun lam : ℝ => hhBasis.repr (rescH (lam : ℂ) (P lam α)) p) atTop
          (𝓝 (hhBasis.repr r p)) := by
  classical
  obtain ⟨hker, hlim⟩ := perturb_limit (stk0 n) (stk1 n) (stk0_ker n) atTop sig tendsto_sig
  have hfinL : Module.Finite ℂ (levelSub n) := by
    rw [levelSub_eq_span]
    exact FiniteDimensional.span_of_finite ℂ ((finite_level n).toFinset.finite_toSet.image _)
  have hex : ∀ᶠ lam : ℝ in atTop, ∀ α : (finite_level n).toFinset,
      ∃ y ∈ primSpace (lam : ℂ) n, evAt 0 y = monomial α.1 (1 : ℂ) := by
    filter_upwards [hker, eventually_gt_atTop 0] with lam hk hlam
    have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
    let e : primSpace (lam : ℂ) n →ₗ[ℂ] levelSub n :=
      LinearMap.codRestrict (levelSub n) (evAt 0 ∘ₗ (primSpace (lam : ℂ) n).subtype)
        (fun y => evAt_zero_mem_level (mem_primSpace.mp y.2).1)
    have hinj : Function.Injective e := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      have hy0 : evAt 0 (y : HH) = 0 := congrArg Subtype.val hy
      have hmem := rescH_mem_level (lam : ℂ) (mem_primSpace.mp y.2).1
      have h1 := prim_resc_eq n lam hlam y.2 hmem
      rw [hy0] at h1
      have h2 : (⟨rescH (lam : ℂ) (y : HH), hmem⟩ : hhLevel n) ∈
          LinearMap.ker (stk0 n + sig lam • stk1 n) := by
        rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.smul_apply, h1]
        rfl
      rw [hk] at h2
      have h3 : rescH (lam : ℂ) (y : HH) = 0 := congrArg Subtype.val ((Submodule.mem_bot ℂ).mp h2)
      exact Subtype.ext (rescH_injective (lam : ℂ) hl (by rw [h3]; simp))
    have hfr : Module.finrank ℂ (primSpace (lam : ℂ) n) = Module.finrank ℂ (levelSub n) := by
      rw [finrank_primSpace hF hK lam hlam n, finrank_levelSub hF hK n]
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj
    intro α
    have hα : lvl α.1 = n := by
      have h := α.2
      rwa [Set.Finite.mem_toFinset] at h
    obtain ⟨y, hy⟩ := hsurj ⟨monomial α.1 1, by
      have h := monomial_mem_levelSub α.1
      rwa [hα] at h⟩
    exact ⟨y, y.2, congrArg Subtype.val hy⟩
  let P : ℝ → (finite_level n).toFinset → HH := fun lam α =>
    if h : ∃ y ∈ primSpace (lam : ℂ) n, evAt 0 y = monomial α.1 (1 : ℂ) then Classical.choose h
    else 0
  have hP : ∀ᶠ lam : ℝ in atTop, ∀ α : (finite_level n).toFinset,
      P lam α ∈ primSpace (lam : ℂ) n ∧ evAt 0 (P lam α) = monomial α.1 (1 : ℂ) := by
    filter_upwards [hex] with lam h α
    simp only [P, dif_pos (h α)]
    exact Classical.choose_spec (h α)
  refine ⟨P, ?_, ?_⟩
  · filter_upwards [hP, eventually_gt_atTop 0] with lam h hlam
    have hli : LinearIndependent ℂ (fun α : (finite_level n).toFinset =>
        (⟨P lam α, (h α).1⟩ : primSpace (lam : ℂ) n)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg α0
      have h1 := congrArg (fun y : primSpace (lam : ℂ) n => coeff α0.1 (evAt 0 (y : HH))) hg
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, (h _).2,
        Submodule.coe_zero, map_zero, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul,
        coeff_zero] at h1
      rw [Finset.sum_eq_single α0 (fun b _ hb => by
          rw [if_neg (fun hh => hb (Subtype.ext hh)), mul_zero])
        (fun hh => absurd (Finset.mem_univ _) hh), if_pos rfl, mul_one] at h1
      exact h1
    have hcard : Fintype.card (finite_level n).toFinset =
        Module.finrank ℂ (primSpace (lam : ℂ) n) := by
      rw [Fintype.card_coe, card_finite_level hF hK, finrank_primSpace hF hK lam hlam]
    exact ⟨basisOfLinearIndependentOfCardEqFinrank' _ hli hcard, fun α => by
      rw [coe_basisOfLinearIndependentOfCardEqFinrank']⟩
  · intro α
    let yX : ℝ → hhLevel n := fun lam =>
      if h : rescH (lam : ℂ) (P lam α) ∈ hhLevel n then ⟨_, h⟩ else 0
    have hy : ∀ᶠ lam : ℝ in atTop,
        stk0 n (yX lam) + sig lam • stk1 n (yX lam) = (0, monomial α.1 (1 : ℂ)) := by
      filter_upwards [hP, eventually_gt_atTop 0] with lam h hlam
      have hmem := rescH_mem_level (lam : ℂ) (mem_primSpace.mp (h α).1).1
      simp only [yX, dif_pos hmem]
      rw [prim_resc_eq n lam hlam (h α).1 hmem, (h α).2]
    obtain ⟨r, hr0, hrlim⟩ := hlim yX _ hy
    refine ⟨(r : HH), ⟨r.2, ?_, congrArg Prod.snd hr0⟩, ?_⟩
    · intro k hk hkn
      have h := congrFun (congrArg Prod.fst hr0) ⟨k - 1, by omega⟩
      have e : k - 1 + 1 = k := by omega
      have h' : Tk 0 (k - 1 + 1) (r : HH) = 0 := h
      rwa [e] at h'
    · intro p
      have h1 := hrlim (hhBasis.coord p ∘ₗ (hhLevel n).subtype)
      refine h1.congr' ?_
      filter_upwards [hP] with lam h
      have hmem := rescH_mem_level (lam : ℂ) (mem_primSpace.mp (h α).1).1
      simp only [yX, dif_pos hmem]
      rfl

include hF hK in
theorem exists_diffeoVec (α : ℕ+ →₀ ℕ) : ∃ r : HH, IsDiffeoVec (lvl α) (monomial α 1) r := by
  obtain ⟨P, -, h⟩ := primaries_level hF hK (lvl α)
  obtain ⟨r, hr, -⟩ := h ⟨α, (Set.Finite.mem_toFinset _).mpr rfl⟩
  exact ⟨r, hr⟩

/-- `U(W)`: on `u^α` the unique vector of level `|α|` with `(D_k + l_k^{(2)})r = 0` and
`r|_{W=0} = u^α` (sphere/paper.tex l.1091–1093). -/
noncomputable def diffeoU : Fock →ₗ[ℂ] HH :=
  (basisMonomials ℕ+ ℂ).constr ℂ fun α => Classical.choose (exists_diffeoVec hF hK α)

theorem diffeoU_monomial (α : ℕ+ →₀ ℕ) :
    IsDiffeoVec (lvl α) (monomial α 1) (diffeoU hF hK (monomial α 1)) := by
  have h := (basisMonomials ℕ+ ℂ).constr_basis ℂ
    (fun α => Classical.choose (exists_diffeoVec hF hK α)) α
  rw [coe_basisMonomials] at h
  rw [diffeoU, h]
  exact Classical.choose_spec (exists_diffeoVec hF hK α)

theorem isDiffeoU_diffeoU : IsDiffeoU (diffeoU hF hK) := by
  constructor
  · intro k hk w
    have key : (TensorProduct.map (Dop k) LinearMap.id +
        TensorProduct.map LinearMap.id (ffOp (0 : ℂ) 0 (k : ℤ))) ∘ₗ diffeoU hF hK = 0 := by
      apply (basisMonomials ℕ+ ℂ).ext
      intro α
      rw [coe_basisMonomials, LinearMap.comp_apply, LinearMap.zero_apply]
      have h := diffeoU_monomial hF hK α
      have e : ∀ x : HH, ((TensorProduct.map (Dop k) LinearMap.id +
          TensorProduct.map LinearMap.id (ffOp (0 : ℂ) 0 (k : ℤ)) : HH →ₗ[ℂ] HH)) x =
          Tk 0 k x := fun x => by
        simp only [Tk, zero_smul, add_zero]
      rw [e]
      by_cases hkα : k ≤ lvl α
      · exact h.2.1 k hk hkα
      · exact Tk_zero_kill k (lvl α) (by omega) _ h.1
    exact LinearMap.congr_fun key w
  · intro w
    have key : evAt 0 ∘ₗ diffeoU hF hK = LinearMap.id := by
      apply (basisMonomials ℕ+ ℂ).ext
      intro α
      rw [coe_basisMonomials]
      exact (diffeoU_monomial hF hK α).2.2
    exact LinearMap.congr_fun key w

include hF hK in
/-- Lemma 3.7, Step 2, first half (sphere/paper.tex l.1074–1093). -/
theorem sub_c2_primaries : Stmt_sub_c2_primaries := by
  refine ⟨diffeoU hF hK, isDiffeoU_diffeoU hF hK, fun n => ?_⟩
  obtain ⟨P, hb, h⟩ := primaries_level hF hK n
  refine ⟨P, hb, fun α p => ?_⟩
  obtain ⟨r, hr, hlim⟩ := h α
  have hα : lvl α.1 = n := by
    have h := α.2
    rwa [Set.Finite.mem_toFinset] at h
  have h1 := diffeoU_monomial hF hK α.1
  rw [hα] at h1
  rw [isDiffeoVec_unique h1 hr]
  exact hlim p

end Cited

end Virasoro.Sphere
