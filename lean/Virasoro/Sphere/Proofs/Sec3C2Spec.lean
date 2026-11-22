import Virasoro.Sphere.Proofs.Sec3C2Conj
import Virasoro.Sphere.Proofs.Sec3C2Input

/-!
# Lemma 3.7, Step 3: applying `U(W_*)^†` and changing variables (sphere paper)

sphere/paper.tex l.1134–1139.  `U(W_*)^†` is the family `d ↦ T_d = ∑_{|β| = d} W_*^β U_β^†`
of its parts raising the level by `d`; `(U(W_*)^† F_2)_n = ∑_d T_d (F_2)_{n-d}`.  Applying
`U(W_*)^†` to `∮ x^{k-1}√(x(x-1)) α(x) dx · F_2 = 0` and using
`U(W)^† α(x) = f'(x;W) α(f(x;W)) U(W)^†` gives, after the change of variables `X = f(x;W_*)`,
`∮ x(X)^{k-1}(X - 1/(16X)) α(X) dX · U(W_*)^† F_2 = 0`.
-/

namespace Virasoro.Sphere

open MvPolynomial Finset

/-- `W_*^β = ∏_m W_{*,m}^{β_m}`. -/
noncomputable def wpow (β : ℕ+ →₀ ℕ) : ℂ := β.prod fun m e => Wstar m ^ e

theorem wpow_add (β1 β2 : ℕ+ →₀ ℕ) : wpow (β1 + β2) = wpow β1 * wpow β2 :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _

theorem wpow_zero : wpow 0 = 1 := Finsupp.prod_zero_index

theorem Wstar_eq_wN (m : ℕ+) : Wstar m = wN m := by
  have hm : ((m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.pos.ne'
  rw [Wstar, wN, halfBinom_eq, Nat.centralBinom]
  push_cast
  field_simp

theorem wpow_linExp (M : ℂ) (β : ℕ+ →₀ ℕ) :
    wpow β * linExpCoef (fun _ => M) β = linExpCoef (fun m => M * wN m) β := by
  unfold wpow linExpCoef Finsupp.prod
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  dsimp only
  rw [Wstar_eq_wN, mul_pow]
  ring

/-- The part of `U(W_*)^†` raising the level by `d`. -/
noncomputable def Tst (U : Fock →ₗ[ℂ] HH) (d : ℕ) : Fock →ₗ[ℂ] Fock :=
  ∑ β ∈ (finite_level d).toFinset, wpow β • Udg U β

theorem Tst_apply (U : Fock →ₗ[ℂ] HH) (d : ℕ) (v : Fock) :
    Tst U d v = ∑ β ∈ (finite_level d).toFinset, wpow β • Udg U β v := by
  simp only [Tst, LinearMap.sum_apply, LinearMap.smul_apply]

/-- `(U(W_*)^† F_2)_i`, zero for `i < 0`. -/
noncomputable def Yz (U : Fock →ₗ[ℂ] HH) (i : ℤ) : Fock := if 0 ≤ i then UdagF U i.toNat else 0

/-- The coefficient of `x^{-N-1}` in `f'(x;W_*) f(x;W_*)^{-(N-a)-1}`, from the coefficients in
`W`. -/
noncomputable def chat (a : ℕ) (N : ℤ) : ℂ :=
  ∑ β ∈ (finite_level a).toFinset, wpow β * thc β N

theorem alphaOp_zero : alphaOp 0 = 0 := by
  rw [alphaOp, if_neg (by omega), if_neg (by omega)]

/-- At `W = W_*` the coefficients of `f' α(f)` are those of the series `f(x;W_*)`. -/
theorem chat_smul (a : ℕ) (N : ℤ) :
    chat a N • alphaOp (N - a) = PowerSeries.coeff a (hS (N - a)) • alphaOp (N - a) := by
  by_cases h : N = (a : ℤ)
  · rw [h, sub_self, alphaOp_zero, smul_zero, smul_zero]
  congr 1
  have hM : (((N - a : ℤ) : ℤ) : ℂ) ≠ 0 := by
    have : N - (a : ℤ) ≠ 0 := sub_ne_zero.mpr h
    exact_mod_cast this
  have h1 := coeff_hS_mul (N - a) a
  have h2 : chat a N = (N : ℂ) / ((N : ℂ) - a) *
      PowerSeries.coeff a (Est (((N - a : ℤ) : ℤ) : ℂ)) := by
    rw [chat, coeff_Est, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have hl : lvl β = a := (mem_level_iff a β).mp hβ
    rw [thc, hl, if_neg h, ← wpow_linExp]
    push_cast
    ring
  refine mul_left_cancel₀ hM ?_
  rw [h1, h2]
  push_cast at hM ⊢
  field_simp
  ring

theorem chat_smul_apply (a : ℕ) (N : ℤ) (v : Fock) :
    chat a N • alphaOp (N - a) v = PowerSeries.coeff a (hS (N - a)) • alphaOp (N - a) v := by
  rw [← LinearMap.smul_apply, chat_smul, LinearMap.smul_apply]

theorem mem_level_le_iff (n : ℕ) (β : ℕ+ →₀ ℕ) :
    β ∈ (finite_level_le n).toFinset ↔ lvl β ≤ n := by
  rw [Set.Finite.mem_toFinset]
  rfl

section Spec

variable {U : Fock →ₗ[ℂ] HH} (hU : IsDiffeoU U)

include hU

/-- `U u^α` has level `|α|`. -/
theorem U_mem_level (α : ℕ+ →₀ ℕ) : U (monomial α 1) ∈ hhLevel (lvl α) := by
  rw [hhLevel, Module.Basis.mem_span_image]
  intro p hp
  have hp' : hhBasis.repr (U (monomial α 1)) p ≠ 0 := Finsupp.mem_support_iff.mp hp
  by_contra hne
  apply hp'
  have h := Ucf_graded hU α p.1 p.2 hne
  rwa [Ucf_apply, coeff_cfW] at h

theorem Ucf_form_zero (α β : ℕ+ →₀ ℕ) (j : ℕ) (h : lvl β + j ≠ lvl α) :
    fockForm (Ucf U β (monomial α 1)) (gaussF 0 j) = 0 := by
  unfold fockForm
  refine Finset.sum_eq_zero fun γ hγ => ?_
  have h1 : lvl γ = j := gaussF_mem_level 0 j (mem_support_iff.mp hγ)
  rw [Ucf_graded hU α β γ (by omega), map_zero, zero_mul, zero_mul]

omit hU in
/-- `P(c, ·) = ∑_β c^β [W^β]P` for `P` of level `n`. -/
theorem evAt_eq (c : ℕ+ → ℂ) (n : ℕ) (y : HH) (hy : y ∈ hhLevel n) :
    evAt c y = ∑ β ∈ (finite_level_le n).toFinset, (β.prod fun m e => c m ^ e) • cfW β y := by
  classical
  rw [hhLevel] at hy
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨p, hp, rfl⟩
    have hp1 : lvl p.1 + lvl p.2 = n := hp
    rw [hhBasis_apply, evAt_tmul, aeval_monomial, Finset.sum_eq_single p.1]
    · rw [cfW_tmul, coeff_monomial, if_pos rfl, one_smul]
      simp
    · intro β _ hne
      rw [cfW_tmul, coeff_monomial, if_neg (Ne.symm hne), zero_smul, smul_zero]
    · intro hnot
      exfalso
      apply hnot
      rw [mem_level_le_iff]
      omega
  · simp
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun β _ => by rw [map_add, smul_add]
  · intro a x _ hx
    rw [map_smul, hx, Finset.smul_sum]
    exact Finset.sum_congr rfl fun β _ => by rw [map_smul, smul_comm]

omit hU in
theorem UdagF_mem_level (n : ℕ) : UdagF U n ∈ levelSub n := by
  unfold UdagF
  refine Submodule.sum_mem _ fun α hα => Submodule.smul_mem _ _ ?_
  have h := monomial_mem_levelSub α
  rwa [(mem_level_iff n α).mp hα] at h

/-- `(U(W_*)^† F_2)_n = ∑_d T_d (F_2)_{n-d}` (sphere/paper.tex l.1102–1105: the adjoint taken
coefficientwise in `W` and specialized at the real point `W_*`). -/
theorem UdagF_eq (n : ℕ) :
    UdagF U n = ∑ d ∈ range (n + 1), Tst U d (gaussF 0 (n - d)) := by
  classical
  ext α
  refine mul_right_cancel₀ (fockNorm_ne_zero α) ?_
  rw [← fockForm_monomial_left, ← fockForm_monomial_left, fockForm_sum_right]
  have hR : ∀ d ∈ range (n + 1), fockForm (monomial α 1) (Tst U d (gaussF 0 (n - d))) =
      ∑ β ∈ (finite_level d).toFinset,
        wpow β * fockForm (Ucf U β (monomial α 1)) (gaussF 0 (n - d)) := by
    intro d _
    rw [Tst_apply, fockForm_sum_right]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [fockForm_smul_right, Udg_adj' hU]
  rw [Finset.sum_congr rfl hR]
  by_cases hα : lvl α = n
  · have hmem : α ∈ (finite_level n).toFinset := (mem_level_iff n α).mpr hα
    rw [fockForm_monomial_left, coeff_UdagF U n α hmem, div_mul_cancel₀ _ (fockNorm_ne_zero α),
      evAt_eq Wstar n _ (hα ▸ U_mem_level hU α), fockForm_sum_left,
      Finset.sum_comm' (s' := fun β : ℕ+ →₀ ℕ => {lvl β})
        (t' := (finite_level_le n).toFinset)]
    · refine Finset.sum_congr rfl fun β hβ => ?_
      have hβn : lvl β ≤ n := (mem_level_le_iff n β).mp hβ
      rw [Finset.sum_singleton, fockForm_smul_left, Ucf_apply, fockForm_sum_right,
        Finset.sum_eq_single (n - lvl β)]
      · rw [← Ucf_apply]
        congr 1
        exact conj_Wstar_prod β
      · intro j _ hj
        rw [← Ucf_apply]
        exact Ucf_form_zero hU α β j (by omega)
      · intro hnot
        exact absurd (Finset.mem_range.mpr (by omega)) hnot
    · intro d β
      simp only [Finset.mem_range, mem_level_iff, mem_level_le_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2.symm, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by omega, h1.symm⟩
  · rw [fockForm_monomial_left, coeff_eq_zero_of_level (UdagF_mem_level n) α hα, zero_mul]
    symm
    refine Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun β hβ => ?_
    have hl : lvl β = d := (mem_level_iff d β).mp hβ
    have hd' := Finset.mem_range.mp hd
    rw [Ucf_form_zero hU α β (n - d) (by omega), mul_zero]

theorem Yz_eq (j : ℤ) (D : ℕ) (hD : j ≤ D) :
    Yz U j = ∑ b ∈ range (D + 1), Tst U b (lp F2s (j - b)) := by
  by_cases hj : 0 ≤ j
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = n := ⟨j.toNat, by omega⟩
    have hnD : n ≤ D := by omega
    rw [Yz, if_pos hj, Int.toNat_natCast, UdagF_eq hU n,
      ← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : n + 1 ≤ D + 1))
        (fun b _ hb => by
          have hb' : ¬ b < n + 1 := fun h => hb (Finset.mem_range.mpr h)
          rw [lp_neg_index _ _ (by omega), map_zero])]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hb' := Finset.mem_range.mp hb
    rw [gaussF_eq_lp]
    congr 2
    omega
  · rw [Yz, if_neg hj]
    symm
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [lp_neg_index _ _ (by omega), map_zero]

variable (hF : Cited_FeiginFuchsOperators)

include hF

/-- `U(W_*)^† α_N = (f' α(f))_N(W_*) U(W_*)^†` on the part raising the level by `d`. -/
theorem Tst_alphaOp (d : ℕ) (N : ℤ) (v : Fock) :
    Tst U d (alphaOp N v) = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal d,
      chat ab.1 N • alphaOp (N - ab.1) (Tst U ab.2 v) := by
  classical
  have h1 : ∀ β : ℕ+ →₀ ℕ, wpow β • Udg U β (alphaOp N v) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal β, (wpow p.1 * thc p.1 N) •
        alphaOp (N - (lvl p.1 : ℤ)) (wpow p.2 • Udg U p.2 v) := by
    intro β
    have h := LinearMap.congr_fun (Udg_alphaOp hU hF N β) v
    rw [LinearMap.comp_apply, LinearMap.sum_apply] at h
    rw [h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    rw [LinearMap.comp_apply, thF, LinearMap.smul_apply, map_smul, smul_smul, smul_smul, ← hp,
      wpow_add]
    congr 1
    ring
  rw [Tst_apply, Finset.sum_congr rfl fun β _ => h1 β,
    sum_level_antidiagonal d fun p => (wpow p.1 * thc p.1 N) •
      alphaOp (N - (lvl p.1 : ℤ)) (wpow p.2 • Udg U p.2 v)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [chat, Finset.sum_smul, Tst_apply, map_sum]
  refine Finset.sum_congr rfl fun β1 hβ1 => ?_
  dsimp only
  rw [(mem_level_iff _ _).mp hβ1, Finset.smul_sum]

/-- `(U(W_*)^† α_N F_2)_{i-N}` in two ways. -/
theorem lemmaA (N i : ℤ) (D : ℕ) (hi : i ≤ D) :
    ∑ d ∈ range (D + 1), Tst U d (alphaOp N (lp F2s (i - d))) =
      ∑ a ∈ range (D + 1), chat a N • alphaOp (N - a) (Yz U (i - a)) := by
  set g : ℕ → ℕ → Fock := fun a b =>
    chat a N • alphaOp (N - a) (Tst U b (lp F2s (i - ((a + b : ℕ) : ℤ)))) with hg
  have hL : ∀ d ∈ range (D + 1), Tst U d (alphaOp N (lp F2s (i - d))) =
      ∑ a ∈ range (d + 1), g a (d - a) := by
    intro d _
    rw [Tst_alphaOp hU hF, ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ g d]
    refine Finset.sum_congr rfl fun ab hab => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
    rw [hg]
    simp only
    rw [hab]
  have hR : ∀ a ∈ range (D + 1), chat a N • alphaOp (N - a) (Yz U (i - a)) =
      ∑ b ∈ range (D + 1 - a), g a b := by
    intro a _
    rw [Yz_eq hU (i - a) D (by omega), map_sum, Finset.smul_sum,
      ← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : D + 1 - a ≤ D + 1))
        (fun b _ hb => by
          have hb' : ¬ b < D + 1 - a := fun h => hb (Finset.mem_range.mpr h)
          rw [lp_neg_index _ _ (by omega), map_zero, map_zero, smul_zero])]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hg]
    simp only
    congr 4
    push_cast
    ring
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  exact Finset.sum_range_diag_flip (D + 1) g

/-- `∮ x^{k-1}√(x(x-1)) f'(x) α(f(x)) dx · U(W_*)^† F_2 = 0` with `f = f(x;W_*)`
(sphere/paper.tex l.1134–1136), at level `n`: the coefficient of `α_M` is the residue of
`x^{k-1}√(x(x-1)) f' f^{-M-1}`. -/
theorem rel0 (k : ℕ) (hk : 1 ≤ k) (n : ℤ) (L : ℕ) (hkL : k ≤ L) (hn : n ≤ L) :
    ∑ M ∈ Icc (-(L : ℤ)) k, PowerSeries.coeff ((k : ℤ) - M).toNat (sOneC * hS M) •
      alphaOp M (Yz U (n + M)) = 0 := by
  classical
  set D := L + k with hD
  set H : ℤ → ℕ → Fock := fun N a =>
    (sk k N * PowerSeries.coeff a (hS (N - a))) • alphaOp (N - a) (Yz U (n + N - a)) with hH
  have h0 : ∑ d ∈ range (D + 1), Tst U d (∑ N ∈ Icc (-(L : ℤ)) k,
      sk k N • alphaOp N (lp F2s (n - d + N))) = 0 :=
    Finset.sum_eq_zero fun d _ => by
      rw [input_residue k hk (n - d) L (by omega), map_zero]
  have h1 : ∑ d ∈ range (D + 1), Tst U d (∑ N ∈ Icc (-(L : ℤ)) k,
      sk k N • alphaOp N (lp F2s (n - d + N))) =
      ∑ N ∈ Icc (-(L : ℤ)) k, ∑ a ∈ range (D + 1), H N a := by
    simp only [map_sum, map_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun N hN => ?_
    have hN' := Finset.mem_Icc.mp hN
    have e : ∀ d : ℕ, n - (d : ℤ) + N = n + N - d := fun d => by ring
    simp only [e]
    rw [← Finset.smul_sum, lemmaA hU hF N (n + N) D (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [chat_smul_apply, hH]
    simp only [smul_smul]
  have h2 : ∀ M ∈ Icc (-(L : ℤ)) k, PowerSeries.coeff ((k : ℤ) - M).toNat (sOneC * hS M) •
      alphaOp M (Yz U (n + M)) = ∑ a ∈ range (((k : ℤ) - M).toNat + 1), H (M + a) a := by
    intro M hM
    have hM' := Finset.mem_Icc.mp hM
    rw [mul_comm, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a (hS M) * PowerSeries.coeff b sOneC), Finset.sum_smul]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.mp ha
    rw [hH]
    simp only
    have e1 : M + (a : ℤ) - a = M := by ring
    have e2 : n + (M + (a : ℤ)) - a = n + M := by ring
    have e3 : ((k : ℤ) - (M + a)).toNat = ((k : ℤ) - M).toNat - a := by omega
    rw [e1, e2, sk, e3, mul_comm]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm' (s' := fun a : ℕ => Icc (-(L : ℤ)) ((k : ℤ) - a))
    (t' := range (D + 1))]
  · rw [← h0, h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.mp ha
    have hsub : ∑ N ∈ Icc (-(L : ℤ) + a) k, H N a = ∑ N ∈ Icc (-(L : ℤ)) k, H N a := by
      refine Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl) fun N hN hN' => ?_
      have h3 := Finset.mem_Icc.mp hN
      have h4 : N < -(L : ℤ) + a := by
        by_contra h5
        exact hN' (Finset.mem_Icc.mpr ⟨by omega, h3.2⟩)
      rw [hH]
      simp only
      rw [Yz, if_neg (by omega), map_zero, smul_zero]
    rw [← hsub]
    refine Finset.sum_nbij' (fun M : ℤ => M + a) (fun N : ℤ => N - a) ?_ ?_ ?_ ?_ ?_
    · intro M hM
      have := Finset.mem_Icc.mp hM
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro N hN
      have := Finset.mem_Icc.mp hN
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro M _
      ring
    · intro N _
      ring
    · intro M _
      rfl
  · intro M a
    simp only [Finset.mem_Icc, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩

/-- `∮ x(X)^{k-1}(X - 1/(16X)) α(X) dX · U(W_*)^† F_2 = 0` (sphere/paper.tex l.1136–1139), at
level `n`, with `x(X)^{k-1}(X - 1/(16X)) = ∑_m cst k m (X^m - 16^{-m}X^{-m})`. -/
theorem rel (k : ℕ) (hk : 1 ≤ k) (n : ℤ) :
    ∑ m ∈ range (k + 1), cst k m • (alphaOp m (Yz U (n + m)) -
      (1 / 16 : ℂ) ^ m • alphaOp (-(m : ℤ)) (Yz U (n - m))) = 0 := by
  classical
  set L := max k n.toNat with hLdef
  have hkL : k ≤ L := le_max_left _ _
  have hn : n ≤ (L : ℤ) := by
    have : n.toNat ≤ L := le_max_right _ _
    omega
  have h := rel0 hU hF k hk n L hkL hn
  have h1 : ∀ M ∈ Icc (-(L : ℤ)) k, PowerSeries.coeff ((k : ℤ) - M).toNat (sOneC * hS M) •
      alphaOp M (Yz U (n + M)) = ∑ m ∈ range (k + 1), cst k m •
        ((if M = (m : ℤ) then alphaOp M (Yz U (n + M)) else 0) -
          (1 / 16 : ℂ) ^ m • (if M = -(m : ℤ) then alphaOp M (Yz U (n + M)) else 0)) := by
    intro M hM
    rw [rho_eq k hk M (Finset.mem_Icc.mp hM).2, Finset.sum_smul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_smul, sub_smul, mul_smul]
    congr 2
    · split_ifs <;> simp
    · congr 1
      split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm] at h
  rw [← h]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.mp hm
  rw [← Finset.smul_sum, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_Icc.mpr ⟨by omega, by omega⟩),
    if_pos (Finset.mem_Icc.mpr ⟨by omega, by omega⟩), sub_eq_add_neg n (m : ℤ)]

end Spec

end Virasoro.Sphere
