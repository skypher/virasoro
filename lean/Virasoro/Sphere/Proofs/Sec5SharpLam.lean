import Virasoro.Sphere.CitedBPZ
import Virasoro.Sphere.Proofs.Sec5TopB
import Virasoro.Proofs.P2Sec13Limit
import Virasoro.Proofs.TwoBranchA
import Virasoro.Proofs.P2Sec13Laurent

/-!
# Theorem 5.4: the BPZ recursion at `b⋆` (sphere/paper.tex l.1651–1667)

"Hence `ℬ_m = [z^m]((1-z)^κ ₂F₁(A,B;C;z))` as an identity of rational functions of
`(b,Λ_μ,Λ₃,Λ₄)` … we specialize the identity only through degree `M`."  With `β_μ`, `β₃`, `β₄`
fixed, every quantity is a Laurent polynomial in `b` (`ℂ[b,b⁻¹]`): the block numerator
`∑ γ adj(G) γ` and the Gram determinants.  The BPZ coefficient times the three determinants is a
Laurent polynomial; it vanishes at every generic `b` (the cited equation), hence identically, hence
at `b⋆`, where the determinants up to the level `M` are nonzero.
-/

namespace Virasoro.Sphere

open Virasoro Virasoro.P2 Polynomial

section Lift

/-- A constant of `ℂ[b,b⁻¹]`. -/
noncomputable def cstL (z : ℂ) : Virasoro.P2.Lam := algebraMap ℂ[X] Virasoro.P2.Lam (C z)

theorem evLam_cst {b : ℂ} (hb : b ≠ 0) (z : ℂ) : evLam b hb (cstL z) = z := by
  rw [cstL, evLam_algebraMap, eval_C]

/-- `wt(β) = ((b²+1)² - β²)/(4b²)` over `ℂ[b,b⁻¹]`. -/
noncomputable def wtL (β : Virasoro.P2.Lam) : Virasoro.P2.Lam := ((lamX ^ 2 + 1) ^ 2 - β ^ 2) * lamXi ^ 2 * cstL (1 / 4)

theorem evLam_wtL {b : ℂ} (hb : b ≠ 0) (β : Virasoro.P2.Lam) : evLam b hb (wtL β) = wtB b (evLam b hb β) := by
  simp only [wtL, wtB, map_mul, map_sub, map_pow, map_add, map_one, evLam_lamX, evLam_lamXi,
    evLam_cst]
  field_simp

theorem gammaY_ringHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Δ Δa Δb : R) :
    ∀ w : List ℕ, f (gammaY Δ Δa Δb w) = gammaY (f Δ) (f Δa) (f Δb) w
  | [] => by simp [gammaY]
  | y :: w => by
    simp only [gammaY, map_mul, map_sub, map_add, map_natCast, gammaY_ringHom f Δ Δa Δb w]

variable (βμ β₃ β₄ : ℂ)

/-- `μ(b) = wt(β_μ)`. -/
noncomputable def μL : Virasoro.P2.Lam := wtL (cstL βμ)

/-- The external weights of the BPZ setting over `ℂ[b,b⁻¹]`. -/
noncomputable def ΔeL : Fin 4 → Virasoro.P2.Lam :=
  ![wtL (cstL βμ + lamX ^ 2), hLam 2 1, wtL (cstL β₃), wtL (cstL β₄)]

theorem evLam_ΔeL {b : ℂ} (hb : b ≠ 0) (i : Fin 4) :
    evLam b hb (ΔeL βμ β₃ β₄ i) = bpzWeights b βμ β₃ β₄ i := by
  fin_cases i <;>
    simp [ΔeL, bpzWeights, evLam_wtL hb, evLam_cst hb, evLam_lamX hb, evLam_hLam hb]

/-- The numerator `∑ γ_Y(μ;Δ₄,Δ₃) adj(G_n(c,μ)) γ_Z(μ;Δ₁,Δ₂)` of `ℬ_n(c(b),μ(b),Δ_i(b))`. -/
noncomputable def BnL (n : ℕ) : Virasoro.P2.Lam :=
  ∑ Y : Nat.Partition n, ∑ Z : Nat.Partition n,
    gammaY (μL βμ) (ΔeL βμ β₃ β₄ 3) (ΔeL βμ β₃ β₄ 2) Y.word * (gram cLam (μL βμ) n).adjugate Y Z *
      gammaY (μL βμ) (ΔeL βμ β₃ β₄ 0) (ΔeL βμ β₃ β₄ 1) Z.word

/-- `det G_n(c(b),μ(b))`. -/
noncomputable def DL (n : ℕ) : Virasoro.P2.Lam := (gram cLam (μL βμ) n).det

theorem evLam_DL {b : ℂ} (hb : b ≠ 0) (n : ℕ) :
    evLam b hb (DL βμ n) = (gram (kacC b) (wtB b βμ) n).det := by
  rw [DL, RingHom.map_det, RingHom.mapMatrix_apply, ← gram_map, evLam_cLam hb, μL, evLam_wtL hb,
    evLam_cst hb]

/-- `ℬ_n = numerator / det` at a weight where `G_n` is invertible. -/
theorem blockAt_eq {b : ℂ} (hb : b ≠ 0) (n : ℕ) (hdet : (gram (kacC b) (wtB b βμ) n).det ≠ 0) :
    blockAt (kacC b) (wtB b βμ) (bpzWeights b βμ β₃ β₄) n =
      evLam b hb (BnL βμ β₃ β₄ n) / evLam b hb (DL βμ n) := by
  rw [blockAt, evLam_DL βμ hb]
  change evalAt _ _ = _
  rw [evalAt_Bsph _ hdet, BnL, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun Z _ => ?_
  have hG : (gram cLam (μL βμ) n).map (evLam b hb) = gram (kacC b) (wtB b βμ) n := by
    rw [← gram_map, evLam_cLam hb, μL, evLam_wtL hb, evLam_cst hb]
  have hadj := congrFun (congrFun (RingHom.map_adjugate (evLam b hb) (gram cLam (μL βμ) n)) Y) Z
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.mapMatrix_apply, hG] at hadj
  rw [map_mul, map_mul, hadj, gammaY_ringHom, gammaY_ringHom, μL, evLam_wtL hb, evLam_cst hb,
    evLam_ΔeL βμ β₃ β₄ hb, evLam_ΔeL βμ β₃ β₄ hb, evLam_ΔeL βμ β₃ β₄ hb, evLam_ΔeL βμ β₃ β₄ hb,
    Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  field_simp

end Lift

section Recursion

variable (βμ β₃ β₄ : ℂ)

/-- `s = μ - Δ₁ - Δ₂` and `D = Δ₁+Δ₂+Δ₃-Δ₄` over `ℂ[b,b⁻¹]`. -/
noncomputable def sL : Virasoro.P2.Lam := μL βμ - ΔeL βμ β₃ β₄ 0 - ΔeL βμ β₃ β₄ 1

noncomputable def DdL : Virasoro.P2.Lam :=
  ΔeL βμ β₃ β₄ 0 + ΔeL βμ β₃ β₄ 1 + ΔeL βμ β₃ β₄ 2 - ΔeL βμ β₃ β₄ 3

noncomputable def P0L (x : Virasoro.P2.Lam) : Virasoro.P2.Lam :=
  lamXi ^ 2 * x * (x - 1) - x + ΔeL βμ β₃ β₄ 0

noncomputable def P1L (x : Virasoro.P2.Lam) : Virasoro.P2.Lam :=
  -2 * lamXi ^ 2 * x * (x - 1) + 3 * x + DdL βμ β₃ β₄ - 2 * ΔeL βμ β₃ β₄ 0

noncomputable def P2L (x : Virasoro.P2.Lam) : Virasoro.P2.Lam :=
  lamXi ^ 2 * x * (x - 1) - 2 * x + ΔeL βμ β₃ β₄ 0 + ΔeL βμ β₃ β₄ 2 - DdL βμ β₃ β₄

/-- The BPZ coefficient multiplied by the three Gram determinants. -/
noncomputable def RL (n : ℕ) : Virasoro.P2.Lam :=
  P0L βμ β₃ β₄ (sL βμ β₃ β₄ + n) * BnL βμ β₃ β₄ n * DL βμ (n - 1) * DL βμ (n - 2) +
    (if 1 ≤ n then P1L βμ β₃ β₄ (sL βμ β₃ β₄ + n - 1) * BnL βμ β₃ β₄ (n - 1) * DL βμ n *
      DL βμ (n - 2) else 0) +
    (if 2 ≤ n then P2L βμ β₃ β₄ (sL βμ β₃ β₄ + n - 2) * BnL βμ β₃ β₄ (n - 2) * DL βμ n *
      DL βμ (n - 1) else 0)

theorem clear3 (p0 p1 p2 B0 B1 B2 D0 D1 D2 : ℂ) (h0 : D0 ≠ 0) (h1 : D1 ≠ 0) (h2 : D2 ≠ 0)
    (c1 c2 : Prop) [Decidable c1] [Decidable c2] :
    p0 * B0 * D1 * D2 + (if c1 then p1 * B1 * D0 * D2 else 0) +
        (if c2 then p2 * B2 * D0 * D1 else 0) =
      D0 * D1 * D2 * (p0 * (B0 / D0) + (if c1 then p1 * (B1 / D1) else 0) +
        (if c2 then p2 * (B2 / D2) else 0)) := by
  split_ifs <;> field_simp <;> ring

theorem evLam_RL {b : ℂ} (hb : b ≠ 0) (n : ℕ) (h0 : (gram (kacC b) (wtB b βμ) n).det ≠ 0)
    (h1 : (gram (kacC b) (wtB b βμ) (n - 1)).det ≠ 0)
    (h2 : (gram (kacC b) (wtB b βμ) (n - 2)).det ≠ 0) :
    evLam b hb (RL βμ β₃ β₄ n) = (gram (kacC b) (wtB b βμ) n).det *
      (gram (kacC b) (wtB b βμ) (n - 1)).det * (gram (kacC b) (wtB b βμ) (n - 2)).det *
        bpzCoeff b βμ β₃ β₄ n := by
  have e0 := blockAt_eq βμ β₃ β₄ hb n h0
  have e1 := blockAt_eq βμ β₃ β₄ hb (n - 1) h1
  have e2 := blockAt_eq βμ β₃ β₄ hb (n - 2) h2
  rw [evLam_DL βμ hb] at e0 e1 e2
  have hs : evLam b hb (sL βμ β₃ β₄) = wtB b βμ - bpzWeights b βμ β₃ β₄ 0 -
      bpzWeights b βμ β₃ β₄ 1 := by
    rw [sL, map_sub, map_sub, μL, evLam_wtL hb, evLam_cst hb, evLam_ΔeL βμ β₃ β₄ hb,
      evLam_ΔeL βμ β₃ β₄ hb]
  have hD : evLam b hb (DdL βμ β₃ β₄) = bpzWeights b βμ β₃ β₄ 0 + bpzWeights b βμ β₃ β₄ 1 +
      bpzWeights b βμ β₃ β₄ 2 - bpzWeights b βμ β₃ β₄ 3 := by
    simp only [DdL, map_sub, map_add, evLam_ΔeL βμ β₃ β₄ hb]
  have hP0 : ∀ x, evLam b hb (P0L βμ β₃ β₄ x) =
      bpzP0 b (bpzWeights b βμ β₃ β₄ 0) (evLam b hb x) := by
    intro x
    simp only [P0L, bpzP0, map_add, map_sub, map_mul, map_pow, map_one, evLam_lamXi hb,
      evLam_ΔeL βμ β₃ β₄ hb, inv_pow]
  have hP1 : ∀ x, evLam b hb (P1L βμ β₃ β₄ x) =
      bpzP1 b (bpzWeights b βμ β₃ β₄ 0) (bpzWeights b βμ β₃ β₄ 0 + bpzWeights b βμ β₃ β₄ 1 +
        bpzWeights b βμ β₃ β₄ 2 - bpzWeights b βμ β₃ β₄ 3) (evLam b hb x) := by
    intro x
    simp only [P1L, bpzP1, map_add, map_sub, map_mul, map_pow, map_one, map_neg, map_ofNat,
      evLam_lamXi hb, evLam_ΔeL βμ β₃ β₄ hb, hD, inv_pow]
  have hP2 : ∀ x, evLam b hb (P2L βμ β₃ β₄ x) =
      bpzP2 b (bpzWeights b βμ β₃ β₄ 0) (bpzWeights b βμ β₃ β₄ 2)
        (bpzWeights b βμ β₃ β₄ 0 + bpzWeights b βμ β₃ β₄ 1 +
        bpzWeights b βμ β₃ β₄ 2 - bpzWeights b βμ β₃ β₄ 3) (evLam b hb x) := by
    intro x
    simp only [P2L, bpzP2, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat,
      evLam_lamXi hb, evLam_ΔeL βμ β₃ β₄ hb, hD, inv_pow]
  have hx0 : evLam b hb (sL βμ β₃ β₄ + n) = wtB b βμ - bpzWeights b βμ β₃ β₄ 0 -
      bpzWeights b βμ β₃ β₄ 1 + n := by rw [map_add, map_natCast, hs]
  have hx1 : evLam b hb (sL βμ β₃ β₄ + n - 1) = wtB b βμ - bpzWeights b βμ β₃ β₄ 0 -
      bpzWeights b βμ β₃ β₄ 1 + n - 1 := by rw [map_sub, map_add, map_natCast, map_one, hs]
  have hx2 : evLam b hb (sL βμ β₃ β₄ + n - 2) = wtB b βμ - bpzWeights b βμ β₃ β₄ 0 -
      bpzWeights b βμ β₃ β₄ 1 + n - 2 := by rw [map_sub, map_add, map_natCast, map_ofNat, hs]
  simp only [RL, bpzCoeff, map_add, map_mul, apply_ite (evLam b hb), map_zero, hP0, hP1, hP2,
    hx0, hx1, hx2, evLam_DL βμ hb, e0, e1, e2]
  exact clear3 _ _ _ _ _ _ _ _ _ h0 h1 h2 _ _

/-- `h_{r,s}(b) = wt(r b² + s)`. -/
theorem kacH_eq_wtB {b : ℂ} (hb : b ≠ 0) (r s : ℤ) : kacH r s b = wtB b (r * b ^ 2 + s) := by
  unfold kacH wtB
  field_simp

/-- `det G_m(c(b),μ(b)) ≢ 0` as a Laurent polynomial: at a large real `b₀`, `μ(b₀)` is no Kac
weight (Kac determinant). -/
theorem DL_ne_zero (hK : Cited_KacDeterminant) (m : ℕ) : DL βμ m ≠ 0 := by
  set t : ℝ := ‖βμ‖ + 2 with ht
  have ht2 : (2 : ℝ) ≤ t := by rw [ht]; linarith [norm_nonneg βμ]
  set b₀ : ℂ := (t : ℂ) with hb₀
  have hb0 : b₀ ≠ 0 := by
    rw [hb₀]; exact_mod_cast (show t ≠ 0 by linarith)
  intro h0
  have h1 := congrArg (evLam b₀ hb0) h0
  rw [evLam_DL βμ hb0, map_zero] at h1
  refine gram_det_ne_of_labels hK hb0 (fun g hg heq => ?_) h1
  obtain ⟨hgr, -⟩ := Finset.mem_product.1 (Finset.mem_filter.1 hg).1
  have hr1 : (1 : ℝ) ≤ g.1 := by exact_mod_cast (Finset.mem_Icc.1 hgr).1
  have hs0 : (0 : ℝ) ≤ g.2 := by positivity
  rw [kacHL, kacH_eq_wtB hb0] at heq
  unfold wtB at heq
  have h4 : (4 * b₀ ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hb0)
  rw [div_left_inj' h4, sub_right_inj] at heq
  have hreal : ((((g.1 : ℤ) : ℂ) * b₀ ^ 2 + ((g.2 : ℤ) : ℂ)) ^ 2) =
      (((g.1 * t ^ 2 + g.2) ^ 2 : ℝ) : ℂ) := by
    rw [hb₀]; push_cast; ring
  rw [hreal] at heq
  have hn := congrArg (fun z : ℂ => ‖z‖) heq
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
  have hbig : ‖βμ‖ ^ 2 < (g.1 * t ^ 2 + g.2) ^ 2 := by
    have h5 : ‖βμ‖ < g.1 * t ^ 2 + g.2 := by nlinarith [norm_nonneg βμ]
    nlinarith [norm_nonneg βμ]
  linarith

/-- A nonzero Laurent polynomial has finitely many zeros in `ℂ^×`. -/
theorem lam_zeros_finite' {a : Virasoro.P2.Lam} (ha : a ≠ 0) :
    {z : ℂ | ∃ hz : z ≠ 0, evLam z hz a = 0}.Finite := by
  obtain ⟨n, q, hq⟩ := IsLocalization.Away.surj (X : ℂ[X]) a
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [map_zero] at hq
    have hu : IsUnit (algebraMap ℂ[X] Virasoro.P2.Lam X ^ n) :=
      (IsUnit.pow n ⟨⟨lamX, lamXi, lamX_mul_lamXi, by rw [mul_comm]; exact lamX_mul_lamXi⟩, rfl⟩)
    exact ha ((hu.mul_left_eq_zero).1 hq)
  refine (Polynomial.finite_setOf_isRoot hq0).subset fun z ⟨hz, h0⟩ => ?_
  have h1 := congrArg (evLam z hz) hq
  rw [map_mul, h0, zero_mul, evLam_algebraMap] at h1
  exact h1.symm

/-- The generic set: `b ≠ 0`, `b² ∉ ℚ`, and every `G_m(c(b),μ(b))` invertible, is infinite. -/
theorem generic_block_infinite (hK : Cited_KacDeterminant) :
    {b : ℂ | b ≠ 0 ∧ (∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) ∧
      ∀ m : ℕ, (gram (kacC b) (wtB b βμ) m).det ≠ 0}.Infinite := by
  intro hfin
  apply not_countable_complex
  have hq : ∀ q : ℚ, {z : ℂ | z ^ 2 = (q : ℂ)}.Countable := by
    intro q
    have hne : (X ^ 2 - C (q : ℂ) : ℂ[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) _
    refine ((Polynomial.finite_setOf_isRoot hne).subset ?_).countable
    intro z hz
    show (X ^ 2 - C (q : ℂ) : ℂ[X]).IsRoot z
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C]
    rw [Set.mem_setOf_eq] at hz
    rw [hz, sub_self]
  have hm : ∀ m : ℕ, {z : ℂ | ∃ hz : z ≠ 0, evLam z hz (DL βμ m) = 0}.Countable :=
    fun m => (lam_zeros_finite' (DL_ne_zero βμ hK m)).countable
  have hcov : (Set.univ : Set ℂ) ⊆
      {b : ℂ | b ≠ 0 ∧ (∀ q : ℚ, b ^ 2 ≠ (q : ℂ)) ∧
        ∀ m : ℕ, (gram (kacC b) (wtB b βμ) m).det ≠ 0} ∪
        (({0} ∪ ⋃ q : ℚ, {z : ℂ | z ^ 2 = (q : ℂ)}) ∪
          ⋃ m : ℕ, {z : ℂ | ∃ hz : z ≠ 0, evLam z hz (DL βμ m) = 0}) := by
    intro z _
    by_cases h0 : z = 0
    · exact Or.inr (Or.inl (Or.inl h0))
    by_cases h1 : ∃ q : ℚ, z ^ 2 = (q : ℂ)
    · obtain ⟨q, hq'⟩ := h1
      exact Or.inr (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨q, hq'⟩)))
    by_cases h2 : ∃ m : ℕ, (gram (kacC z) (wtB z βμ) m).det = 0
    · obtain ⟨m, hm'⟩ := h2
      refine Or.inr (Or.inr (Set.mem_iUnion.2 ⟨m, h0, ?_⟩))
      rw [evLam_DL βμ h0]; exact hm'
    · push_neg at h1 h2
      exact Or.inl ⟨h0, fun q hq' => h1 q hq', h2⟩
  refine Set.Countable.mono hcov (hfin.countable.union ?_)
  exact ((Set.countable_singleton 0).union (Set.countable_iUnion hq)).union
    (Set.countable_iUnion hm)

/-- The BPZ coefficient vanishes at every `b ≠ 0` where `G_m(c(b),μ(b))`, `m ≤ n`, is
invertible (l.1663–1667). -/
theorem bpz_at (hBPZ : Cited_BPZEquation) (hK : Cited_KacDeterminant) {b : ℂ} (hb : b ≠ 0)
    (n : ℕ) (hdet : ∀ m ≤ n, (gram (kacC b) (wtB b βμ) m).det ≠ 0) :
    bpzCoeff b βμ β₃ β₄ n = 0 := by
  have hR : RL βμ β₃ β₄ n = 0 := by
    refine lam_eq_zero_of_infinite (generic_block_infinite βμ hK) fun b' hb' hG => ?_
    rw [evLam_RL βμ β₃ β₄ hb' n (hG.2.2 n) (hG.2.2 (n - 1)) (hG.2.2 (n - 2)),
      hBPZ b' βμ β₃ β₄ hb' hG.2.1 hG.2.2 n, mul_zero]
  have h := congrArg (evLam b hb) hR
  rw [evLam_RL βμ β₃ β₄ hb n (hdet n le_rfl) (hdet (n - 1) (by omega)) (hdet (n - 2) (by omega)),
    map_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero (mul_ne_zero (hdet n le_rfl)
    (hdet (n - 1) (by omega))) (hdet (n - 2) (by omega)))

end Recursion

end Virasoro.Sphere
