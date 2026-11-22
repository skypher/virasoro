import Virasoro.Proofs.Shapovalov
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Proposition 6.8(ii): the Gram entries at partitions `(1^a, μ)` (paper.tex l.1306–1322)

For `λ = (1^a, μ)` and `λ' = (1^{a'}, μ')`,
`G_{λ,λ'} = ⟨Δ| L_1^a (L_μ L_{−μ'}) L_{−1}^{a'} |Δ⟩`.  The paper applies
`L_1^a X = ∑_p C(a,p) (ad(L_1)^p X) L_1^{a−p}` (`H13C.pow_mul_eq_sum_ad`, a ring identity) and
`L_1^k L_{−1}^b|Δ⟩ = (b!/q!) ∏_{s=q}^{b−1}(2Δ+s) L_{−1}^q|Δ⟩`, `q = b − k`
(`H13C.L1_pow_Lm1_pow`), which give the sum over `p` of `H13C.gramWord_ones`.
-/

namespace Virasoro.H13C

/-! ### The ring identity `x^a X = ∑_p C(a,p) (ad(x)^p X) x^{a−p}` (l.1316) -/

section Ring

variable {A : Type*} [Ring A]

/-- `ad(x)^p (X)`, with `ad(x)(Z) = xZ − Zx`. -/
def adp (x : A) (p : ℕ) (X : A) : A := (fun Z => x * Z - Z * x)^[p] X

theorem adp_zero (x X : A) : adp x 0 X = X := rfl

theorem adp_succ (x : A) (p : ℕ) (X : A) : adp x (p + 1) X = x * adp x p X - adp x p X * x :=
  Function.iterate_succ_apply' _ _ _

private theorem mulLeft_pow_apply (x : A) (a : ℕ) (X : A) :
    (LinearMap.mulLeft ℤ x ^ a) X = x ^ a * X := by
  induction a generalizing X with
  | zero => simp
  | succ a ih => rw [pow_succ, Module.End.mul_apply, LinearMap.mulLeft_apply, ih, pow_succ, mul_assoc]

private theorem mulRight_pow_apply (x : A) (a : ℕ) (X : A) :
    (LinearMap.mulRight ℤ x ^ a) X = X * x ^ a := by
  induction a generalizing X with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, Module.End.mul_apply, LinearMap.mulRight_apply, ih, pow_succ', mul_assoc]

private theorem ad_pow_apply (x : A) (p : ℕ) (X : A) :
    ((LinearMap.mulLeft ℤ x - LinearMap.mulRight ℤ x) ^ p) X = adp x p X := by
  induction p with
  | zero => simp [adp]
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply, ih, adp_succ, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]

/-- `x^a X = ∑_p C(a,p) (ad(x)^p X) x^{a−p}` (paper.tex l.1316): left multiplication by `x` is
`ad(x)` plus right multiplication by `x`, and these two commute. -/
theorem pow_mul_eq_sum_ad (x X : A) (a : ℕ) :
    x ^ a * X = ∑ p ∈ Finset.range (a + 1), a.choose p • (adp x p X * x ^ (a - p)) := by
  have hc : Commute (LinearMap.mulLeft ℤ x - LinearMap.mulRight ℤ x) (LinearMap.mulRight ℤ x) :=
    (LinearMap.commute_mulLeft_right x x).sub_left (Commute.refl _)
  have h := hc.add_pow a
  rw [sub_add_cancel] at h
  have h2 := congrArg (fun f : Module.End ℤ A => f X) h
  simp only [LinearMap.sum_apply] at h2
  rw [mulLeft_pow_apply] at h2
  rw [h2]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [(hc.pow_pow p (a - p)).eq, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.natCast_apply, map_nsmul, map_nsmul, mulRight_pow_apply, ad_pow_apply]

end Ring

/-! ### `L_1^k L_{−1}^b |Δ⟩` (l.1317–1318) -/

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

open Verma

/-- `L_{−1}^b |Δ⟩`. -/
noncomputable def vb (c h : R) (b : ℕ) : Verma R c h := VirEnv.L c (-1) ^ b • (hw : Verma R c h)

theorem vb_succ (b : ℕ) : vb c h (b + 1) = L (-1) (vb c h b) := by
  rw [vb, pow_succ', mul_smul]
  rfl

theorem L0_vb (b : ℕ) : L 0 (vb c h b) = (h + (b : R)) • vb c h b := by
  induction b with
  | zero =>
    rw [vb, pow_zero, one_smul, L_hw_zero]
    simp
  | succ b ih =>
    rw [vb_succ, L_L, ih, if_neg (by decide), add_zero, map_smul]
    have e : L (0 + -1) (vb c h b) = L (-1) (vb c h b) := rfl
    rw [e]
    push_cast
    module

theorem L1_vb_zero : L 1 (vb c h 0) = 0 := by
  rw [vb, pow_zero, one_smul]
  exact L_hw_pos one_pos

theorem L1_vb_succ (b : ℕ) :
    L 1 (vb c h (b + 1)) = (((b : R) + 1) * (2 * h + (b : R))) • vb c h b := by
  induction b with
  | zero =>
    rw [vb_succ, L_L, L1_vb_zero, map_zero, zero_add, if_pos (by decide), centralTerm_one]
    have e : L (1 + -1) (vb c h 0) = L 0 (vb c h 0) := rfl
    rw [e, L0_vb]
    push_cast
    module
  | succ b ih =>
    rw [vb_succ, L_L, ih, if_pos (by decide), centralTerm_one, map_smul, ← vb_succ]
    have e : L (1 + -1) (vb c h (b + 1)) = L 0 (vb c h (b + 1)) := rfl
    rw [e, L0_vb]
    push_cast
    module

/-- `L_1^k L_{−1}^b|Δ⟩ = (b!/q!) ∏_{s=q}^{b−1}(2Δ+s) L_{−1}^q|Δ⟩`, `q = b − k`
(paper.tex l.1317–1318); `b!/q!` is `b(b−1)⋯(b−k+1)`, which vanishes for `k > b`. -/
theorem L1_pow_Lm1_pow (k b : ℕ) :
    VirEnv.L c 1 ^ k • vb c h b =
      ((b.descFactorial k : R) * ∏ s ∈ Finset.Ico (b - k) b, (2 * h + (s : R))) • vb c h (b - k) := by
  induction k generalizing b with
  | zero =>
    rw [pow_zero, one_smul, Nat.descFactorial_zero, Nat.sub_zero, Finset.Ico_self,
      Finset.prod_empty, Nat.cast_one, mul_one]
    exact (one_smul R (vb c h b)).symm
  | succ k ih =>
    rw [pow_succ, mul_smul]
    cases b with
    | zero =>
      have e : VirEnv.L c 1 • vb c h 0 = 0 := L1_vb_zero
      rw [e, smul_zero, Nat.zero_descFactorial_succ, Nat.cast_zero, zero_mul]
      exact (zero_smul R (vb c h (0 - (k + 1)))).symm
    | succ b =>
      have e : VirEnv.L c 1 • vb c h (b + 1) = L 1 (vb c h (b + 1)) := rfl
      rw [e, L1_vb_succ, smul_comm, ih, Nat.succ_descFactorial_succ, Nat.add_sub_add_right,
        Finset.prod_Ico_succ_top (Nat.sub_le b k)]
      push_cast
      module

/-! ### The Gram entries (l.1313–1322) -/

theorem posOp_append_ones (c : R) (μ : List ℕ) (a : ℕ) :
    VirEnv.posOp c (μ ++ List.replicate a 1) = VirEnv.L c 1 ^ a * VirEnv.posOp c μ := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : VirEnv.posOp c (μ ++ List.replicate a 1 ++ [1]) =
        VirEnv.L c 1 * VirEnv.posOp c (μ ++ List.replicate a 1) := by
      simp [VirEnv.posOp]
    rw [List.replicate_succ', ← List.append_assoc, e, ih, pow_succ', mul_assoc]

theorem negOp_append_ones (c : R) (μ : List ℕ) (a : ℕ) :
    VirEnv.negOp c (μ ++ List.replicate a 1) = VirEnv.negOp c μ * VirEnv.L c (-1) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : VirEnv.negOp c (μ ++ List.replicate a 1 ++ [1]) =
        VirEnv.negOp c (μ ++ List.replicate a 1) * VirEnv.L c (-1) := by
      simp [VirEnv.negOp, mul_assoc]
    rw [List.replicate_succ', ← List.append_assoc, e, ih, pow_succ, mul_assoc]

/-- The local bracket `⟨Δ| ad(L_1)^p(L_μ L_{−μ'}) L_{−1}^q |Δ⟩` (paper.tex l.1322). -/
noncomputable def locBr (c h : R) (μ μ' : List ℕ) (p q : ℕ) : R :=
  vacuum c h ((adp (VirEnv.L c 1) p (VirEnv.posOp c μ * VirEnv.negOp c μ') *
    VirEnv.L c (-1) ^ q) • (hw : Verma R c h))

/-- `G_{(1^a,μ),(1^{a'},μ')} = ∑_p C(a,p) (a'!/q!) ∏_{s=q}^{a'−1}(2Δ+s)
⟨Δ|ad(L_1)^p(L_μ L_{−μ'}) L_{−1}^q|Δ⟩`, `q = a' − (a − p)` (paper.tex l.1313–1322, before the
rescaling by powers of `t`). -/
theorem gramWord_ones (c h : R) (μ μ' : List ℕ) (hμ' : PosWord μ') (a a' : ℕ) :
    gramWord c h (μ ++ List.replicate a 1) (μ' ++ List.replicate a' 1) =
      ∑ p ∈ Finset.range (a + 1),
        (a.choose p : R) * ((a'.descFactorial (a - p) : R) *
          ∏ s ∈ Finset.Ico (a' - (a - p)) a', (2 * h + (s : R))) *
          locBr c h μ μ' p (a' - (a - p)) := by
  have hpos : PosWord (μ' ++ List.replicate a' 1) := by
    intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hμ' y hy
    · rw [List.eq_of_mem_replicate hy]
      exact one_pos
  have h1 : neg (c := c) (h := h) (μ' ++ List.replicate a' 1) = VirEnv.negOp c μ' • vb c h a' := by
    rw [neg, negOp_append_ones, mul_smul]
    rfl
  have h2 : VirEnv.posOp c (μ ++ List.replicate a 1) • neg (c := c) (h := h)
      (μ' ++ List.replicate a' 1) = ∑ p ∈ Finset.range (a + 1),
        ((a.choose p : R) * ((a'.descFactorial (a - p) : R) *
          ∏ s ∈ Finset.Ico (a' - (a - p)) a', (2 * h + (s : R)))) •
        ((adp (VirEnv.L c 1) p (VirEnv.posOp c μ * VirEnv.negOp c μ') *
          VirEnv.L c (-1) ^ (a' - (a - p))) • (hw : Verma R c h)) := by
    rw [h1, posOp_append_ones, ← mul_smul, mul_assoc, pow_mul_eq_sum_ad, Finset.sum_smul]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e2 : (adp (VirEnv.L c 1) p (VirEnv.posOp c μ * VirEnv.negOp c μ') *
        VirEnv.L c (-1) ^ (a' - (a - p))) • (hw : Verma R c h) =
        adp (VirEnv.L c 1) p (VirEnv.posOp c μ * VirEnv.negOp c μ') • vb c h (a' - (a - p)) :=
      mul_smul _ _ _
    rw [e2, ← Nat.cast_smul_eq_nsmul R (a.choose p), smul_assoc, mul_smul, L1_pow_Lm1_pow,
      smul_comm (adp (VirEnv.L c 1) p (VirEnv.posOp c μ * VirEnv.negOp c μ')) _
        (vb c h (a' - (a - p)))]
    exact smul_smul (a.choose p : R) ((a'.descFactorial (a - p) : R) *
      ∏ s ∈ Finset.Ico (a' - (a - p)) a', (2 * h + (s : R)))
      (adp (VirEnv.L c 1) p (VirEnv.posOp c μ * VirEnv.negOp c μ') • vb c h (a' - (a - p)))
  rw [← vacuum_gramWord (isVacuum_vacuum (c := c) (h := h)) _ _ hpos, h2, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

end Virasoro.H13C
