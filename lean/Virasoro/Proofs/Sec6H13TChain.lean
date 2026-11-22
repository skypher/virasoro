import Virasoro.Proofs.Sec6H13TStep

/-!
# Proposition 6.8(ii): the chains of `(1 − G̃D₀⁻¹)^s` (paper.tex l.1366–1378)

`K̂_s(μ₀; μ)(M)` is the entry of `(1 − G̃D₀⁻¹)^s` at `((1^{M−w₀}, μ₀), (1^{M−w}, μ))` (zero when a
partition does not exist).  It is good from the level `w₀` on, with valuation `max(0, w − w₀)`:
the chain expansion `K̂_{s+1}(μ₀; μ) = ∑_{μ'} K̂_s(μ₀; μ') Ê(μ', μ)` has, for each coefficient,
only the finitely many `μ'` with `|μ'| ≤ w₀ + 2(i+j)`, and the root sets are handled by
`GF.mul_vanish` (`K̂_s(μ₀; μ')` vanishes below `|μ'|`).
-/

namespace Virasoro.H13T

open Virasoro.H13D Virasoro.H13C Finset

/-- A family that is a sum over a size-graded finite index set, whose terms are good from `W` on
with valuation growing with the size, is good from `W` on: each coefficient sees only the terms of
bounded size (l.1366–1378). -/
theorem GF.of_sum_sz {ι : Type*} {G : ℕ → LL} {F : ι → ℕ → LL} {W : ℕ} {D V : ℤ}
    (S : ℕ → Finset ι) (P : ι → Prop) (sz : ι → ℕ) (c : ℤ)
    (hS : ∀ M a, a ∈ S M ↔ P a ∧ sz a ≤ M)
    (hG : ∀ M, W ≤ M → G M = ∑ a ∈ S M, F a M)
    (hord : ∃ b : ℤ, ∀ M : ℕ, W ≤ M → ∀ n < b, (G M).coeff n = 0)
    (hF : ∀ a, P a → GF (F a) W D (max V ((sz a : ℤ) - c)))
    (hz : ∀ a M, P a → W ≤ M → M < sz a → F a M = 0) : GF G W D V := by
  classical
  refine GF.of_cf_eq hord fun i j => ⟨fun M => ∑ a ∈ S (2 * i + 2 * j + c).toNat, F a M,
    GF.sum _ fun a ha => (hF a ((hS _ a).1 ha).1).mono le_rfl (le_max_left _ _), fun M hM => ?_⟩
  set B := (2 * i + 2 * j + c).toNat with hB
  beta_reduce
  rw [hG M hM, cfL_sum, cfL_sum]
  have h1 : ∀ a ∈ S M ∪ S B, a ∉ S M → cfL (F a M) i j = 0 := by
    intro a ha ha'
    rcases mem_union.1 ha with ha | ha
    · exact absurd ha ha'
    · have hP := ((hS B a).1 ha).1
      have hlt : M < sz a := by
        by_contra hc
        exact ha' ((hS M a).2 ⟨hP, by omega⟩)
      rw [hz a M hP hM hlt, cfL_zero]
  have h2 : ∀ a ∈ S M ∪ S B, a ∉ S B → cfL (F a M) i j = 0 := by
    intro a ha ha'
    rcases mem_union.1 ha with ha | ha
    · have hP := ((hS M a).1 ha).1
      have hlt : B < sz a := by
        by_contra hc
        exact ha' ((hS B a).2 ⟨hP, by omega⟩)
      have := (hF a hP).val (M - W) i j (lt_max_of_lt_right (by omega))
      beta_reduce at this
      rwa [show M - W + W = M by omega] at this
    · exact absurd ha ha'
  rw [sum_subset subset_union_left h1, sum_subset subset_union_right h2]

/-- Good from `W` on implies good from any later level on. -/
theorem GF.lift {G : ℕ → LL} {W W' : ℕ} {D V : ℤ} (h : GF G W D V) (hW : W ≤ W') :
    GF G W' D V := by
  have := Good.shift h (W' - W)
  have e : (fun M => G (M + (W' - W) + W)) = fun M => G (M + W') := by
    funext M
    congr 1
    omega
  show Good (fun M => G (M + W')) D V
  rw [← e]
  exact this

theorem GF.mul {G G' : ℕ → LL} {W : ℕ} {D V D' V' : ℤ} (h : GF G W D V) (h' : GF G' W D' V') :
    GF (fun M => G M * G' M) W (D + D') (V + V') :=
  Good.mul h h'

/-! ### The entries of `(1 − G̃D₀⁻¹)^s` -/

/-- The entry of `(1 − G̃D₀⁻¹)^s` along the levels (zero when a partition does not exist). -/
noncomputable def Khat (s : ℕ) (μ₀ μ : List ℕ) (M : ℕ) : LL := by
  classical
  exact if μ₀.sum ≤ M ∧ μ.sum ≤ M then jL ((Em M ^ s) (lamOf μ₀ M) (lamOf μ M)) else 0

theorem Khat_low {s : ℕ} {μ₀ μ : List ℕ} {M : ℕ} (h : M < μ₀.sum ∨ M < μ.sum) :
    Khat s μ₀ μ M = 0 := by
  rw [Khat, if_neg (by omega)]

theorem Ehat_low {μ' μ : List ℕ} {M : ℕ} (h : M < μ'.sum ∨ M < μ.sum) : Ehat μ' μ M = 0 := by
  rw [Ehat, if_neg (by omega)]

theorem Khat_ord (s : ℕ) (μ₀ μ : List ℕ) (M : ℕ) (n : ℤ) (hn : n < 0) :
    (Khat s μ₀ μ M).coeff n = 0 := by
  unfold Khat
  split_ifs
  · exact jL_coeff_neg _ n hn
  · rfl

theorem Khat_succ {μ₀ μ : List ℕ} (s M : ℕ) :
    Khat (s + 1) μ₀ μ M = ∑ μ' ∈ admSet M, Khat s μ₀ μ' M * Ehat μ' μ M := by
  classical
  by_cases hp : μ₀.sum ≤ M ∧ μ.sum ≤ M
  · rw [Khat, if_pos hp, pow_succ, Matrix.mul_apply, map_sum,
      sum_partition_eq M (fun Y => jL ((Em M ^ s) (lamOf μ₀ M) Y * Em M Y (lamOf μ M)))]
    refine sum_congr rfl fun μ' hμ' => ?_
    have h' := (mem_admSet.1 hμ').2
    rw [map_mul, Khat, if_pos ⟨hp.1, h'⟩, Ehat, if_pos ⟨h', hp.2⟩]
  · rw [Khat, if_neg hp]
    refine (sum_eq_zero fun μ' _ => ?_).symm
    by_cases h0 : μ₀.sum ≤ M
    · rw [Ehat_low (Or.inr (by omega)), mul_zero]
    · rw [Khat_low (Or.inl (by omega)), zero_mul]

theorem good_Khat_zero {μ₀ μ : List ℕ} (h₀ : Adm μ₀) (h : Adm μ) :
    GF (Khat 0 μ₀ μ) μ₀.sum 0 (max 0 ((μ.sum : ℤ) - μ₀.sum)) := by
  classical
  by_cases he : μ₀ = μ
  · subst he
    refine GF.congr (G := fun _ => (1 : LL)) (by simpa [GF] using good_one) fun M hM => ?_
    rw [Khat, if_pos ⟨hM, hM⟩, pow_zero, Matrix.one_apply_eq, map_one]
  · refine GF.congr (G := fun _ => (0 : LL)) (by simpa [GF] using good_zero 0 _) fun M hM => ?_
    unfold Khat
    split_ifs with hp
    · rw [pow_zero, Matrix.one_apply_ne (fun hl => he ((lamOf_inj h₀ h hp.1 hp.2).1 hl)), map_zero]
    · rfl

/-- `K̂_s(μ₀; μ)` is good from the level `w₀` on, with valuation `max(0, w − w₀)`
(paper.tex l.1366–1378). -/
theorem good_Khat {μ₀ : List ℕ} (h₀ : Adm μ₀) (s : ℕ) :
    ∀ μ, Adm μ → GF (Khat s μ₀ μ) μ₀.sum 0 (max 0 ((μ.sum : ℤ) - μ₀.sum)) := by
  induction s with
  | zero => exact fun μ h => good_Khat_zero h₀ h
  | succ s ih =>
    intro μ h
    refine GF.of_sum_sz admSet Adm List.sum μ₀.sum (fun M a => mem_admSet)
      (fun M _ => Khat_succ s M) ⟨0, fun M _ n hn => Khat_ord _ _ _ M n hn⟩ (fun μ' h' => ?_)
      (fun μ' M _ _ hM => by rw [Khat_low (Or.inr hM), zero_mul])
    by_cases hle : μ₀.sum ≤ μ'.sum
    · have := GF.mul_vanish (ih μ' h') (good_Ehat h' h) hle
        (fun M _ hM => Khat_low (Or.inr hM))
      exact this.mono (by simp) (by omega)
    · have := GF.mul (ih μ' h') ((good_Ehat h' h).lift (by omega : μ'.sum ≤ μ₀.sum))
      exact this.mono (by simp) (by omega)

end Virasoro.H13T
