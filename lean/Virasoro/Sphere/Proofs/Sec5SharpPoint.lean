import Virasoro.Sphere.Proofs.Sec5SharpLam
import Virasoro.Sphere.Proofs.Sec3FpowExp
import Virasoro.Sphere.Proofs.Sec2HSeries

/-!
# Theorem 5.4: `ℬ_M = (-1)^M binom(κ,M)` at the specialization (sphere/paper.tex l.1662–1690)

At `B = 0` (`β₄ = -(1 + b² + β_μ + β₃)`) the solution `z^s(1-z)^κ` of the BPZ equation has the
coefficients `(-1)^n binom(κ,n)`, `κ = (1 + b² + β₃)/2`; they satisfy the recursion of the BPZ
coefficients.  `P₀(s+n) = n b⁻²(n - 1 + C)`, `C = 1 + b² + β_μ`, and `C = 1 - u` with `u ≤ M`
would make `μ = h_{1,u}(b)`, so `det G_M(c,μ) = 0`.  Hence the block coefficients up to the
level `M` are `(-1)^n binom(κ,n)` (l.1673–1690).
-/

namespace Virasoro.Sphere

open Virasoro Polynomial

/-- `(-1)^n binom(κ,n)`, the coefficients of `(1-z)^κ`. -/
noncomputable def gSeq (κ : ℂ) (n : ℕ) : ℂ := (-1) ^ n * gbinom κ n

section Point

variable (b βμ β₃ : ℂ)

/-- `β₄` with `B = (1 + b² + β_μ + β₃ + β₄)/2 = 0`. -/
noncomputable def β4of : ℂ := -(1 + b ^ 2 + βμ + β₃)

/-- `κ = (1 + b² + β₃)/2`. -/
noncomputable def κof : ℂ := (1 + b ^ 2 + β₃) / 2

/-- `(-1)^n binom(κ,n)` solves the BPZ recursion at `B = 0`. -/
theorem gSeq_rec (hb : b ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    let μ := wtB b βμ
    let Δe := bpzWeights b βμ β₃ (β4of b βμ β₃)
    let s := μ - Δe 0 - Δe 1
    let D := Δe 0 + Δe 1 + Δe 2 - Δe 3
    bpzP0 b (Δe 0) (s + n) * gSeq (κof b β₃) n +
      (if 1 ≤ n then bpzP1 b (Δe 0) D (s + n - 1) * gSeq (κof b β₃) (n - 1) else 0) +
      (if 2 ≤ n then bpzP2 b (Δe 0) (Δe 2) D (s + n - 2) * gSeq (κof b β₃) (n - 2) else 0) = 0 := by
  intro μ Δe s D
  have hD0 : Δe 0 = wtB b (βμ + b ^ 2) := rfl
  have hD1 : Δe 1 = kacH 2 1 b := rfl
  have hD2 : Δe 2 = wtB b β₃ := rfl
  have hD3 : Δe 3 = wtB b (β4of b βμ β₃) := rfl
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · -- `n = 1`
    simp only [zero_add, le_refl, if_true, Nat.sub_self, show ¬ (2 ≤ 1) by omega, if_false,
      add_zero]
    have g1 : gSeq (κof b β₃) 1 = -κof b β₃ := by simp [gSeq, gbinom]
    have g0 : gSeq (κof b β₃) 0 = 1 := by simp [gSeq, gbinom]
    rw [g1, g0]
    simp only [s, D, μ, hD0, hD1, hD2, hD3, bpzP0, bpzP1, wtB, kacH, β4of, κof]
    push_cast
    field_simp
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e2 : gSeq (κof b β₃) (i + 2) * (((i : ℂ) + 1) * ((i : ℂ) + 2)) =
        gSeq (κof b β₃) i * ((κof b β₃ - i) * (κof b β₃ - (i + 1))) := by
      have h1 := gbinom_succ_mul2C (κof b β₃) i
      have h2 := gbinom_succ_mul2C (κof b β₃) (i + 1)
      simp only [gSeq, pow_succ]
      push_cast at h1 h2 ⊢
      linear_combination ((κof b β₃ - (i + 1)) * (-1) ^ i) * h1 + ((-1) ^ i * ((i : ℂ) + 1)) * h2
    have e1 : gSeq (κof b β₃) (i + 1) * ((i : ℂ) + 1) =
        -(gSeq (κof b β₃) i * (κof b β₃ - i)) := by
      have h1 := gbinom_succ_mul2C (κof b β₃) i
      simp only [gSeq, pow_succ]
      linear_combination (-(-1 : ℂ) ^ i) * h1
    simp only [show 1 ≤ i + 1 + 1 by omega, show 2 ≤ i + 1 + 1 by omega, if_true,
      show i + 1 + 1 - 1 = i + 1 by omega, show i + 1 + 1 - 2 = i by omega]
    have hi1 : ((i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
    have hi2 : ((i : ℂ) + 2) ≠ 0 := by exact_mod_cast (show i + 2 ≠ 0 by omega)
    have ea : gSeq (κof b β₃) (i + 2) = gSeq (κof b β₃) i * ((κof b β₃ - i) *
        (κof b β₃ - (i + 1))) / (((i : ℂ) + 1) * ((i : ℂ) + 2)) := by
      rw [← e2]; field_simp
    have eb : gSeq (κof b β₃) (i + 1) = -(gSeq (κof b β₃) i * (κof b β₃ - i)) / ((i : ℂ) + 1) := by
      rw [← e1]; field_simp
    rw [show i + 1 + 1 = i + 2 by omega, ea, eb]
    simp only [s, D, μ, hD0, hD1, hD2, hD3, bpzP0, bpzP1, bpzP2, wtB, kacH, β4of, κof]
    push_cast
    field_simp
    ring

/-- `P₀(s+n) = n (n + b² + β_μ)/b²` (`n - 1 + C`, `C = 1 + b² + β_μ`). -/
theorem bpzP0_eq (hb : b ≠ 0) (n : ℕ) :
    bpzP0 b (bpzWeights b βμ β₃ (β4of b βμ β₃) 0)
      (wtB b βμ - bpzWeights b βμ β₃ (β4of b βμ β₃) 0 - bpzWeights b βμ β₃ (β4of b βμ β₃) 1 + n) =
        n * (n + b ^ 2 + βμ) / b ^ 2 := by
  simp only [bpzWeights, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, bpzP0, wtB,
    kacH]
  push_cast
  field_simp
  ring

/-- The block coefficients at `B = 0` up to the level `M` (l.1673–1690). -/
theorem block_point (hBPZ : Cited_BPZEquation) (hK : Cited_KacDeterminant) (hb : b ≠ 0)
    (M : ℕ) (hdet : ∀ m ≤ M, (gram (kacC b) (wtB b βμ) m).det ≠ 0) :
    ∀ n ≤ M, blockAt (kacC b) (wtB b βμ) (bpzWeights b βμ β₃ (β4of b βμ β₃)) n =
      gSeq (κof b β₃) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [blockAt, Bsph_zero, gSeq, gbinom]
    have hc := bpz_at βμ β₃ (β4of b βμ β₃) hBPZ hK hb n (fun m hm => hdet m (by omega))
    have hg := gSeq_rec b βμ β₃ hb n hn0
    simp only at hg
    unfold bpzCoeff at hc
    simp only at hc
    have hP : bpzP0 b (bpzWeights b βμ β₃ (β4of b βμ β₃) 0)
        (wtB b βμ - bpzWeights b βμ β₃ (β4of b βμ β₃) 0 -
          bpzWeights b βμ β₃ (β4of b βμ β₃) 1 + n) ≠ 0 := by
      rw [bpzP0_eq b βμ β₃ hb n]
      refine div_ne_zero (mul_ne_zero (by exact_mod_cast hn0.ne') fun h0 => ?_)
        (pow_ne_zero 2 hb)
      have hβ : βμ = -(1 * b ^ 2 + n) := by linear_combination h0
      have hmem : ((1, n) : Label) ∈ labels M := by
        simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        omega
      have hz := gram_det_eq_zero_of_label hK hb (M := M) hmem
      apply hdet M le_rfl
      rw [← hz, kacHL, kacH_eq_wtB hb, hβ]
      congr 1
      unfold wtB
      push_cast
      ring
    have h1 : 1 ≤ n → blockAt (kacC b) (wtB b βμ) (bpzWeights b βμ β₃ (β4of b βμ β₃)) (n - 1) =
        gSeq (κof b β₃) (n - 1) := fun h => ih (n - 1) (by omega) (by omega)
    have h2 : 2 ≤ n → blockAt (kacC b) (wtB b βμ) (bpzWeights b βμ β₃ (β4of b βμ β₃)) (n - 2) =
        gSeq (κof b β₃) (n - 2) := fun h => ih (n - 2) (by omega) (by omega)
    have hc' : bpzP0 b (bpzWeights b βμ β₃ (β4of b βμ β₃) 0)
        (wtB b βμ - bpzWeights b βμ β₃ (β4of b βμ β₃) 0 -
          bpzWeights b βμ β₃ (β4of b βμ β₃) 1 + n) *
        (blockAt (kacC b) (wtB b βμ) (bpzWeights b βμ β₃ (β4of b βμ β₃)) n -
          gSeq (κof b β₃) n) = 0 := by
      have e1 : (if 1 ≤ n then bpzP1 b (bpzWeights b βμ β₃ (β4of b βμ β₃) 0)
            (bpzWeights b βμ β₃ (β4of b βμ β₃) 0 + bpzWeights b βμ β₃ (β4of b βμ β₃) 1 +
              bpzWeights b βμ β₃ (β4of b βμ β₃) 2 - bpzWeights b βμ β₃ (β4of b βμ β₃) 3)
            (wtB b βμ - bpzWeights b βμ β₃ (β4of b βμ β₃) 0 -
              bpzWeights b βμ β₃ (β4of b βμ β₃) 1 + n - 1) *
            blockAt (kacC b) (wtB b βμ) (bpzWeights b βμ β₃ (β4of b βμ β₃)) (n - 1) else 0) =
          (if 1 ≤ n then bpzP1 b (bpzWeights b βμ β₃ (β4of b βμ β₃) 0)
            (bpzWeights b βμ β₃ (β4of b βμ β₃) 0 + bpzWeights b βμ β₃ (β4of b βμ β₃) 1 +
              bpzWeights b βμ β₃ (β4of b βμ β₃) 2 - bpzWeights b βμ β₃ (β4of b βμ β₃) 3)
            (wtB b βμ - bpzWeights b βμ β₃ (β4of b βμ β₃) 0 -
              bpzWeights b βμ β₃ (β4of b βμ β₃) 1 + n - 1) * gSeq (κof b β₃) (n - 1) else 0) := by
        split_ifs with h
        · rw [h1 h]
        · rfl
      have e2 : (if 2 ≤ n then bpzP2 b (bpzWeights b βμ β₃ (β4of b βμ β₃) 0)
            (bpzWeights b βμ β₃ (β4of b βμ β₃) 2)
            (bpzWeights b βμ β₃ (β4of b βμ β₃) 0 + bpzWeights b βμ β₃ (β4of b βμ β₃) 1 +
              bpzWeights b βμ β₃ (β4of b βμ β₃) 2 - bpzWeights b βμ β₃ (β4of b βμ β₃) 3)
            (wtB b βμ - bpzWeights b βμ β₃ (β4of b βμ β₃) 0 -
              bpzWeights b βμ β₃ (β4of b βμ β₃) 1 + n - 2) *
            blockAt (kacC b) (wtB b βμ) (bpzWeights b βμ β₃ (β4of b βμ β₃)) (n - 2) else 0) =
          (if 2 ≤ n then bpzP2 b (bpzWeights b βμ β₃ (β4of b βμ β₃) 0)
            (bpzWeights b βμ β₃ (β4of b βμ β₃) 2)
            (bpzWeights b βμ β₃ (β4of b βμ β₃) 0 + bpzWeights b βμ β₃ (β4of b βμ β₃) 1 +
              bpzWeights b βμ β₃ (β4of b βμ β₃) 2 - bpzWeights b βμ β₃ (β4of b βμ β₃) 3)
            (wtB b βμ - bpzWeights b βμ β₃ (β4of b βμ β₃) 0 -
              bpzWeights b βμ β₃ (β4of b βμ β₃) 1 + n - 2) * gSeq (κof b β₃) (n - 2) else 0) := by
        split_ifs with h
        · rw [h2 h]
        · rfl
      rw [e1, e2] at hc
      linear_combination hc - hg
    exact sub_eq_zero.1 ((mul_eq_zero.1 hc').resolve_left hP)

theorem gSeq_ne_zero {κ : ℂ} {M : ℕ} (hκ : ∀ i : ℕ, i < M → κ ≠ i) : gSeq κ M ≠ 0 := by
  unfold gSeq gbinom
  have hf : ((M.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero M)
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (div_ne_zero ?_ hf)
  exact Finset.prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (hκ i (Finset.mem_range.1 hi))

end Point

end Virasoro.Sphere
