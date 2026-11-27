import Virasoro.Proofs.Sec8BLabels2
import Virasoro.Proofs.Sec8DiagChains

/-!
# Lemma 8.10 (`lem:boundary-labels`), the pole order

For `Δ = k - i` even, `M_k - M_i = (Δ/2) N₀`; for `Δ` odd, `M_k - M_i = ((Δ-1)/2) N₀ + (M_{i+1} - M_i)`
with `M_{i+1} - M_i ∈ {N₀ - 2x₀, 2x₀}`.  Both give `Δ - 1` lattice points in the box.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' x₀ : ℕ} {b : ℂ}

section Count

variable (hB : BoundarySetting p p' x₀ b)
include hB

theorem bM_gap_even {i k : ℕ} (hik : i < k) (he : (k - i) % 2 = 0) :
    (bM p p' x₀ k : ℤ) - bM p p' x₀ i = 2 * (((k - i) / 2 : ℕ) : ℤ) * ((p : ℤ) * p') := by
  rw [bM_int hB, bM_int hB]
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' i <;> obtain ⟨c, rfl | rfl⟩ := Nat.even_or_odd' k
  · rw [if_pos (by omega), if_pos (by omega), show 2 * c / 2 = c by omega, show 2 * a / 2 = a by omega,
      show (2 * c - 2 * a) / 2 = c - a by omega, Nat.cast_sub (by omega)]
    ring
  · omega
  · omega
  · rw [if_neg (by omega), if_neg (by omega), show (2 * c + 1 + 1) / 2 = c + 1 by omega,
      show (2 * a + 1 + 1) / 2 = a + 1 by omega,
      show (2 * c + 1 - (2 * a + 1)) / 2 = c - a by omega, Nat.cast_sub (by omega)]
    push_cast
    ring

theorem bM_gap_odd {i k : ℕ} (hik : i < k) (ho : (k - i) % 2 = 1) :
    ∃ e : ℤ, |e| < (p : ℤ) * p' ∧ (bM p p' x₀ k : ℤ) - bM p p' x₀ i =
      (2 * (((k - i - 1) / 2 : ℕ) : ℤ) + 1) * ((p : ℤ) * p') + e := by
  have h0 := hB.2.2.2.1
  have h1 := hB.2.2.2.2.1
  have h0' : (0 : ℤ) < x₀ := by exact_mod_cast h0
  have h1' : (x₀ : ℤ) < p * p' := by exact_mod_cast h1
  rw [bM_int hB, bM_int hB]
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' i <;> obtain ⟨c, rfl | rfl⟩ := Nat.even_or_odd' k
  · omega
  · refine ⟨(p : ℤ) * p' - 2 * x₀, abs_lt.2 ⟨by linarith, by linarith⟩, ?_⟩
    rw [if_neg (by omega), if_pos (by omega), show (2 * c + 1 + 1) / 2 = c + 1 by omega,
      show 2 * a / 2 = a by omega, show (2 * c + 1 - 2 * a - 1) / 2 = c - a by omega,
      Nat.cast_sub (by omega)]
    push_cast
    ring
  · refine ⟨2 * x₀ - (p : ℤ) * p', abs_lt.2 ⟨by linarith, by linarith⟩, ?_⟩
    rw [if_pos (by omega), if_neg (by omega), show 2 * c / 2 = c by omega,
      show (2 * a + 1 + 1) / 2 = a + 1 by omega,
      show (2 * c - (2 * a + 1) - 1) / 2 = c - a - 1 by omega, Nat.cast_sub (by omega),
      Nat.cast_sub (by omega)]
    push_cast
    ring
  · omega

/-- The lattice count of Lemma 8.10: `Δ - 1` points. -/
theorem bLabel_count {i k : ℕ} (hik : i < k) :
    ((genAIndex (bLabel p p' x₀ i k).1 (bLabel p p' x₀ i k).2).filter
      (fun pq => (p : ℤ) * pq.2 = p' * pq.1)).card = k - i - 1 := by
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  obtain ⟨h1, h2, hy, hx⟩ := bLabel_xy hB hik
  have hP : (0 : ℤ) < (p : ℤ) * p' := by exact_mod_cast Nat.mul_pos hp hp'
  have habs : |(p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2| = bM p p' x₀ i := by
    rw [hx, bM_abs hB, abs_mul, abs_mul, abs_neg]
    unfold bEps; split_ifs <;> simp
  have hx0 : (p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2 ≠ 0 := by
    intro h
    rw [h, abs_zero, bM_abs hB, eq_comm, abs_eq_zero] at habs
    exact bT_ne hB i habs
  rcases Nat.even_or_odd (k - i) with hev | hod
  · have he : (k - i) % 2 = 0 := Nat.even_iff.1 hev
    obtain ⟨m, hm⟩ : ∃ m, m = (k - i) / 2 := ⟨_, rfl⟩
    have hm1 : 1 ≤ m := by omega
    have hgap : ((p' : ℤ) * (bLabel p p' x₀ i k).1 + p * (bLabel p p' x₀ i k).2) -
        |(p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2| = 2 * m * ((p : ℤ) * p') := by
      rw [hy, habs, bM_gap_even hB hik he, ← hm]
    obtain ⟨B1, B2⟩ := box_line_bounds_even (U := 2 * p' * ((bLabel p p' x₀ i k).1 : ℤ))
      (V := 2 * p * ((bLabel p p' x₀ i k).2 : ℤ)) hP (by ring) (by ring) hgap hx0 hm1
    rw [box_count hp hp' hB.2.2.1 h1 h2 hx0 m (m - 1) B1 B2]
    omega
  · have ho : (k - i) % 2 = 1 := Nat.odd_iff.1 hod
    obtain ⟨e, he, hg⟩ := bM_gap_odd hB hik ho
    have hgap : ((p' : ℤ) * (bLabel p p' x₀ i k).1 + p * (bLabel p p' x₀ i k).2) -
        |(p' : ℤ) * (bLabel p p' x₀ i k).1 - p * (bLabel p p' x₀ i k).2| =
          (2 * (((k - i - 1) / 2 : ℕ) : ℤ) + 1) * ((p : ℤ) * p') + e := by
      rw [hy, habs, hg]
    obtain ⟨B1, B2⟩ := box_line_bounds (U := 2 * p' * ((bLabel p p' x₀ i k).1 : ℤ))
      (V := 2 * p * ((bLabel p p' x₀ i k).2 : ℤ)) hP (by ring) (by ring) hgap he
    rw [box_count hp hp' hB.2.2.1 h1 h2 hx0 _ _ B1 B2]
    omega

/-- The pole order of `R_g`: exactly `Δ - 1`, with `ρ_g ≠ 0`. -/
theorem bR_order {i k : ℕ} (hik : i < k) :
    (bR p p' x₀ b i k).orderTop = ((1 - ((k : ℤ) - i) : ℤ) : WithTop ℤ) ∧ bRho p p' x₀ b i k ≠ 0 := by
  have hmin := bSetting_minimal hB
  have hb0 := b_ne_zero_of hmin
  have hbs : (bsC b : Kd) ≠ 0 := by simpa [bsC] using hb0
  have hP := regVal_genP hbs dvar (bLabel p p' x₀ i k).1 (bLabel p p' x₀ i k).2
  have hPord : (genP (bLabel p p' x₀ i k).1 (bLabel p p' x₀ i k).2 (bGerm (bsC b))
      (HahnSeries.C dvar)).orderTop = 0 :=
    dgOrderTop_zero (by simpa [OrdGE] using hP.1) (by rw [hP.2]; exact genP_ratC_ne hb0 _ _)
  have hord : (bR p p' x₀ b i k).orderTop = ((1 - ((k : ℤ) - i) : ℤ) : WithTop ℤ) := by
    unfold bR RG genR
    rw [HahnSeries.orderTop_mul, genA_orderTop hmin, hPord, add_zero, bLabel_count hB hik]
    congr 1
    omega
  refine ⟨hord, ?_⟩
  unfold bRho
  exact HahnSeries.coeff_orderTop_ne hord

end Count

/-- Lemma 8.10 (`lem:boundary-labels`).

Paper label: lem:boundary-labels -/
theorem lem_boundary_labels : Stmt_lem_boundary_labels := by
  intro p p' x₀ b hB
  refine ⟨fun i k hik => ?_, fun i g h1 h2 hw => label_leads hB i g h1 h2 hw⟩
  obtain ⟨h1, h2, hy, hx⟩ := bLabel_xy hB hik
  obtain ⟨hord, hrho⟩ := bR_order hB hik
  refine ⟨fun g hg1 hg2 => label_iff hB hik g hg1 hg2, h1, h2, hy, hx, ?_, hord.ge, hrho⟩
  rw [hx, hy, bM_sgn hB]
  unfold bEps
  split_ifs <;> ring

end Virasoro
