import Virasoro.Proofs.P2Sec9Ratio

/-!
# Theorem 9.2: the four quadrants (paper.tex l.2697–2713)

The shifted box `[1-R+k,R+k] × [1-S+m,S+m]` without the origin is the disjoint union of four
quadrants, each indexed by `{0,…,R-1} × {0,…,S-1}`; the origin is omitted in the second one.
-/

namespace Virasoro.P2

open Virasoro

/-- The index set `{0,…,R-1} × {0,…,S-1}` of the pairs `(p',q') = (2i+1-R, 2i'+1-S)`. -/
def idxBox (R S : ℕ) : Finset (ℕ × ℕ) := Finset.range R ×ˢ Finset.range S

theorem box_quadrants {R S k m : ℕ} (hk : k < R) (hm : m < S) (f : ℤ × ℤ → ℂ) :
    ∏ z ∈ (boxShift R S k m).erase (0, 0), f z =
      (∏ y ∈ idxBox R S, f ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 + m)) *
        (∏ y ∈ (idxBox R S).erase (k, m), f ((k : ℤ) - y.1, (m : ℤ) - y.2)) *
        (∏ y ∈ idxBox R S, f ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 - S + m)) *
        (∏ y ∈ idxBox R S, f ((k : ℤ) - y.1, (S : ℤ) - y.2 + m)) := by
  set B := (boxShift R S k m).erase (0, 0) with hB
  have q1 : ∏ z ∈ (B.filter fun z => (k : ℤ) < z.1).filter (fun z => (m : ℤ) < z.2), f z =
      ∏ y ∈ idxBox R S, f ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 + m) := by
    refine Finset.prod_nbij' (fun z => ((z.1 - 1 - k).toNat, (z.2 - 1 - m).toNat))
      (fun y => ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 + m)) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, idxBox, Finset.mem_range, ne_eq, Prod.ext_iff] at hz ⊢
      omega
    · intro y hy
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, idxBox, Finset.mem_range, ne_eq, Prod.ext_iff] at hy ⊢
      omega
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, ne_eq, Prod.ext_iff] at hz
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro y hy
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, ne_eq, Prod.ext_iff] at hz
      congr 1
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
  have q3 : ∏ z ∈ (B.filter fun z => (k : ℤ) < z.1).filter (fun z => ¬(m : ℤ) < z.2), f z =
      ∏ y ∈ idxBox R S, f ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 - S + m) := by
    refine Finset.prod_nbij' (fun z => ((z.1 - 1 - k).toNat, (z.2 - 1 + S - m).toNat))
      (fun y => ((y.1 : ℤ) + 1 + k, (y.2 : ℤ) + 1 - S + m)) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, idxBox, Finset.mem_range, ne_eq, Prod.ext_iff] at hz ⊢
      omega
    · intro y hy
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, idxBox, Finset.mem_range, ne_eq, Prod.ext_iff] at hy ⊢
      omega
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, ne_eq, Prod.ext_iff] at hz
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro y hy
      simp only [idxBox, Finset.mem_product, Finset.mem_range] at hy
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, ne_eq, Prod.ext_iff] at hz
      congr 1
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
  have q2 : ∏ z ∈ (B.filter fun z => ¬(k : ℤ) < z.1).filter (fun z => ¬(m : ℤ) < z.2), f z =
      ∏ y ∈ (idxBox R S).erase (k, m), f ((k : ℤ) - y.1, (m : ℤ) - y.2) := by
    refine Finset.prod_nbij' (fun z => ((k - z.1).toNat, (m - z.2).toNat))
      (fun y => ((k : ℤ) - y.1, (m : ℤ) - y.2)) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, idxBox, Finset.mem_range, ne_eq, Prod.ext_iff] at hz ⊢
      omega
    · intro y hy
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, idxBox, Finset.mem_range, ne_eq, Prod.ext_iff] at hy ⊢
      omega
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, ne_eq, Prod.ext_iff] at hz
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro y hy
      simp only [idxBox, Finset.mem_erase, Finset.mem_product, Finset.mem_range] at hy
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, ne_eq, Prod.ext_iff] at hz
      congr 1
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
  have q4 : ∏ z ∈ (B.filter fun z => ¬(k : ℤ) < z.1).filter (fun z => (m : ℤ) < z.2), f z =
      ∏ y ∈ idxBox R S, f ((k : ℤ) - y.1, (S : ℤ) - y.2 + m) := by
    refine Finset.prod_nbij' (fun z => ((k - z.1).toNat, (S + m - z.2).toNat))
      (fun y => ((k : ℤ) - y.1, (S : ℤ) - y.2 + m)) ?_ ?_ ?_ ?_ ?_
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, idxBox, Finset.mem_range, ne_eq, Prod.ext_iff] at hz ⊢
      omega
    · intro y hy
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, idxBox, Finset.mem_range, ne_eq, Prod.ext_iff] at hy ⊢
      omega
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, ne_eq, Prod.ext_iff] at hz
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro y hy
      simp only [idxBox, Finset.mem_product, Finset.mem_range] at hy
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
    · intro z hz
      simp only [hB, Finset.mem_filter, Finset.mem_erase, boxShift, Finset.mem_product,
        Finset.mem_Icc, ne_eq, Prod.ext_iff] at hz
      congr 1
      refine Prod.ext ?_ ?_ <;> simp only <;> omega
  rw [← Finset.prod_filter_mul_prod_filter_not B (fun z => (k : ℤ) < z.1),
    ← Finset.prod_filter_mul_prod_filter_not (B.filter fun z => (k : ℤ) < z.1)
      (fun z => (m : ℤ) < z.2),
    ← Finset.prod_filter_mul_prod_filter_not (B.filter fun z => ¬(k : ℤ) < z.1)
      (fun z => (m : ℤ) < z.2), q1, q2, q3, q4]
  ring

end Virasoro.P2
