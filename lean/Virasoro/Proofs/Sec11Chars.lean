import Virasoro.Cited
import Virasoro.Statements.Sec11
import Virasoro.Proofs.EtaPartition
import Virasoro.Proofs.Sec3
import Virasoro.Proofs.JantzenLevel

/-!
# Theorem 11.3: the three Ising characters

From the Euler–Poincaré form of the BGG resolution (`Cited_BGGCharacter`),
`rank G_N = p(N) + ∑_{k=1}^{N} (-1)^k (p(N - ℓ⁺_k) + p(N - ℓ⁻_k))`.  Multiplying by the Euler
product and using `∑_j η_j p(M - j) = δ_{M,0}` gives
`Ĥ(N) = δ_{N,0} + ∑_{k=1}^{N} (-1)^k ([ℓ⁺_k = N] + [ℓ⁻_k = N])`, and the levels `ℓ^±_k` are the
exponents of the theta sums: `ℓ^±_{2m} = e₁(±m)`, `ℓ⁺_{2m+1} = e₂(m)`, `ℓ⁻_{2m+1} = e₂(-m-1)`.
-/

namespace Virasoro

open Finset

/-- `p(M - ℓ)` if `ℓ ≤ M`, and `0` otherwise. -/
def pShift (M ℓ : ℕ) : ℤ := if ℓ ≤ M then (Fintype.card (Nat.Partition (M - ℓ)) : ℤ) else 0

/-- `∑_{j=0}^{N} η_j p(N - j - ℓ) = [ℓ = N]`. -/
theorem eta_pShift (N ℓ : ℕ) :
    ∑ j ∈ range (N + 1), eta j * pShift (N - j) ℓ = if ℓ = N then 1 else 0 := by
  by_cases h : ℓ ≤ N
  · have key : ∑ j ∈ range (N + 1), eta j * pShift (N - j) ℓ
        = ∑ j ∈ range (N - ℓ + 1), eta j * (Fintype.card (Nat.Partition (N - ℓ - j)) : ℤ) := by
      rw [show N + 1 = (N - ℓ + 1) + ℓ by omega, Finset.sum_range_add]
      have h2 : ∑ x ∈ range ℓ, eta (N - ℓ + 1 + x) * pShift (N - (N - ℓ + 1 + x)) ℓ = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx' : x < ℓ := Finset.mem_range.mp hx
        have : ¬ ℓ ≤ N - (N - ℓ + 1 + x) := by omega
        simp [pShift, this]
      rw [h2, add_zero]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < N - ℓ + 1 := Finset.mem_range.mp hj
      have hl : ℓ ≤ N - j := by omega
      simp only [pShift, hl, if_true]
      rw [show N - j - ℓ = N - ℓ - j by omega]
    rw [key, eta_partition]
    by_cases hN : ℓ = N
    · subst hN; simp
    · rw [if_neg (by omega), if_neg hN]
  · rw [if_neg (by omega)]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ¬ ℓ ≤ N - j := by omega
    simp [pShift, this]

/-- The rank predicted by the BGG resolution at level `M`, for level functions `ℓ^±`. -/
def bggRank (ellP ellM : ℕ → ℕ) (M : ℕ) : ℤ :=
  (Fintype.card (Nat.Partition M) : ℤ) +
    ∑ k ∈ Icc 1 M, (-1 : ℤ) ^ k * (pShift M (ellP k) + pShift M (ellM k))

/-- If `ℓ^±_k ≥ k`, the `k`-sum of `bggRank` may be extended to `1 ≤ k ≤ N` for `M ≤ N`. -/
theorem bggRank_extend (ellP ellM : ℕ → ℕ) (hP : ∀ k, 1 ≤ k → k ≤ ellP k)
    (hM : ∀ k, 1 ≤ k → k ≤ ellM k) {M N : ℕ} (hMN : M ≤ N) :
    bggRank ellP ellM M = (Fintype.card (Nat.Partition M) : ℤ) +
      ∑ k ∈ Icc 1 N, (-1 : ℤ) ^ k * (pShift M (ellP k) + pShift M (ellM k)) := by
  unfold bggRank
  congr 1
  apply Finset.sum_subset (Finset.Icc_subset_Icc (le_refl 1) hMN)
  intro k hk hk'
  simp only [Finset.mem_Icc] at hk hk'
  have h1 : M < k := by omega
  have hp : ¬ ellP k ≤ M := by have := hP k hk.1; omega
  have hm : ¬ ellM k ≤ M := by have := hM k hk.1; omega
  simp [pShift, hp, hm]

/-- Multiplying the BGG rank by the Euler product:
`∑_j η_j rank(N - j) = δ_{N,0} + ∑_{k=1}^{N} (-1)^k ([ℓ⁺_k = N] + [ℓ⁻_k = N])`. -/
theorem eta_bggRank (ellP ellM : ℕ → ℕ) (hP : ∀ k, 1 ≤ k → k ≤ ellP k)
    (hM : ∀ k, 1 ≤ k → k ≤ ellM k) (N : ℕ) :
    ∑ j ∈ range (N + 1), eta j * bggRank ellP ellM (N - j) =
      (if N = 0 then 1 else 0) +
        ∑ k ∈ Icc 1 N, (-1 : ℤ) ^ k *
          ((if ellP k = N then 1 else 0) + (if ellM k = N then 1 else 0)) := by
  have hext : ∀ j ∈ range (N + 1), eta j * bggRank ellP ellM (N - j) =
      eta j * (Fintype.card (Nat.Partition (N - j)) : ℤ) +
        ∑ k ∈ Icc 1 N, (-1 : ℤ) ^ k *
          (eta j * pShift (N - j) (ellP k) + eta j * pShift (N - j) (ellM k)) := by
    intro j _
    rw [bggRank_extend ellP ellM hP hM (Nat.sub_le N j), mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [Finset.sum_congr rfl hext, Finset.sum_add_distrib, eta_partition, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, eta_pShift, eta_pShift]

/-- Centered sums: `∑_{i<2N+1} G(i - N) = G 0 + ∑_{m<N} (G(m+1) + G(-(m+1)))`. -/
theorem sum_centered (G : ℤ → ℤ) (N : ℕ) :
    ∑ i ∈ range (2 * N + 1), G ((i : ℤ) - N) =
      G 0 + ∑ m ∈ range N, (G ((m : ℤ) + 1) + G (-((m : ℤ) + 1))) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun m : ℕ => G ((m : ℤ) + 1) + G (-((m : ℤ) + 1))) n]
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ']
    have hmid : ∑ i ∈ range (2 * n + 1), G (((i + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ)) =
        ∑ i ∈ range (2 * n + 1), G ((i : ℤ) - n) :=
      Finset.sum_congr rfl fun i _ => by congr 1; push_cast; ring
    rw [hmid, ih]
    have e2 : ((2 * n + 1 + 1 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
    have e3 : ((0 : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) = -((n : ℤ) + 1) := by push_cast; ring
    rw [e2, e3]
    ring

/-- Splitting a sum over `1 ≤ k ≤ 2N` by parity. -/
theorem sum_Icc_parity (f : ℕ → ℤ) (N : ℕ) :
    ∑ k ∈ Icc 1 (2 * N), f k = ∑ m ∈ range N, (f (2 * m + 1) + f (2 * m + 2)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hsub : Icc 1 (2 * (n + 1)) = Icc 1 (2 * n) ∪ {2 * n + 1, 2 * n + 2} := by
      ext k; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_insert,
        Finset.mem_singleton]; omega
    rw [hsub, Finset.sum_union]
    · rw [Finset.sum_pair (by omega)]
    · rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk'
      omega

/-- The card of a filter over `range (2N+1)` as a centered indicator sum. -/
theorem card_filter_centered (e : ℤ → ℤ) (N : ℕ) :
    (((range (2 * N + 1)).filter fun i : ℕ => e ((i : ℤ) - N) = N).card : ℤ) =
      ∑ i ∈ range (2 * N + 1), (if e ((i : ℤ) - N) = N then 1 else 0) := by
  rw [Finset.card_filter]
  push_cast
  rfl

/-- The theta-coefficient identity, for exponent functions `e₁`, `e₂` and levels `ℓ^±` related
by `ℓ^±_{2m+2} = e₁(±(m+1))`, `ℓ⁺_{2m+1} = e₂(m)`, `ℓ⁻_{2m+1} = e₂(-(m+1))`, with `e₁ 0 = 0` and
`e₂ N ≠ N`. -/
theorem thetaCoeff_eq (e₁ e₂ : ℤ → ℤ) (ellP ellM : ℕ → ℕ)
    (hP : ∀ k, 1 ≤ k → k ≤ ellP k) (hM : ∀ k, 1 ≤ k → k ≤ ellM k)
    (h10 : e₁ 0 = 0) (h2N : ∀ N : ℕ, e₂ N ≠ N)
    (hPe : ∀ m : ℕ, (ellP (2 * m + 2) : ℤ) = e₁ ((m : ℤ) + 1))
    (hMe : ∀ m : ℕ, (ellM (2 * m + 2) : ℤ) = e₁ (-((m : ℤ) + 1)))
    (hPo : ∀ m : ℕ, (ellP (2 * m + 1) : ℤ) = e₂ m)
    (hMo : ∀ m : ℕ, (ellM (2 * m + 1) : ℤ) = e₂ (-((m : ℤ) + 1))) (N : ℕ) :
    thetaCoeff e₁ e₂ N =
      (if N = 0 then 1 else 0) +
        ∑ k ∈ Icc 1 N, (-1 : ℤ) ^ k *
          ((if ellP k = N then 1 else 0) + (if ellM k = N then 1 else 0)) := by
  -- extend the `k`-sum to `1 ≤ k ≤ 2N`
  have hext : ∑ k ∈ Icc 1 N, (-1 : ℤ) ^ k *
        ((if ellP k = N then 1 else 0) + (if ellM k = N then 1 else 0)) =
      ∑ k ∈ Icc 1 (2 * N), (-1 : ℤ) ^ k *
        ((if ellP k = N then 1 else 0) + (if ellM k = N then 1 else 0)) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) ?_
    intro k hk hk'
    simp only [Finset.mem_Icc] at hk hk'
    have hp : ellP k ≠ N := by have := hP k hk.1; omega
    have hm : ellM k ≠ N := by have := hM k hk.1; omega
    simp [hp, hm]
  rw [hext, sum_Icc_parity]
  -- the indicator `[ℓ = N]` in terms of the integer exponent
  have ind : ∀ (a : ℕ) (z : ℤ), (a : ℤ) = z →
      (if a = N then (1 : ℤ) else 0) = if z = N then 1 else 0 := by
    intro a z h
    subst h
    by_cases ha : a = N
    · simp [ha]
    · have : (a : ℤ) ≠ N := by exact_mod_cast ha
      simp [ha, this]
  have hpar : ∀ m : ℕ,
      (-1 : ℤ) ^ (2 * m + 1) * ((if ellP (2 * m + 1) = N then 1 else 0) +
          (if ellM (2 * m + 1) = N then 1 else 0)) +
        (-1 : ℤ) ^ (2 * m + 2) * ((if ellP (2 * m + 2) = N then 1 else 0) +
          (if ellM (2 * m + 2) = N then 1 else 0)) =
      ((if e₁ ((m : ℤ) + 1) = N then 1 else 0) + (if e₁ (-((m : ℤ) + 1)) = N then 1 else 0)) -
        ((if e₂ (m : ℤ) = N then 1 else 0) + (if e₂ (-((m : ℤ) + 1)) = N then 1 else 0)) := by
    intro m
    rw [ind _ _ (hPo m), ind _ _ (hMo m), ind _ _ (hPe m), ind _ _ (hMe m)]
    have o : (-1 : ℤ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; simp
    have ev : (-1 : ℤ) ^ (2 * m + 2) = 1 := by
      rw [show 2 * m + 2 = 2 * (m + 1) by ring, pow_mul]; simp
    rw [o, ev]
    ring
  rw [Finset.sum_congr rfl fun m _ => hpar m]
  unfold thetaCoeff
  rw [card_filter_centered, card_filter_centered, sum_centered (fun z => if e₁ z = N then 1 else 0),
    sum_centered (fun z => if e₂ z = N then 1 else 0)]
  rw [h10]
  -- the `e₂` sums differ by the terms `e₂ 0` and `e₂ N`, which are not `N` except `e₂ 0 = 0 = N`
  have hshift : (if e₂ 0 = N then (1 : ℤ) else 0) +
      ∑ m ∈ range N, ((if e₂ ((m : ℤ) + 1) = N then 1 else 0) +
        (if e₂ (-((m : ℤ) + 1)) = N then 1 else 0)) =
      ∑ m ∈ range N, ((if e₂ (m : ℤ) = N then 1 else 0) +
        (if e₂ (-((m : ℤ) + 1)) = N then 1 else 0)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← add_assoc]
    congr 1
    have h1 := Finset.sum_range_succ' (fun m : ℕ => (if e₂ (m : ℤ) = N then (1 : ℤ) else 0)) N
    have h2 := Finset.sum_range_succ (fun m : ℕ => (if e₂ (m : ℤ) = N then (1 : ℤ) else 0)) N
    have hN : (if e₂ (N : ℤ) = N then (1 : ℤ) else 0) = 0 := by simp [h2N N]
    rw [hN, add_zero] at h2
    rw [← h2, h1]
    push_cast
    ring
  have hz : (if (0 : ℤ) = N then (1 : ℤ) else 0) = if N = 0 then 1 else 0 := by
    by_cases h : N = 0
    · subst h; simp
    · have : (0 : ℤ) ≠ N := by exact_mod_cast (Ne.symm h)
      simp [h, this]
  rw [hz, Finset.sum_sub_distrib, ← hshift]
  ring

end Virasoro

namespace Virasoro

open Finset

/-- `ℓ⁺_{2m+2} = (m+1)(12(m+1) + n₀)` at `(p,p') = (3,4)`. -/
theorem ellPlus34_even (r s m : ℕ) (hnn : 0 ≤ ((m : ℤ) + 1) * (((m : ℤ) + 1) * 12 + (4 * r - 3 * s))) :
    (ellPlus 3 4 r s (2 * m + 2) : ℤ) = ((m : ℤ) + 1) * (12 * ((m : ℤ) + 1) + (4 * r - 3 * s)) := by
  unfold ellPlus
  rw [if_pos (by omega), show (2 * m + 2) / 2 = m + 1 by omega]
  push_cast
  rw [Int.toNat_of_nonneg (by linarith)]
  ring

/-- `ℓ⁻_{2m+2} = (m+1)(12(m+1) - n₀)` at `(p,p') = (3,4)`. -/
theorem ellMinus34_even (r s m : ℕ) (hnn : 0 ≤ ((m : ℤ) + 1) * (((m : ℤ) + 1) * 12 - (4 * r - 3 * s))) :
    (ellMinus 3 4 r s (2 * m + 2) : ℤ) = ((m : ℤ) + 1) * (12 * ((m : ℤ) + 1) - (4 * r - 3 * s)) := by
  unfold ellMinus
  rw [if_pos (by omega), show (2 * m + 2) / 2 = m + 1 by omega]
  push_cast
  rw [Int.toNat_of_nonneg (by linarith)]
  ring

/-- `ℓ⁺_{2m+1} = (r + 3m)(s + 4m)` at `(p,p') = (3,4)`. -/
theorem ellPlus34_odd (r s m : ℕ) :
    (ellPlus 3 4 r s (2 * m + 1) : ℤ) = ((r : ℤ) + 3 * m) * ((s : ℤ) + 4 * m) := by
  unfold ellPlus
  rw [if_neg (by omega), show (2 * m + 1) / 2 = m by omega]
  push_cast
  ring

/-- `ℓ⁻_{2m+1} = (3(m+1) - r)(4(m+1) - s)` at `(p,p') = (3,4)`, for `r ≤ 3`, `s ≤ 4`. -/
theorem ellMinus34_odd (r s m : ℕ) (hr : r ≤ 3) (hs : s ≤ 4) :
    (ellMinus 3 4 r s (2 * m + 1) : ℤ) = (3 * ((m : ℤ) + 1) - r) * (4 * ((m : ℤ) + 1) - s) := by
  unfold ellMinus
  rw [if_neg (by omega), show (2 * m + 1) / 2 = m by omega]
  rw [Nat.cast_mul, Nat.cast_sub (by nlinarith), Nat.cast_sub (by nlinarith)]
  push_cast
  ring

/-- The eta-reduced irreducible block at an interior Ising weight, from the BGG formula. -/
theorem hatH_eq_of_bgg (hB : Cited_BGGCharacter) (r s : ℕ) (h : ℂ) (hr : 0 < r) (hr3 : r < 3)
    (hs : 0 < s) (hs4 : s < 4) (hrs : 4 * r + 3 * s < 3 * 4)
    (hh : kacH (r : ℤ) (s : ℤ) b0 = h) (N : ℕ) :
    hatH h N = (if N = 0 then 1 else 0) +
      ∑ k ∈ Icc 1 N, (-1 : ℤ) ^ k *
        ((if ellPlus 3 4 r s k = N then 1 else 0) + (if ellMinus 3 4 r s k = N then 1 else 0)) := by
  have hc : kacC b0 = (1 / 2 : ℂ) := def_fixed_specialization_ising.1
  have hrank : ∀ M : ℕ, ((gram (1 / 2 : ℂ) h M).rank : ℤ) =
      bggRank (ellPlus 3 4 r s) (ellMinus 3 4 r s) M := by
    intro M
    have := hB 3 4 r s (by norm_num) (by norm_num) (by norm_num) hr hr3 hs hs4 hrs b0
      (by rw [b0_sq]; norm_num) M
    rw [hc, hh] at this
    rw [this]
    rfl
  unfold hatH
  simp_rw [hrank]
  exact eta_bggRank _ _
    (fun k hk => le_ellPlus (by norm_num) (by norm_num) hr hs hs4 hk)
    (fun k hk => le_ellMinus (by norm_num) (by norm_num) hr3 hs hs4 hk) N

end Virasoro

namespace Virasoro

open Finset

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 100000 in
/-- Theorem 11.3 (`thm:ising-characters`), from the BGG resolution of Iohara–Koga, Thm 6.9. -/
theorem thm_ising_characters (hB : Cited_BGGCharacter) : Stmt_thm_ising_characters := by
  have hw : ∀ r s : ℤ, kacH r s b0 = (isingDelta r s : ℂ) := def_fixed_specialization_ising.2
  have h11 : kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = 0 := by rw [hw]; norm_num [isingDelta]
  have h21 : kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b0 = 1 / 2 := by rw [hw]; norm_num [isingDelta]
  have h12 : kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b0 = 1 / 16 := by rw [hw]; norm_num [isingDelta]
  have T0 : ∀ N : ℕ, hatH 0 N =
      thetaCoeff (fun j => 12 * j ^ 2 + j) (fun j => 12 * j ^ 2 + 7 * j + 1) N := by
    intro N
    rw [hatH_eq_of_bgg hB 1 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) h11 N]
    symm
    refine thetaCoeff_eq _ _ _ _
      (fun k hk => le_ellPlus (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hk)
      (fun k hk => le_ellMinus (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hk) (by norm_num) (fun n => by push_cast; nlinarith) (fun m => ?_)
      (fun m => ?_) (fun m => ?_) (fun m => ?_) N
    · rw [ellPlus34_even 1 1 m (by push_cast; positivity)]; push_cast; ring
    · rw [ellMinus34_even 1 1 m (by push_cast; nlinarith)]; push_cast; ring
    · rw [ellPlus34_odd]; push_cast; ring
    · rw [ellMinus34_odd 1 1 m (by norm_num) (by norm_num)]; push_cast; ring
  have T12 : ∀ N : ℕ, hatH (1 / 2) N =
      thetaCoeff (fun j => 12 * j ^ 2 + 5 * j) (fun j => 12 * j ^ 2 + 11 * j + 2) N := by
    intro N
    rw [hatH_eq_of_bgg hB 2 1 (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) h21 N]
    symm
    refine thetaCoeff_eq _ _ _ _
      (fun k hk => le_ellPlus (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hk)
      (fun k hk => le_ellMinus (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hk) (by norm_num) (fun n => by push_cast; nlinarith) (fun m => ?_)
      (fun m => ?_) (fun m => ?_) (fun m => ?_) N
    · rw [ellPlus34_even 2 1 m (by push_cast; positivity)]; push_cast; ring
    · rw [ellMinus34_even 2 1 m (by push_cast; nlinarith)]; push_cast; ring
    · rw [ellPlus34_odd]; push_cast; ring
    · rw [ellMinus34_odd 2 1 m (by norm_num) (by norm_num)]; push_cast; ring
  have T116 : ∀ N : ℕ, hatH (1 / 16) N =
      thetaCoeff (fun j => 12 * j ^ 2 - 2 * j) (fun j => 12 * j ^ 2 + 10 * j + 2) N := by
    intro N
    rw [hatH_eq_of_bgg hB 1 2 (1 / 16) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) h12 N]
    symm
    refine thetaCoeff_eq _ _ _ _
      (fun k hk => le_ellPlus (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hk)
      (fun k hk => le_ellMinus (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hk) (by norm_num) (fun n => by push_cast; nlinarith) (fun m => ?_)
      (fun m => ?_) (fun m => ?_) (fun m => ?_) N
    · rw [ellPlus34_even 1 2 m (by push_cast; nlinarith)]; push_cast; ring
    · rw [ellMinus34_even 1 2 m (by push_cast; nlinarith)]; push_cast; ring
    · rw [ellPlus34_odd]; push_cast; ring
    · rw [ellMinus34_odd 1 2 m (by norm_num) (by norm_num)]; push_cast; ring
  refine ⟨T0, T12, T116, ?_, ?_, ?_⟩
  · intro N hN
    rw [T0]
    interval_cases N <;> decide
  · intro N hN
    rw [T12]
    interval_cases N <;> decide
  · intro N hN
    rw [T116]
    interval_cases N <;> decide

end Virasoro
