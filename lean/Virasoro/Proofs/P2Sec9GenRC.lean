import Virasoro.Proofs.P2Sec13DiagMain
import Virasoro.Proofs.P2Sec12Cocycle
import Virasoro.Proofs.P2Sec9Final
import Virasoro.Proofs.P2Sec11VertexStep

/-!
# Theorem 9.3, the identity (9.3) (paper.tex l.1926–1945, proof l.3040–3075)

Multiplying Lemma 13.1 at a node `μ` with children `ν₁`, `ν₂` by `Ω_{u,v}(λ→μ) q^{μ-λ}` gives,
by the cocycle property (Proposition 12.1(ii)), `T̃(μ) + T̃(ν₂) = F̃(μ) - F̃(ν₁)`.  Along the
alternating chain `μ₀ = λ`, `μ₁ = μ⁻₁`, `μ₂ = μ⁺₂`, … (`ν₂ = μ_{j+1}`) the alternating sum
telescopes; at level `N` the terms of layer `N+1` vanish.
-/

namespace Virasoro.P2

open Virasoro

section Path

variable {p p' r s k m : ℕ}

theorem pathProd_append_single : ∀ (l : List Bool) (ε : Bool) (j : ℕ) (x : Bool),
    pathProd p p' r s k m ε j (l ++ [x]) =
      pathProd p p' r s k m ε j l * cArrow p p' r s k m (l.getLast?.getD ε) (j + l.length) x
  | [], ε, j, x => by simp [pathProd]
  | y :: l, ε, j, x => by
    rw [List.cons_append, pathProd, pathProd_append_single l y (j + 1) x, pathProd,
      List.getLast?_cons, Option.getD_some, List.length_cons]
    rw [show j + (l.length + 1) = j + 1 + l.length by ring]
    ring

/-- The cocycle `Ω(λ→μ^ε_j) c(μ^ε_j→μ^{ε'}_{j+1}) = Ω(λ→μ^{ε'}_{j+1})` (Proposition 12.1(ii)),
for `j ≥ 1`, and at `j = 0` from the node `μ⁺_0 = λ`. -/
theorem omega_cocycle {b : ℂ} (hset : MinimalSetting p p' r s b) (hk : k < min r (p - r))
    (hm : m < min s (p' - s)) (ε : Bool) (j : ℕ) (hj : j ≠ 0 ∨ ε = true) (ε' : Bool) :
    Omega p p' r s k m true 0 ε j * cArrow p p' r s k m ε j ε' =
      Omega p p' r s k m true 0 ε' (j + 1) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · have hε : ε = true := hj.resolve_left (fun h => h rfl)
    subst hε
    simp [Omega, pathProd]
  · have hpi := (prop_bgg_cocycle p p' r s b hset k m hk hm).2.2
    rw [Omega, if_neg (by omega), Omega, if_neg (by omega), Nat.add_sub_cancel]
    have h1 := pathProd_append_single (p := p) (p' := p') (r := r) (s := s) (k := k) (m := m)
      (List.replicate (j - 1) true ++ [ε]) true 0 ε'
    have hlast : (List.replicate (j - 1) true ++ [ε]).getLast? = some ε := by simp
    have hlen : (List.replicate (j - 1) true ++ [ε]).length = j := by simp; omega
    rw [hlast, Option.getD_some, hlen, zero_add] at h1
    rw [← h1]
    refine hpi true 0 _ _ (by simp) (by simp; omega) (by simp)

end Path

section Shift

variable (p p' r s k m : ℕ) (b : ℂ) (N : ℕ)

/-- `[q^N] Ω(λ→μ^ε_j) q^{ℓ^ε_j} ℱ^Verma_{μ^ε_j}`. -/
noncomputable def Fsh (ε : Bool) (j : ℕ) : ℂ :=
  if ellOrb p p' r s ε j ≤ N then
    (Omega p p' r s k m true 0 ε j : ℂ) *
      FvalAt (kacC b) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) (N - ellOrb p p' r s ε j)
        (muOrb p p' r s ε j)
  else 0

/-- `[q^N] Ω(λ→μ^ε_j) q^{ℓ^ε_j} 𝒯^irr_{μ^ε_j}` for chosen traces `tv`. -/
noncomputable def Tsh (tv : Bool → ℕ → ℕ → ℂ) (ε : Bool) (j : ℕ) : ℂ :=
  if ellOrb p p' r s ε j ≤ N then
    (Omega p p' r s k m true 0 ε j : ℂ) * tv ε j (N - ellOrb p p' r s ε j)
  else 0

end Shift

/-- The sign of the alternating chain: `μ_j = μ^{σ_j}_j`, `σ_j = +` for even `j`. -/
def sig (j : ℕ) : Bool := !(Nat.bodd j)

theorem sig_succ (j : ℕ) : sig (j + 1) = !sig j := by simp [sig, Nat.bodd_succ]

theorem sig_zero : sig 0 = true := rfl

theorem ellOrb_ge {p p' r s : ℕ} (hp : 0 < p) (hp' : 0 < p') (hr0 : 0 < r) (hr : r < p)
    (hs0 : 0 < s) (hs : s < p') : ∀ (j : ℕ) (ε : Bool), j ≤ ellOrb p p' r s ε j
  | 0, ε => Nat.zero_le _
  | j + 1, ε => by
    have h1 := ellOrb_ge hp hp' hr0 hr hs0 hs j ε
    have h2 := ellOrb_lt_succ hp hp' hr0 hr hs0 hs ε j ε
    omega

/-- Lemma 13.1 multiplied by `Ω(λ→μ) q^{μ-λ}` (l.3048–3054). -/
theorem scaled_step (h131 : Stmt_lem_degenerate_quotient_t) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) {k m : ℕ} (hk : k < min r (p - r))
    (hm : m < min s (p' - s)) (N : ℕ) (tv : Bool → ℕ → ℕ → ℂ)
    (htv : ∀ ε j M, IsIrrTrace (kacC b) (muOrb p p' r s ε j)
      (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) M (tv ε j M))
    (ε : Bool) (j : ℕ) (hj : j ≠ 0 ∨ ε = true) (ε₁ : Bool) :
    Tsh p p' r s k m N tv ε j + Tsh p p' r s k m N tv (!ε₁) (j + 1) =
      Fsh p p' r s k m b N ε j - Fsh p p' r s k m b N ε₁ (j + 1) := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hlt1 := ellOrb_lt_succ hp hp' hr0 hr hs0 hs ε j ε₁
  have hlt2 := ellOrb_lt_succ hp hp' hr0 hr hs0 hs ε j (!ε₁)
  by_cases hle : ellOrb p p' r s ε j ≤ N
  · have key := h131 p p' r s b hset k m hk hm ε j ε₁ (N - ellOrb p p' r s ε j)
      (tv ε j (N - ellOrb p p' r s ε j))
      (if ellOrb p p' r s (!ε₁) (j + 1) ≤ N then
        tv (!ε₁) (j + 1) (N - ellOrb p p' r s (!ε₁) (j + 1)) else 0)
      (htv ε j _)
      (fun hl => by
        rw [if_pos (by omega)]
        have e : N - ellOrb p p' r s ε j -
            (ellOrb p p' r s (!ε₁) (j + 1) - ellOrb p p' r s ε j) =
              N - ellOrb p p' r s (!ε₁) (j + 1) := by omega
        rw [e]
        exact htv _ _ _)
      (fun hl => by rw [if_neg (by omega)])
    have hc1 := omega_cocycle hset hk hm ε j hj ε₁
    have hc2 := omega_cocycle hset hk hm ε j hj (!ε₁)
    unfold Tsh Fsh
    rw [if_pos hle, if_pos hle]
    by_cases h1 : ellOrb p p' r s ε₁ (j + 1) ≤ N <;>
      by_cases h2 : ellOrb p p' r s (!ε₁) (j + 1) ≤ N
    · rw [if_pos h1, if_pos h2]
      rw [if_pos h2, if_pos (show ellOrb p p' r s ε₁ (j + 1) - ellOrb p p' r s ε j ≤
        N - ellOrb p p' r s ε j by omega)] at key
      have e : N - ellOrb p p' r s ε j - (ellOrb p p' r s ε₁ (j + 1) - ellOrb p p' r s ε j) =
          N - ellOrb p p' r s ε₁ (j + 1) := by omega
      rw [e] at key
      rw [← hc1, ← hc2]
      push_cast
      linear_combination (Omega p p' r s k m true 0 ε j : ℂ) * key
    · rw [if_pos h1, if_neg h2]
      rw [if_neg h2, if_pos (show ellOrb p p' r s ε₁ (j + 1) - ellOrb p p' r s ε j ≤
        N - ellOrb p p' r s ε j by omega)] at key
      have e : N - ellOrb p p' r s ε j - (ellOrb p p' r s ε₁ (j + 1) - ellOrb p p' r s ε j) =
          N - ellOrb p p' r s ε₁ (j + 1) := by omega
      rw [e] at key
      rw [← hc1]
      push_cast
      linear_combination (Omega p p' r s k m true 0 ε j : ℂ) * key
    · rw [if_neg h1, if_pos h2]
      rw [if_pos h2, if_neg (show ¬ (ellOrb p p' r s ε₁ (j + 1) - ellOrb p p' r s ε j ≤
        N - ellOrb p p' r s ε j) by omega)] at key
      rw [← hc2]
      push_cast
      linear_combination (Omega p p' r s k m true 0 ε j : ℂ) * key
    · rw [if_neg h1, if_neg h2]
      rw [if_neg h2, if_neg (show ¬ (ellOrb p p' r s ε₁ (j + 1) - ellOrb p p' r s ε j ≤
        N - ellOrb p p' r s ε j) by omega)] at key
      linear_combination (Omega p p' r s k m true 0 ε j : ℂ) * key
  · unfold Tsh Fsh
    rw [if_neg hle, if_neg hle, if_neg (by omega), if_neg (by omega)]
    ring

/-- The left-hand telescoping sum (l.3066–3069). -/
theorem telescope_left (A B C : ℕ → ℂ) (h : ∀ j, A j + A (j + 1) = B j - C j) :
    ∀ K : ℕ, ∑ j ∈ Finset.range (K + 1), (-1 : ℂ) ^ j * (B j - C j) =
      A 0 + (-1 : ℂ) ^ K * A (K + 1)
  | 0 => by simp [← h 0]
  | K + 1 => by
    rw [Finset.sum_range_succ, telescope_left A B C h K, ← h (K + 1), pow_succ]
    ring

/-- The right-hand sum (l.3069–3073): `B_j = F̃(μ_j)`, `C_j = F̃(μ^{σ_j}_{j+1})`. -/
theorem telescope_right (F : Bool → ℕ → ℂ) :
    ∀ K : ℕ, ∑ j ∈ Finset.range (K + 1), (-1 : ℂ) ^ j * (F (sig j) j - F (sig j) (j + 1)) =
      F true 0 + ∑ i ∈ Finset.Icc 1 K, (-1 : ℂ) ^ i * (F true i + F false i) -
        (-1 : ℂ) ^ K * F (sig K) (K + 1)
  | 0 => by simp [sig_zero]
  | K + 1 => by
    rw [Finset.sum_range_succ, telescope_right F K, Finset.sum_Icc_succ_top (by omega), sig_succ]
    have hsplit : F true (K + 1) + F false (K + 1) = F (sig K) (K + 1) + F (!sig K) (K + 1) := by
      cases sig K <;> simp [add_comm]
    rw [hsplit, pow_succ]
    ring

end Virasoro.P2
