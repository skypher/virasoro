import Virasoro.Proofs.P2Sec9GenRC3
import Virasoro.Proofs.TopLayerArith

/-!
# Theorem 9.3(c): `σ^±_j/γ^±_j = Ω_{u,v}(λ→μ^±_j)` (paper.tex l.1954–1959, 3089–3105)

The scaled two-term identities give, by downward induction on the layer, the inverse form of
(9.3): `F̃(μ) = ∑_{ν ⪰ μ} T̃(ν)`; at `μ = λ`,
`F_N(c⋆,λ,d) = T^irr_N(λ) + ∑_{j,±} Ω(λ→μ^±_j) T^irr_{N-ℓ^±_j}(μ^±_j)` (the paper writes this
through the unitriangular zeta matrix of the braided poset, l.3091–3100).  Compared with the
Jantzen-vertex decomposition of Proposition 11.2(ii) in increasing order of the pairwise distinct
levels `ℓ^±_j`, with `T^irr_0 = 1`, it gives `σ^±_j/γ^±_j = Ω(λ→μ^±_j)`.
-/

namespace Virasoro.P2

open Virasoro

/-- The inverse form of (9.3) at a node of layer `j ≤ N` (l.3091–3100). -/
theorem inv_formula (h131 : Stmt_lem_degenerate_quotient_t) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) {k m : ℕ} (hk : k < min r (p - r))
    (hm : m < min s (p' - s)) (N : ℕ) (tv : Bool → ℕ → ℕ → ℂ)
    (htv : ∀ ε j M, IsIrrTrace (kacC b) (muOrb p p' r s ε j)
      (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) M (tv ε j M)) :
    ∀ d : ℕ, d ≤ N → ∀ ε : Bool, (N - d ≠ 0 ∨ ε = true) →
      Fsh p p' r s k m b N ε (N - d) = Tsh p p' r s k m N tv ε (N - d) +
        ∑ i ∈ Finset.Ioc (N - d) N, (Tsh p p' r s k m N tv true i + Tsh p p' r s k m N tv false i) := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hge := ellOrb_ge hp hp' hr0 hr hs0 hs
  have hT1 : ∀ ε, Tsh p p' r s k m N tv ε (N + 1) = 0 := fun ε => by
    unfold Tsh; rw [if_neg (by have := hge (N + 1) ε; omega)]
  have hF1 : ∀ ε, Fsh p p' r s k m b N ε (N + 1) = 0 := fun ε => by
    unfold Fsh; rw [if_neg (by have := hge (N + 1) ε; omega)]
  intro d
  induction d with
  | zero =>
    intro _ ε hε
    have h := scaled_step h131 hset hk hm N tv htv ε N (by simpa using hε) true
    rw [hT1, hF1] at h
    simp only [Nat.sub_zero, Finset.Ioc_self, Finset.sum_empty, add_zero]
    linear_combination -h
  | succ d ih =>
    intro hd ε hε
    have hj : N - (d + 1) + 1 = N - d := by omega
    have h := scaled_step h131 hset hk hm N tv htv ε (N - (d + 1)) hε true
    rw [hj] at h
    have h2 := ih (by omega) true (Or.inr rfl)
    have hI : Finset.Ioc (N - (d + 1)) N = insert (N - d) (Finset.Ioc (N - d) N) := by
      ext x
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    rw [hI, Finset.sum_insert (by simp)]
    rw [h2] at h
    simp only [Bool.not_true] at h
    linear_combination -h

/-- `T^irr_0 = 1` at every orbit node (Lemma 13.1 at level `0`, `F_0 = 1`). -/
theorem irrTrace_zero_orbit (h131 : Stmt_lem_degenerate_quotient_t) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) {k m : ℕ} (hk : k < min r (p - r))
    (hm : m < min s (p' - s)) (ε : Bool) (j : ℕ) {T : ℂ}
    (hT : IsIrrTrace (kacC b) (muOrb p p' r s ε j) (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
      0 T) : T = 1 := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hlt1 := ellOrb_lt_succ hp hp' hr0 hr hs0 hs ε j true
  have hlt2 := ellOrb_lt_succ hp hp' hr0 hr hs0 hs ε j (!true)
  have h := h131 p p' r s b hset k m hk hm ε j true 0 T 0 hT (fun h => absurd h (by omega))
    (fun _ => rfl)
  simp only [mul_zero, add_zero] at h
  rw [h, if_neg (by omega), sub_zero, FvalAt, Frat_zero]
  simp

/-- Distinct orbit levels: `ℓ^ε_i = ℓ^{ε'}_{i'}` with `i, i' ≥ 1` forces `(ε,i) = (ε',i')`. -/
theorem ellOrb_inj {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) {ε ε' : Bool}
    {i i' : ℕ} (hi : 1 ≤ i) (hi' : 1 ≤ i')
    (h : ellOrb p p' r s ε i = ellOrb p p' r s ε' i') : ε = ε' ∧ i = i' := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hbsq⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hmono : ∀ (a : ℕ) (c c' : Bool) (n : ℕ), ellOrb p p' r s c a < ellOrb p p' r s c' (a + n + 1) := by
    intro a c c' n
    induction n with
    | zero => exact ellOrb_lt_succ hp hp' hr0 hr hs0 hs c a c'
    | succ n ihn =>
      exact ihn.trans (ellOrb_lt_succ hp hp' hr0 hr hs0 hs c' (a + n + 1) c')
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · exfalso
    obtain ⟨n, rfl⟩ : ∃ n, i' = i + n + 1 := ⟨i' - i - 1, by omega⟩
    exact absurd h (ne_of_lt (hmono i ε ε' n))
  · subst heq
    refine ⟨?_, rfl⟩
    by_contra hne
    have hpm := ellPlus_ne_ellMinus hcop hr0 hr hs hn1 hi
    have hT : ellOrb p p' r s true i = ellPlus p p' r s i := by
      simp [ellOrb, Nat.pos_iff_ne_zero.1 hi]
    have hF : ellOrb p p' r s false i = ellMinus p p' r s i := by
      simp [ellOrb, Nat.pos_iff_ne_zero.1 hi]
    cases ε <;> cases ε'
    · exact hne rfl
    · rw [hF, hT] at h; exact hpm h.symm
    · rw [hT, hF] at h; exact hpm h
    · exact hne rfl
  · exfalso
    obtain ⟨n, rfl⟩ : ∃ n, i = i' + n + 1 := ⟨i - i' - 1, by omega⟩
    exact absurd h.symm (ne_of_lt (hmono i' ε' ε n))

end Virasoro.P2
