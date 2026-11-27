import Virasoro.Proofs.Sec8BEll

/-!
# Section 8.2: Lemma 8.7(ii) at the boundary

With `w_γ = Top(μ_i→μ_k) ℓ(γ)/(-ε ς N₀ T_i)^{D-1}`, the first and the last slope of a chain are
`h_0 = ς(U - V π_{x₁})`, `h_n = ς(U' - V' π_{x_n})` with `U = K + ε T_i x₀`, `V = -ε T_i N₀`,
`U' = K + ε x₀ T_k`, `V' = -ε N₀ T_k`.  The vanishing of Lemma 8.5(i) at the boundary gives
`∑_γ ℓ(γ) π_{x₁}^e π_{x_n}^{e'} = 0` for `e + e' ≤ D - 2`, and for `k' + j = D` only the terms of
top degree remain: `j! (T_i/T_k)^j c^{(D-j)}_{μ_i→μ_k,j}(b⋆) = f_j(i,k) Top(μ_i→μ_k)`, where
`f_j(i,k) = (-1)^{D-1} ∑_γ ℓ(γ) π_{x₁}^{D-1-j} π_{x_n}^j` depends only on the positions `π`.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' x₀ : ℕ} {b : ℂ}

/-- The last slope of a chain is `h` of its last link. -/
theorem b_penult_spec {k : ℕ} : ∀ (l : List ℕ) (y x : ℕ), bSteps k (x :: l) →
    bChHn p p' x₀ b (y :: x :: l) = bH p p' x₀ b (bPenult (y :: x :: l)) k
  | [], y, x, h => by
    simp only [bSteps] at h
    subst h
    rfl
  | z :: l', y, x, h => by
    obtain ⟨-, h2⟩ := h
    exact b_penult_spec l' x z h2

theorem fvalB_alg {K : Type*} [Field K] {σ ε N Ti Tk V V' M : K} (n j : ℕ) (hσ : σ ≠ 0)
    (hε : ε ≠ 0) (hN : N ≠ 0) (hTi : Ti ≠ 0) (hTk : Tk ≠ 0) (hV : V = -(ε * Ti * N))
    (hV' : V' = -(ε * N * Tk)) :
    (Ti / Tk) ^ j * (σ ^ (n + j) / (-(ε * σ * N * Ti)) ^ (n + j) *
      ((-V) ^ n * (-V') ^ j * M)) = (-1) ^ (n + j) * M := by
  subst hV hV'
  have hX : Tk ^ j * (ε * σ * N * Ti) ^ (n + j) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hTk)
      (pow_ne_zero _ (mul_ne_zero (mul_ne_zero (mul_ne_zero hε hσ) hN) hTi))
  have key : Ti ^ j * σ ^ (n + j) * (ε * Ti * N) ^ n * (ε * N * Tk) ^ j =
      Tk ^ j * (ε * σ * N * Ti) ^ (n + j) := by ring
  calc (Ti / Tk) ^ j * (σ ^ (n + j) / (-(ε * σ * N * Ti)) ^ (n + j) *
        ((-(-(ε * Ti * N))) ^ n * (-(-(ε * N * Tk))) ^ j * M))
      = M * ((-1) ^ (n + j))⁻¹ * ((Ti ^ j * σ ^ (n + j) * (ε * Ti * N) ^ n * (ε * N * Tk) ^ j) *
          (Tk ^ j * (ε * σ * N * Ti) ^ (n + j))⁻¹) := by
        rw [div_pow, neg_pow (ε * σ * N * Ti), neg_neg, neg_neg]
        ring
    _ = (-1) ^ (n + j) * M := by
        rw [key, mul_inv_cancel₀ hX, mul_one]
        rcases neg_one_pow_eq_or K (n + j) with h | h <;> rw [h] <;> simp

/-- Lemma 8.7(ii) at the boundary. -/
theorem b_values_ii (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hB : BoundarySetting p p' x₀ b) {i k : ℕ} (hik : i < k) (j : ℕ) (hj : j < k - i) :
    (j.factorial : Kd) * ((((bT p p' x₀ i : ℚ) / bT p p' x₀ k) ^ j : ℚ) : Kd) *
        (bChain p p' x₀ b i k (k - i - j) j).coeff 0 =
      (fValB i k j : Kd) * bTop p p' x₀ b i k := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp [fValB, bTop]
  have hreg := lem_chain_regular_of_cited hK hH
  obtain ⟨hvan, hval⟩ := b_leading_sums hB hreg hik
  have hp : 0 < p := by have := hB.1; omega
  have hp' : 0 < p' := by have := hB.2.1; omega
  have hσ := varsig_ne hB
  have hε := bEps_ne hB
  have hN : (2 * (p : ℂ) * p') ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne')) (by exact_mod_cast hp'.ne')
  have hTi : (bT p p' x₀ i : ℂ) ≠ 0 := by exact_mod_cast bT_ne hB i
  have hTk : (bT p p' x₀ k : ℂ) ≠ 0 := by exact_mod_cast bT_ne hB k
  have hu : -((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ)) ≠ 0 :=
    neg_ne_zero.2 (mul_ne_zero (mul_ne_zero (mul_ne_zero hε hσ) hN) hTi)
  have hTop : bTop p p' x₀ b i k ≠ 0 := (b_thm_i hB hK hH hik).2.2
  obtain ⟨U, hU⟩ : ∃ U : ℂ, U = ((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) +
      (bEps p x₀ : ℂ) * (bT p p' x₀ i : ℂ) * (x₀ : ℂ) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℂ, V = -((bEps p x₀ : ℂ) * (bT p p' x₀ i : ℂ) * (2 * (p : ℂ) * p')) :=
    ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : ℂ, U' = ((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) +
      (bEps p x₀ : ℂ) * (x₀ : ℂ) * (bT p p' x₀ k : ℂ) := ⟨_, rfl⟩
  obtain ⟨V', hV'⟩ : ∃ V' : ℂ, V' = -((bEps p x₀ : ℂ) * (2 * (p : ℂ) * p') * (bT p p' x₀ k : ℂ)) :=
    ⟨_, rfl⟩
  have hV0 : V ≠ 0 := by rw [hV]; exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hε hTi) hN)
  have hV'0 : V' ≠ 0 := by rw [hV']; exact neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hε hN) hTk)
  have hTc : ∀ m : ℕ, (bT p p' x₀ m : ℂ) = (x₀ : ℂ) + (bPi m : ℂ) * (2 * (p : ℂ) * p') := by
    intro m; unfold bT; push_cast; ring
  -- the first and the last slope of a chain
  have hchain : ∀ γ ∈ bChains i k,
      bChH0 p p' x₀ b γ = pt (varsig p' b * (U - V * ((bPi (γ.tail.headD i) : ℚ) : ℂ))) ∧
      bChHn p p' x₀ b γ = pt (varsig p' b * (U' - V' * ((bPi (bPenult γ) : ℚ) : ℂ))) := by
    intro γ hγ
    obtain ⟨x, l, rfl, -, hst⟩ := b_steps_of_mem hγ
    refine ⟨?_, ?_⟩
    · show bH p p' x₀ b i x = _
      unfold bH
      congr 2
      simp only [List.tail_cons, List.headD_cons]
      rw [hU, hV, hTc x]
      push_cast
      ring
    · rw [b_penult_spec l i x hst]
      unfold bH
      congr 2
      rw [hU', hV', hTc (bPenult (i :: x :: l))]
      push_cast
      ring
  -- the sums of Lemma 8.5(i) in terms of the moments of `ℓ`
  have hsum : ∀ k' j : ℕ, ∑ γ ∈ bChains i k, bChW p p' x₀ b γ *
        bChH0 p p' x₀ b γ ^ (k' - 1) * bChHn p p' x₀ b γ ^ j =
      bTop p p' x₀ b i k * pt (varsig p' b ^ (k' - 1 + j) /
        (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ))) ^ (k - i - 1) *
        ∑ γ ∈ bChains i k, ((bEll k γ : ℚ) : ℂ) *
          (U - V * ((bPi (γ.tail.headD i) : ℚ) : ℂ)) ^ (k' - 1) *
          (U' - V' * ((bPi (bPenult γ) : ℚ) : ℂ)) ^ j) := by
    intro k' j
    have h1 : ∀ γ ∈ bChains i k, bChW p p' x₀ b γ *
        bChH0 p p' x₀ b γ ^ (k' - 1) * bChHn p p' x₀ b γ ^ j =
        bTop p p' x₀ b i k * pt (varsig p' b ^ (k' - 1 + j) /
          (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ))) ^
            (k - i - 1) *
          (((bEll k γ : ℚ) : ℂ) * (U - V * ((bPi (γ.tail.headD i) : ℚ) : ℂ)) ^ (k' - 1) *
            (U' - V' * ((bPi (bPenult γ) : ℚ) : ℂ)) ^ j)) := by
      intro γ hγ
      rw [bChW_eq hB hK hH _ i k rfl γ hγ, (hchain γ hγ).1, (hchain γ hγ).2]
      simp only [pt, map_mul, map_pow, map_div₀]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← map_sum, Finset.mul_sum]
  -- vanishing of the affine moments, then of the moments
  have hMX : ∀ e e' : ℕ, e + e' < k - i - 1 →
      ∑ γ ∈ bChains i k, ((bEll k γ : ℚ) : ℂ) *
        (U - V * ((bPi (γ.tail.headD i) : ℚ) : ℂ)) ^ e *
        (U' - V' * ((bPi (bPenult γ) : ℚ) : ℂ)) ^ e' = 0 := by
    intro e e' h
    have h0 := hvan (e + 1) e' (by omega) (by omega)
    rw [hsum (e + 1) e', Nat.add_sub_cancel] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hTop
    · have h' := RatFunc.C_injective (h.trans (map_zero _).symm)
      rcases mul_eq_zero.1 h' with h2 | h2
      · exact absurd h2 (div_ne_zero (pow_ne_zero _ hσ) (pow_ne_zero _ hu))
      · exact h2
  have hπ := moments_vanish (bChains i k) (fun γ => ((bEll k γ : ℚ) : ℂ))
    (fun γ => ((bPi (γ.tail.headD i) : ℚ) : ℂ)) (fun γ => ((bPi (bPenult γ) : ℚ) : ℂ))
    U V U' V' hV0 hV'0 (k - i - 1) hMX
  have htop := bimoment (bChains i k) (fun γ => ((bEll k γ : ℚ) : ℂ))
    (fun γ => ((bPi (γ.tail.headD i) : ℚ) : ℂ)) (fun γ => ((bPi (bPenult γ) : ℚ) : ℂ))
    U V U' V' (k - i - 1 - j) j (fun a a' h => hπ a a' (by omega))
  beta_reduce at htop
  -- the value
  rw [hval (k - i - j) j (by omega) (by omega), hsum (k - i - j) j,
    show k - i - j - 1 = k - i - 1 - j by omega, htop,
    fValB, if_neg (by omega), ← map_ratCast (RatFunc.C : ℂ →+* Kd),
    ← map_ratCast (RatFunc.C : ℂ →+* Kd)]
  obtain ⟨n, hn⟩ : ∃ n, k - i - 1 = n + j := ⟨k - i - 1 - j, by omega⟩
  rw [show k - i - 1 - j = n by omega, hn]
  have hcx : (((((bT p p' x₀ i : ℚ) / bT p p' x₀ k) ^ j : ℚ) : ℂ)) *
      (varsig p' b ^ (n + j) /
        (-((bEps p x₀ : ℂ) * varsig p' b * (2 * (p : ℂ) * p') * (bT p p' x₀ i : ℂ))) ^ (n + j) *
        ((-V) ^ n * (-V') ^ j * ∑ γ ∈ bChains i k, ((bEll k γ : ℚ) : ℂ) *
          ((bPi (γ.tail.headD i) : ℚ) : ℂ) ^ n * ((bPi (bPenult γ) : ℚ) : ℂ) ^ j)) =
      (((((-1) ^ (n + j) * ∑ γ ∈ bChains i k, bEll k γ * (bPi (γ.tail.headD i) : ℚ) ^ n *
          (bPi (bPenult γ) : ℚ) ^ j : ℚ)) : ℂ)) := by
    push_cast
    exact fvalB_alg n j hσ hε hN hTi hTk hV hV'
  rw [← hcx, map_mul]
  have hf : (j.factorial : Kd) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  field_simp

end Virasoro
