import Virasoro.Proofs.Sec8DiagEll

/-!
# Lemma 8.7 (`lem:diagonal-values`)

Part (ii): with `w_γ = Top(a→μ) ℓ(γ)/(ς S_a N₀)^{D-1}`, the factors `K - S_a S_{x₁}` and
`K - S_{x_n} S_μ` are affine in `π_{x₁}`, `π_{x_n}` with linear coefficients `-N₀ S_a`, `-N₀ S_μ`;
the vanishing of Lemma 8.5(i) gives `∑_γ ℓ(γ) π_{x₁}^e π_{x_n}^{e'} = 0` for `e + e' ≤ D - 2`, and
for `k + j = D` only the terms of top degree remain:
`f_j(a,μ) = (-1)^{D-1} ∑_γ ℓ(γ) π_{x₁}^{D-1-j} π_{x_n}^j`.
-/

namespace Virasoro

open scoped LaurentSeries

/-- Expanding `(U - V π₁)^e (U' - V' π_n)^{e'}`: if the moments of lower total degree vanish, only
the top term remains. -/
theorem bimoment {K ι : Type*} [Field K] (s : Finset ι) (ℓ π1 πn : ι → K) (U V U' V' : K)
    (e e' : ℕ) (hlow : ∀ i i' : ℕ, i + i' < e + e' → ∑ γ ∈ s, ℓ γ * π1 γ ^ i * πn γ ^ i' = 0) :
    ∑ γ ∈ s, ℓ γ * (U - V * π1 γ) ^ e * (U' - V' * πn γ) ^ e' =
      (-V) ^ e * (-V') ^ e' * ∑ γ ∈ s, ℓ γ * π1 γ ^ e * πn γ ^ e' := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → K, c = fun i => (e.choose i : K) * U ^ (e - i) * (-V) ^ i := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c : ℕ → K, c = fun i => (e'.choose i : K) * U' ^ (e' - i) * (-V') ^ i :=
    ⟨_, rfl⟩
  have hx : ∀ γ, (U - V * π1 γ) ^ e = ∑ i ∈ Finset.range (e + 1), c i * π1 γ ^ i := by
    intro γ
    rw [show U - V * π1 γ = (-V) * π1 γ + U by ring, add_pow, hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hy : ∀ γ, (U' - V' * πn γ) ^ e' = ∑ i ∈ Finset.range (e' + 1), c' i * πn γ ^ i := by
    intro γ
    rw [show U' - V' * πn γ = (-V') * πn γ + U' by ring, add_pow, hc']
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hexp : ∑ γ ∈ s, ℓ γ * (U - V * π1 γ) ^ e * (U' - V' * πn γ) ^ e' =
      ∑ i ∈ Finset.range (e + 1), ∑ i' ∈ Finset.range (e' + 1),
        c i * c' i' * ∑ γ ∈ s, ℓ γ * π1 γ ^ i * πn γ ^ i' := by
    calc ∑ γ ∈ s, ℓ γ * (U - V * π1 γ) ^ e * (U' - V' * πn γ) ^ e'
        = ∑ γ ∈ s, ∑ i ∈ Finset.range (e + 1), ∑ i' ∈ Finset.range (e' + 1),
            c i * c' i' * (ℓ γ * π1 γ ^ i * πn γ ^ i') := by
          refine Finset.sum_congr rfl fun γ _ => ?_
          rw [hx, hy, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i' _ => ?_
          ring
      _ = ∑ i ∈ Finset.range (e + 1), ∑ γ ∈ s, ∑ i' ∈ Finset.range (e' + 1),
            c i * c' i' * (ℓ γ * π1 γ ^ i * πn γ ^ i') := Finset.sum_comm
      _ = ∑ i ∈ Finset.range (e + 1), ∑ i' ∈ Finset.range (e' + 1), ∑ γ ∈ s,
            c i * c' i' * (ℓ γ * π1 γ ^ i * πn γ ^ i') :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i ∈ Finset.range (e + 1), ∑ i' ∈ Finset.range (e' + 1),
            c i * c' i' * ∑ γ ∈ s, ℓ γ * π1 γ ^ i * πn γ ^ i' :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
            (Finset.mul_sum _ _ _).symm
  rw [hexp, Finset.sum_range_succ, Finset.sum_range_succ]
  have h1 : ∑ i ∈ Finset.range e, ∑ i' ∈ Finset.range (e' + 1),
      c i * c' i' * ∑ γ ∈ s, ℓ γ * π1 γ ^ i * πn γ ^ i' = 0 :=
    Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun i' hi' => by
      rw [Finset.mem_range] at hi hi'
      rw [hlow i i' (by omega), mul_zero]
  have h2 : ∑ i' ∈ Finset.range e', c e * c' i' * ∑ γ ∈ s, ℓ γ * π1 γ ^ e * πn γ ^ i' = 0 :=
    Finset.sum_eq_zero fun i' hi' => by
      rw [Finset.mem_range] at hi'
      rw [hlow e i' (by omega), mul_zero]
  rw [h1, h2, zero_add, zero_add, hc, hc']
  simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, one_mul]

/-- The moments of total degree `< d` vanish if the affine moments of total degree `< d` do. -/
theorem moments_vanish {K ι : Type*} [Field K] (s : Finset ι) (ℓ π1 πn : ι → K) (U V U' V' : K)
    (hV : V ≠ 0) (hV' : V' ≠ 0) (d : ℕ)
    (hX : ∀ e e' : ℕ, e + e' < d →
      ∑ γ ∈ s, ℓ γ * (U - V * π1 γ) ^ e * (U' - V' * πn γ) ^ e' = 0) :
    ∀ i i' : ℕ, i + i' < d → ∑ γ ∈ s, ℓ γ * π1 γ ^ i * πn γ ^ i' = 0 := by
  suffices H : ∀ n : ℕ, ∀ i i' : ℕ, i + i' = n → n < d →
      ∑ γ ∈ s, ℓ γ * π1 γ ^ i * πn γ ^ i' = 0 from fun i i' h => H _ i i' rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i i' hn hd
  have hb := bimoment s ℓ π1 πn U V U' V' i i'
    (fun a a' h => ih (a + a') (by omega) a a' rfl (by omega))
  rw [hX i i' (by omega)] at hb
  have hc : (-V) ^ i * (-V') ^ i' ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hV)) (pow_ne_zero _ (neg_ne_zero.2 hV'))
  exact (mul_eq_zero.1 hb.symm).resolve_left hc

theorem fval_alg {K : Type*} [Field K] {σ Sa Sm N M : K} (n j : ℕ) (hσ : σ ≠ 0) (hSa : Sa ≠ 0)
    (hSm : Sm ≠ 0) (hN : N ≠ 0) :
    (Sa / Sm) ^ j * (σ ^ (n + j) / (σ * Sa * N) ^ (n + j) *
      ((-(Sa * N)) ^ n * (-(N * Sm)) ^ j * M)) = (-1) ^ (n + j) * M := by
  have hX : (σ * Sa * N) ^ (n + j) * Sm ^ j ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hσ hSa) hN)) (pow_ne_zero _ hSm)
  have key : σ ^ (n + j) * Sa ^ j * (Sa * N) ^ n * (N * Sm) ^ j = (σ * Sa * N) ^ (n + j) * Sm ^ j := by
    ring
  calc (Sa / Sm) ^ j * (σ ^ (n + j) / (σ * Sa * N) ^ (n + j) *
        ((-(Sa * N)) ^ n * (-(N * Sm)) ^ j * M))
      = (-1) ^ n * (-1) ^ j * M * ((σ ^ (n + j) * Sa ^ j * (Sa * N) ^ n * (N * Sm) ^ j) *
          ((σ * Sa * N) ^ (n + j) * Sm ^ j)⁻¹) := by
        rw [div_pow, neg_pow, neg_pow (N * Sm)]
        ring
    _ = (-1) ^ (n + j) * M := by rw [key, mul_inv_cancel₀ hX, mul_one, pow_add]

/-- The last node before the end of a chain. -/
def penult : List Node → Node
  | [x₀, _] => x₀
  | _ :: l => penult l
  | [] => (true, 0)

/-- The class constant: `S_x = c + 2pp' π_x` with `c = cstQ (L_x mod 2)`. -/
def cstQ (p p' r s : ℕ) (q : ℕ) : ℚ :=
  if q = 0 then (p' : ℚ) * r - p * s else (p' : ℚ) * r + p * s - p * p'

variable {p p' r s : ℕ} {b : ℂ}

theorem penult_spec {μ : Node} : ∀ (l : List Node) (x : Node), StepsOK μ (x :: l) → l ≠ [] →
    chainHn p p' r s b (x :: l) = nodeH p p' r s b (penult (x :: l)) μ ∧
      (penult (x :: l)).2 < μ.2 ∧ (μ.2 - (penult (x :: l)).2) % 2 = 1
  | [], _, _, h => absurd rfl h
  | [y], x, hok, _ => by
    obtain ⟨h1, h2, h3⟩ := hok
    simp only [StepsOK] at h3
    subst h3
    exact ⟨rfl, h1, h2⟩
  | y :: z :: l', x, hok, _ => by
    obtain ⟨-, -, h3⟩ := hok
    exact penult_spec (z :: l') y h3 (List.cons_ne_nil _ _)

theorem nodeS_cls (x : Node) :
    (nodeS p p' r s x : ℂ) =
      ((cstQ p p' r s (x.2 % 2) : ℚ) : ℂ) + 2 * (p : ℂ) * p' * ((nodePos x : ℚ) : ℂ) := by
  have e : ((nodeS p p' r s x : ℤ) : ℚ) = cstQ p p' r s (x.2 % 2) + 2 * p * p' * nodePos x :=
    nodeS_pos x
  have := congrArg (fun q : ℚ => (q : ℂ)) e
  push_cast at this
  exact this

/-- The rational number `f_j(a,μ)` of Lemma 8.7(ii):
`(-1)^{D-1} ∑_γ ℓ(γ) π_{x₁}^{D-1-j} π_{x_n}^j`, and `f_0 = 1`. -/
def fVal (a μ : Node) (j : ℕ) : ℚ :=
  if j = 0 then 1 else
    (-1) ^ (μ.2 - a.2 - 1) * ∑ γ ∈ nodeChains a μ,
      ellC μ γ * nodePos (γ.tail.headD a) ^ (μ.2 - a.2 - 1 - j) * nodePos (penult γ) ^ j

/-- Lemma 8.7(ii). -/
theorem diag_values_ii (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hset : MinimalSetting p p' r s b) {a μ : Node} (haμ : a.2 < μ.2) (j : ℕ)
    (hj : j < μ.2 - a.2) :
    (j.factorial : Kd) * ((((nodeS p p' r s a : ℚ) / nodeS p p' r s μ) ^ j : ℚ) : Kd) *
        (nodeChain p p' r s b a μ (μ.2 - a.2 - j) j).coeff 0 =
      (fVal a μ j : Kd) * nodeTop p p' r s b a μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  · simp [fVal, nodeTop]
  have hreg := lem_chain_regular_of_cited hK hH
  obtain ⟨hvan, hval⟩ := node_leading_sums hreg hset haμ
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb0 := b_ne_zero_of hset
  have hσ : varsig p' b ≠ 0 := by
    unfold varsig
    exact div_ne_zero hb0 (mul_ne_zero two_ne_zero (pow_ne_zero 2 (by exact_mod_cast hp'.ne')))
  have hN : (2 * (p : ℂ) * p') ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hp.ne')) (by exact_mod_cast hp'.ne')
  have hSa : (nodeS p p' r s a : ℂ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset a
  have hSμ : (nodeS p p' r s μ : ℂ) ≠ 0 := by exact_mod_cast nodeS_ne_zero hset μ
  have hu : varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p') ≠ 0 :=
    mul_ne_zero (mul_ne_zero hσ hSa) hN
  have hTop : nodeTop p p' r s b a μ ≠ 0 := top_ne hK hH hset haμ
  obtain ⟨U, hU⟩ : ∃ U : ℂ, U = ((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) -
      (nodeS p p' r s a : ℂ) * ((cstQ p p' r s ((a.2 + 1) % 2) : ℚ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : ℂ, V = (nodeS p p' r s a : ℂ) * (2 * (p : ℂ) * p') := ⟨_, rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : ℂ, U' = ((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) -
      ((cstQ p p' r s ((μ.2 + 1) % 2) : ℚ) : ℂ) * (nodeS p p' r s μ : ℂ) := ⟨_, rfl⟩
  obtain ⟨V', hV'⟩ : ∃ V' : ℂ, V' = 2 * (p : ℂ) * p' * (nodeS p p' r s μ : ℂ) := ⟨_, rfl⟩
  have hV0 : V ≠ 0 := by rw [hV]; exact mul_ne_zero hSa hN
  have hV'0 : V' ≠ 0 := by rw [hV']; exact mul_ne_zero hN hSμ
  -- the first and the last slope of a chain
  have hchain : ∀ γ ∈ nodeChains a μ,
      chainH0 p p' r s b γ =
        pt (varsig p' b * (U - V * ((nodePos (γ.tail.headD a) : ℚ) : ℂ))) ∧
      chainHn p p' r s b γ =
        pt (varsig p' b * (U' - V' * ((nodePos (penult γ) : ℚ) : ℂ))) := by
    intro γ hγ
    obtain ⟨x, l, rfl, hlt, hodd, hok⟩ := stepsOK_of_mem hγ
    obtain ⟨hHn, hpl, hpo⟩ := penult_spec (p := p) (p' := p') (r := r) (s := s) (b := b)
      (x :: l) a ⟨hlt, hodd, hok⟩ (List.cons_ne_nil _ _)
    refine ⟨?_, ?_⟩
    · show nodeH p p' r s b a x = _
      unfold nodeH
      congr 2
      rw [nodeS_cls x, show x.2 % 2 = (a.2 + 1) % 2 by omega, hU, hV]
      simp only [List.tail_cons, List.headD_cons]
      ring
    · rw [hHn]
      unfold nodeH
      congr 2
      rw [nodeS_cls (penult (a :: x :: l)),
        show (penult (a :: x :: l)).2 % 2 = (μ.2 + 1) % 2 by omega, hU', hV']
      ring
  -- the sums of Lemma 8.5(i) in terms of the moments of `ℓ`
  have hsum : ∀ k j : ℕ, ∑ γ ∈ nodeChains a μ, chainW p p' r s b γ *
        chainH0 p p' r s b γ ^ (k - 1) * chainHn p p' r s b γ ^ j =
      nodeTop p p' r s b a μ * pt (varsig p' b ^ (k - 1 + j) /
        (varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (μ.2 - a.2 - 1) *
        ∑ γ ∈ nodeChains a μ, ((ellC μ γ : ℚ) : ℂ) *
          (U - V * ((nodePos (γ.tail.headD a) : ℚ) : ℂ)) ^ (k - 1) *
          (U' - V' * ((nodePos (penult γ) : ℚ) : ℂ)) ^ j) := by
    intro k j
    have h1 : ∀ γ ∈ nodeChains a μ, chainW p p' r s b γ *
        chainH0 p p' r s b γ ^ (k - 1) * chainHn p p' r s b γ ^ j =
        nodeTop p p' r s b a μ * pt (varsig p' b ^ (k - 1 + j) /
          (varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (μ.2 - a.2 - 1) *
          (((ellC μ γ : ℚ) : ℂ) * (U - V * ((nodePos (γ.tail.headD a) : ℚ) : ℂ)) ^ (k - 1) *
            (U' - V' * ((nodePos (penult γ) : ℚ) : ℂ)) ^ j)) := by
      intro γ hγ
      rw [chainW_eq hset hK hH _ a μ rfl γ hγ, (hchain γ hγ).1, (hchain γ hγ).2]
      simp only [pt, map_mul, map_pow, map_div₀]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, ← map_sum, Finset.mul_sum]
  -- vanishing of the affine moments, then of the moments
  have hMX : ∀ e e' : ℕ, e + e' < μ.2 - a.2 - 1 →
      ∑ γ ∈ nodeChains a μ, ((ellC μ γ : ℚ) : ℂ) *
        (U - V * ((nodePos (γ.tail.headD a) : ℚ) : ℂ)) ^ e *
        (U' - V' * ((nodePos (penult γ) : ℚ) : ℂ)) ^ e' = 0 := by
    intro e e' h
    have h0 := hvan (e + 1) e' (by omega) (by omega)
    rw [hsum (e + 1) e', Nat.add_sub_cancel] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd h hTop
    · have h' := RatFunc.C_injective (h.trans (map_zero _).symm)
      rcases mul_eq_zero.1 h' with h2 | h2
      · exact absurd h2 (div_ne_zero (pow_ne_zero _ hσ) (pow_ne_zero _ hu))
      · exact h2
  have hπ := moments_vanish (nodeChains a μ) (fun γ => ((ellC μ γ : ℚ) : ℂ))
    (fun γ => ((nodePos (γ.tail.headD a) : ℚ) : ℂ)) (fun γ => ((nodePos (penult γ) : ℚ) : ℂ))
    U V U' V' hV0 hV'0 (μ.2 - a.2 - 1) hMX
  have htop := bimoment (nodeChains a μ) (fun γ => ((ellC μ γ : ℚ) : ℂ))
    (fun γ => ((nodePos (γ.tail.headD a) : ℚ) : ℂ)) (fun γ => ((nodePos (penult γ) : ℚ) : ℂ))
    U V U' V' (μ.2 - a.2 - 1 - j) j (fun i i' h => hπ i i' (by omega))
  beta_reduce at htop
  -- the value
  rw [hval (μ.2 - a.2 - j) j (by omega) (by omega), hsum (μ.2 - a.2 - j) j,
    show μ.2 - a.2 - j - 1 = μ.2 - a.2 - 1 - j by omega, htop,
    fVal, if_neg (by omega), ← map_ratCast (RatFunc.C : ℂ →+* Kd),
    ← map_ratCast (RatFunc.C : ℂ →+* Kd)]
  obtain ⟨n, hn⟩ : ∃ n, μ.2 - a.2 - 1 = n + j := ⟨μ.2 - a.2 - 1 - j, by omega⟩
  rw [show μ.2 - a.2 - 1 - j = n by omega, hn]
  have hcx : (((((nodeS p p' r s a : ℚ) / nodeS p p' r s μ) ^ j : ℚ) : ℂ)) *
      (varsig p' b ^ (n + j) / (varsig p' b * nodeS p p' r s a * (2 * (p : ℂ) * p')) ^ (n + j) *
        ((-V) ^ n * (-V') ^ j * ∑ γ ∈ nodeChains a μ, ((ellC μ γ : ℚ) : ℂ) *
          ((nodePos (γ.tail.headD a) : ℚ) : ℂ) ^ n * ((nodePos (penult γ) : ℚ) : ℂ) ^ j)) =
      (((((-1) ^ (n + j) * ∑ γ ∈ nodeChains a μ, ellC μ γ * nodePos (γ.tail.headD a) ^ n *
          nodePos (penult γ) ^ j : ℚ)) : ℂ)) := by
    push_cast
    rw [hV, hV', mul_comm (nodeS p p' r s a : ℂ) (2 * (p : ℂ) * p')]
    rw [show (2 * (p : ℂ) * p' * (nodeS p p' r s a : ℂ)) = (nodeS p p' r s a : ℂ) * (2 * (p : ℂ) * p')
      by ring]
    exact fval_alg n j hσ hSa hSμ hN
  rw [← hcx, map_mul]
  have hf : (j.factorial : Kd) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  field_simp

/-- Lemma 8.7 (`lem:diagonal-values`), from the two cited results (through Theorem 7.14,
Lemma 7.13 and Proposition 8.6).

Paper label: lem:diagonal-values -/
theorem lem_diagonal_values_of_cited (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) : Stmt_lem_diagonal_values :=
  ⟨fun _ _ _ _ _ hset _ _ haμ k j hk hj hkj => diag_values_i hK hH hset haμ k j hk hj hkj,
    ⟨fVal, fun a μ => by simp [fVal],
      fun _ _ _ _ _ hset _ _ haμ j hj => diag_values_ii hK hH hset haμ j hj⟩⟩

end Virasoro
