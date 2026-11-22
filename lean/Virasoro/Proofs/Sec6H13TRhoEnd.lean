import Virasoro.Proofs.Sec6H13TChain

/-!
# Proposition 6.8(ii): the `ρ̃` end is good (paper.tex l.1333–1366, l.1374–1378)

The normalized term `rhoN` with the factor `M^{\underline{w_b}}` taken out (`rhoN2`) is good from
the level `max(w_b, w_k)` on: the two descending factorials `(M−w_b)^{\underline{p₁+r}}` and
`(M−w_k)^{\underline{k+q+s}}` are polynomials in `M` vanishing on `[max(w_b,w_k), W')`, below the
level `W'` from which the three products have polynomial coefficients (root sets, l.1374–1378).
Its degree drop is at least `w_b` (`w_b ≥ 2ℓ_b`, all parts at least `2`) and its valuation at
least `max(w_b, p₁, r, q, s)`.
-/

namespace Virasoro.H13T

open Virasoro.H13D Virasoro.H13C Verma Finset

theorem good_cL (x : ℚ) : Good (fun _ => cL x) 0 0 := by
  have h := good_scalar (Polynomial.C x) (e := 0) (by simp)
  simpa using h

theorem good_dL (ν : Fin 2) : Good (fun _ => dL ν) (-2) (-2) := by
  unfold dL
  have h1 := good_mono (-1) 0 (-2)
  norm_num at h1
  exact h1.add ((good_cL (zeta ν)).mono (by norm_num) (by norm_num))

/-- The value at `(c, Δ, d)` of a polynomial of total degree at most `n`: `Good (−2n) (−2n)`. -/
theorem good_polyVal3 (ν : Fin 2) {x : LL} {n : ℕ} (hx : PolyVal3 cLc DL (dL ν) n x) :
    Good (fun _ => x) (-2 * n) (-2 * n) := by
  obtain ⟨P, hP, rfl⟩ := hx
  conv => enter [1, M]; rw [P.as_sum]
  simp only [map_sum]
  refine Good.sum _ fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_three]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, algebraMap_LL]
  have hdeg : m 0 + m 1 + m 2 ≤ n := by
    have h1 := MvPolynomial.le_totalDegree hm
    have h2 : m.sum (fun _ e => e) = m 0 + m 1 + m 2 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_three]
    omega
  have h1 := ((good_scalar (Polynomial.C (P.coeff m)) (e := 0) (by simp)).mul
    (((good_cLc.pow (m 0)).mul (good_DL.pow (m 1))).mul ((good_dL ν).pow (m 2))))
  simp only [Polynomial.eval_C] at h1
  refine (h1.mono ?_ ?_)
  · push_cast; nlinarith
  · push_cast; nlinarith

theorem good_prod_range {F : ℕ → ℕ → LL} {D V : ℤ} (k : ℕ) (h : ∀ u < k, Good (F u) D V) :
    Good (fun M => ∏ u ∈ range k, F u M) (k * D) (k * V) := by
  induction k with
  | zero => simpa using good_one
  | succ k ih =>
    have h1 := (ih fun u hu => h u (by omega)).mul (h k (by omega))
    have e1 : ((k + 1 : ℕ) : ℤ) * D = k * D + D := by push_cast; ring
    have e2 : ((k + 1 : ℕ) : ℤ) * V = k * V + V := by push_cast; ring
    rw [e1, e2]
    simpa only [prod_range_succ] using h1

/-- A factor `2Y + (M + c')t²` of `∏_{u<k}(2Y + (a_k−k+u)t²)`. -/
theorem good_kfac (c' : ℕ) :
    Good (fun M => mono 0 1 2 + cL (((M + c' : ℕ)) : ℚ) * mono 2 0 1) 2 2 := by
  have h1 := good_mono 0 1 2
  have h2 := (good_scalar (Polynomial.X + Polynomial.C (c' : ℚ)) (e := 1)
    (Polynomial.natDegree_X_add_C _).le).mul (good_mono 2 0 1)
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at h2
  push_cast
  exact (h1.mono (by norm_num) (by norm_num)).add (h2.mono (by norm_num) (by norm_num))

theorem two_length_le {μ : List ℕ} (hμ : ∀ y ∈ μ, 2 ≤ y) : 2 * μ.length ≤ μ.sum := by
  induction μ with
  | nil => simp
  | cons y t ih =>
    have h1 := hμ y (by simp)
    have h2 := ih fun z hz => hμ z (by simp [hz])
    simp only [List.length_cons, List.sum_cons]
    omega

theorem Good.congr {G G' : ℕ → LL} {D V : ℤ} (h : Good G D V) (hG : ∀ M, G' M = G M) :
    Good G' D V := by
  have : G' = G := funext hG
  rw [this]
  exact h

/-! ### The part with `M`-independent factors -/

/-- `rhoN` without its two descending factorials. -/
noncomputable def rhoR (ν : Fin 2) (μb μk : List ℕ) (M p1 r p2 q s : ℕ) : LL :=
  cL ((-1 : ℚ) ^ (μb.sum + μk.sum + p1 + p2 + q + s) /
      (2 ^ (μk.sum + p1 + p2 + 2 * (r - p2) + q + s) * (topNat μb μb : ℚ) * (p1.factorial : ℚ) *
        (p2.factorial : ℚ) * ((r - p2).factorial : ℚ) * (q.factorial : ℚ) * (s.factorial : ℚ))) *
  mono (μb.length + μk.length + p1 + p2 + q + s) ((μb.sum : ℤ) - μb.length) 1 *
  (∏ u ∈ range (M - μb.sum - p1 - r), (1 + cL ((1 + (u : ℚ) - zeta ν) / 2) * tL)) *
  (∏ i ∈ range (M - μk.sum - (r - p2) - q - s),
    (1 + cL ((((μb.sum + p1 + r : ℕ) : ℚ) - ((μk.sum + (r - p2) + q + s : ℕ) : ℚ) - zeta ν - i)
      / 2) * tL)) *
  (∏ u ∈ range (r - p2), (mono 0 1 2 + cL (((M - μk.sum - (r - p2) + u : ℕ)) : ℚ) * mono 2 0 1)) *
  torBr (pairing cLc DL (dL ν)) μb μk p1 s p2 q

theorem good_rhoR (ν : Fin 2) (μb μk : List ℕ) {p1 r p2 q s : ℕ} (hp : p2 ≤ r) :
    GF (fun M => rhoR ν μb μk M p1 r p2 q s) (max (μb.sum + p1 + r) (μk.sum + (r - p2) + q + s))
      (2 * ((p1 + r + q + s : ℕ) : ℤ) + 2 * ((μb.sum : ℤ) - μb.length))
      (2 * ((p1 + r + q + s : ℕ) : ℤ) + 2 * ((μb.sum : ℤ) - μb.length)) := by
  set W' := max (μb.sum + p1 + r) (μk.sum + (r - p2) + q + s) with hW'
  have h1 := good_prod ((1 - zeta ν) / 2) (1 / 2) (W' - μb.sum - p1 - r) 1 le_rfl 0 (by norm_num) 1
  have h2 := good_prod ((((μb.sum + p1 + r : ℕ) : ℚ) - ((μk.sum + (r - p2) + q + s : ℕ) : ℚ) -
    zeta ν) / 2) (-1 / 2) (W' - μk.sum - (r - p2) - q - s) 1 le_rfl 0 (by norm_num) 1
  have hk := good_prod_range (r - p2) (fun u _ => good_kfac (W' - μk.sum - (r - p2) + u))
  have ht := good_polyVal3 ν (torBr_deg (isPrimaryPairing_pairing (dL ν)) μb μk p1 s p2 q)
  have H := (((((good_cL ((-1 : ℚ) ^ (μb.sum + μk.sum + p1 + p2 + q + s) /
      (2 ^ (μk.sum + p1 + p2 + 2 * (r - p2) + q + s) * (topNat μb μb : ℚ) * (p1.factorial : ℚ) *
        (p2.factorial : ℚ) * ((r - p2).factorial : ℚ) * (q.factorial : ℚ) *
        (s.factorial : ℚ)))).mul
    (good_mono (μb.length + μk.length + p1 + p2 + q + s) ((μb.sum : ℤ) - μb.length) 1)).mul
    h1).mul h2).mul hk).mul ht
  show Good (fun M => rhoR ν μb μk (M + W') p1 r p2 q s) _ _
  refine Good.mono (Good.congr H (G' := fun M => rhoR ν μb μk (M + W') p1 r p2 q s)
    fun M => ?_) ?_ ?_
  rotate_left
  · push_cast; omega
  · push_cast; omega
  beta_reduce
  have e1 : ∏ u ∈ range (M + W' - μb.sum - p1 - r), (1 + cL ((1 + (u : ℚ) - zeta ν) / 2) * tL) =
      ∏ u ∈ range (M + (W' - μb.sum - p1 - r)),
        (1 + cL ((1 - zeta ν) / 2 + 1 / 2 * (u : ℚ)) * mono ((1 : ℕ) : ℤ) 0 1) := by
    rw [show M + W' - μb.sum - p1 - r = M + (W' - μb.sum - p1 - r) by omega]
    refine prod_congr rfl fun u _ => ?_
    rw [show (1 + (u : ℚ) - zeta ν) / 2 = (1 - zeta ν) / 2 + 1 / 2 * (u : ℚ) by ring]
    try rfl
  have e2 : ∏ i ∈ range (M + W' - μk.sum - (r - p2) - q - s),
      (1 + cL ((((μb.sum + p1 + r : ℕ) : ℚ) - ((μk.sum + (r - p2) + q + s : ℕ) : ℚ) - zeta ν - i)
        / 2) * tL) =
      ∏ i ∈ range (M + (W' - μk.sum - (r - p2) - q - s)),
        (1 + cL ((((μb.sum + p1 + r : ℕ) : ℚ) - ((μk.sum + (r - p2) + q + s : ℕ) : ℚ) -
          zeta ν) / 2 + -1 / 2 * (i : ℚ)) * mono ((1 : ℕ) : ℤ) 0 1) := by
    rw [show M + W' - μk.sum - (r - p2) - q - s = M + (W' - μk.sum - (r - p2) - q - s) by omega]
    refine prod_congr rfl fun i _ => ?_
    rw [show (((μb.sum + p1 + r : ℕ) : ℚ) - ((μk.sum + (r - p2) + q + s : ℕ) : ℚ) - zeta ν - i)
        / 2 = (((μb.sum + p1 + r : ℕ) : ℚ) - ((μk.sum + (r - p2) + q + s : ℕ) : ℚ) -
          zeta ν) / 2 + -1 / 2 * (i : ℚ) by ring]
    try rfl
  have e3 : ∏ u ∈ range (r - p2),
      (mono 0 1 2 + cL (((M + W' - μk.sum - (r - p2) + u : ℕ)) : ℚ) * mono 2 0 1) =
      ∏ u ∈ range (r - p2),
        (mono 0 1 2 + cL (((M + (W' - μk.sum - (r - p2) + u) : ℕ)) : ℚ) * mono 2 0 1) :=
    prod_congr rfl fun u _ => by
      rw [show M + W' - μk.sum - (r - p2) + u = M + (W' - μk.sum - (r - p2) + u) by omega]
  rw [rhoR, e1, e2, e3]

/-! ### Taking out `M^{\underline{w_b}}`: the root sets of the two descending factorials -/

theorem descFactorial_add_split (n a b : ℕ) :
    n.descFactorial (a + b) = n.descFactorial a * (n - a).descFactorial b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, Nat.descFactorial_succ, ih, Nat.descFactorial_succ,
      show n - (a + b) = n - a - b by omega]
    ring

theorem eval_desc (c k M : ℕ) (h : c ≤ M) :
    ((descPochhammer ℚ k).comp (Polynomial.X - Polynomial.C (c : ℚ))).eval (M : ℚ) =
      ((M - c).descFactorial k : ℚ) := by
  rw [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    ← Nat.cast_sub h, descPochhammer_eval_eq_descFactorial]

theorem natDegree_desc (c k : ℕ) :
    ((descPochhammer ℚ k).comp (Polynomial.X - Polynomial.C (c : ℚ))).natDegree ≤ k := by
  refine Polynomial.natDegree_comp_le.trans ?_
  rw [descPochhammer_natDegree, Polynomial.natDegree_X_sub_C, mul_one]

/-- `rhoN` with `M^{\underline{w_b}}` taken out. -/
noncomputable def rhoN2 (ν : Fin 2) (μb μk : List ℕ) (M p1 r p2 q s : ℕ) : LL :=
  cL ((((M - μb.sum).descFactorial (p1 + r) : ℕ) : ℚ) *
    (((M - μk.sum).descFactorial ((r - p2) + q + s) : ℕ) : ℚ)) * rhoR ν μb μk M p1 r p2 q s

theorem rhoN_eq (ν : Fin 2) (μb μk : List ℕ) (M p1 r p2 q s : ℕ) :
    rhoN ν μb μk M p1 r p2 q s =
      cL ((M.descFactorial μb.sum : ℕ) : ℚ) * rhoN2 ν μb μk M p1 r p2 q s := by
  have e : M.descFactorial (μb.sum + p1 + r) =
      M.descFactorial μb.sum * (M - μb.sum).descFactorial (p1 + r) := by
    rw [Nat.add_assoc, descFactorial_add_split]
  rw [rhoN, rhoN2, rhoR, e]
  simp only [Nat.cast_mul, map_mul]
  ring

/-- The box `p₁, r, q, s ≤ N`, `p₂ ≤ r` of indices `(p₁, r, p₂, q, s)`. -/
noncomputable def box (N : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  (range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).filter
    fun τ => τ.2.2.1 ≤ τ.2.1

def szB (τ : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := max τ.1 (max τ.2.1 (max τ.2.2.2.1 τ.2.2.2.2))

theorem mem_box {N : ℕ} {τ : ℕ × ℕ × ℕ × ℕ × ℕ} : τ ∈ box N ↔ τ.2.2.1 ≤ τ.2.1 ∧ szB τ ≤ N := by
  obtain ⟨p1, r, p2, q, s⟩ := τ
  simp only [box, szB, mem_filter, mem_product, mem_range]
  omega

theorem sum_box (N : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℕ → LL) :
    ∑ τ ∈ box N, f τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1 τ.2.2.2.2 =
    ∑ p1 ∈ range (N + 1), ∑ r ∈ range (N + 1), ∑ p2 ∈ range (N + 1), ∑ q ∈ range (N + 1),
      ∑ s ∈ range (N + 1), if p2 ≤ r then f p1 r p2 q s else 0 := by
  rw [box, sum_filter]
  simp only [sum_product]

/-- Each term of the box is good from `max(w_b, w_k)` on, with degree drop `w_b` and valuation
`max(w_b, p₁, r, q, s)`. -/
theorem good_rhoN2 (ν : Fin 2) (μb μk : List ℕ) (hμb : ∀ y ∈ μb, 2 ≤ y)
    {τ : ℕ × ℕ × ℕ × ℕ × ℕ} (hτ : τ.2.2.1 ≤ τ.2.1) :
    GF (fun M => rhoN2 ν μb μk M τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1 τ.2.2.2.2) (max μb.sum μk.sum)
      μb.sum (max μb.sum ((szB τ : ℕ) : ℤ)) := by
  obtain ⟨p1, r, p2, q, s⟩ := τ
  simp only [szB] at hτ ⊢
  have hl := two_length_le hμb
  set π := (descPochhammer ℚ (p1 + r)).comp (Polynomial.X - Polynomial.C (μb.sum : ℚ)) *
    (descPochhammer ℚ ((r - p2) + q + s)).comp (Polynomial.X - Polynomial.C (μk.sum : ℚ)) with hπd
  have hπ : π.natDegree ≤ (p1 + r) + ((r - p2) + q + s) :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add (natDegree_desc _ _) (natDegree_desc _ _))
  have hz : ∀ M : ℕ, max μb.sum μk.sum ≤ M →
      M < max (μb.sum + p1 + r) (μk.sum + (r - p2) + q + s) → π.eval (M : ℚ) = 0 := by
    intro M h1 h2
    rw [hπd, Polynomial.eval_mul, eval_desc _ _ _ (by omega), eval_desc _ _ _ (by omega)]
    by_cases hb : M < μb.sum + p1 + r
    · rw [(Nat.descFactorial_eq_zero_iff_lt).2 (by omega), Nat.cast_zero, zero_mul]
    · rw [(Nat.descFactorial_eq_zero_iff_lt (n := M - μk.sum)).2 (by omega), Nat.cast_zero,
        mul_zero]
  have h := GF.pi_mul π hπ (W₀ := max μb.sum μk.sum)
    (W := max (μb.sum + p1 + r) (μk.sum + (r - p2) + q + s)) (by omega) hz
    (good_rhoR ν μb μk hτ)
  refine (h.congr fun M hM => ?_).mono (by omega) (by omega)
  rw [rhoN2, hπd, Polynomial.eval_mul, eval_desc _ _ _ (by omega), eval_desc _ _ _ (by omega)]

/-! ### Reindexing the raw five-fold sum to the box -/

theorem sum_range_reflect' (f : ℕ → LL) (n : ℕ) :
    ∑ j ∈ range (n + 1), f (n - j) = ∑ j ∈ range (n + 1), f j := by
  have := sum_range_reflect f (n + 1)
  simpa using this

theorem sum_range_extend {f : ℕ → LL} {n N : ℕ} (hn : n ≤ N) (hf : ∀ j, n < j → f j = 0) :
    ∑ j ∈ range (n + 1), f j = ∑ j ∈ range (N + 1), f j :=
  sum_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega) fun j _ hj' =>
    hf j (by simp only [mem_range] at hj'; omega)

theorem sum_range_ite {r N : ℕ} (hr : r ≤ N) (F : ℕ → LL) :
    ∑ p ∈ range (r + 1), F p = ∑ p ∈ range (N + 1), if p ≤ r then F p else 0 := by
  rw [← sum_filter]
  congr 1
  ext p
  simp only [mem_filter, mem_range]
  omega

/-- The raw five-fold sum of `torus_ones_raw` (indices `p₁, m_L, p₂, q, m'`) is the box sum in
`(p₁, r, p₂, q, s)`, `r = a_r − p₁ − m_L`, `s = a₀ − k − q − m'`, `k = r − p₂`, for a summand
vanishing when `p₁ + r > a_r` or `k + q + s > a₀`. -/
theorem raw5_eq_box (f : ℕ → ℕ → ℕ → ℕ → ℕ → LL) {ar a0 N : ℕ} (har : ar ≤ N) (ha0 : a0 ≤ N)
    (hz1 : ∀ p1 r p2 q s, ar < p1 + r → f p1 r p2 q s = 0)
    (hz2 : ∀ p1 r p2 q s, p2 ≤ r → a0 < r - p2 + q + s → f p1 r p2 q s = 0) :
    ∑ p1 ∈ range (ar + 1), ∑ mL ∈ range (ar - p1 + 1), ∑ p2 ∈ range (ar - p1 - mL + 1),
      ∑ q ∈ range (a0 - (ar - p1 - mL - p2) + 1),
        ∑ m' ∈ range (a0 - (ar - p1 - mL - p2) - q + 1),
          f p1 (p2 + (ar - p1 - mL - p2)) p2 q (a0 - (ar - p1 - mL - p2) - q - m') =
    ∑ p1 ∈ range (N + 1), ∑ r ∈ range (N + 1), ∑ p2 ∈ range (N + 1), ∑ q ∈ range (N + 1),
      ∑ s ∈ range (N + 1), if p2 ≤ r then f p1 r p2 q s else 0 := by
  have hA : ∀ p1 R p2, p2 ≤ R →
      ∑ q ∈ range (a0 - (R - p2) + 1), ∑ m' ∈ range (a0 - (R - p2) - q + 1),
        f p1 (p2 + (R - p2)) p2 q (a0 - (R - p2) - q - m') =
      ∑ q ∈ range (N + 1), ∑ s ∈ range (N + 1), f p1 R p2 q s := by
    intro p1 R p2 hp2
    rw [Nat.add_sub_cancel' hp2]
    have h1 : ∀ q, ∑ m' ∈ range (a0 - (R - p2) - q + 1), f p1 R p2 q (a0 - (R - p2) - q - m') =
        ∑ s ∈ range (N + 1), f p1 R p2 q s := fun q =>
      (sum_range_reflect' (fun s => f p1 R p2 q s) _).trans
        (sum_range_extend (by omega) fun s hs => hz2 p1 R p2 q s hp2 (by omega))
    refine (sum_congr rfl fun q _ => h1 q).trans ?_
    exact sum_range_extend (by omega) fun q hq =>
      sum_eq_zero fun s _ => hz2 p1 R p2 q s hp2 (by omega)
  have hB : ∀ p1, p1 ≤ ar →
      ∑ mL ∈ range (ar - p1 + 1), ∑ p2 ∈ range (ar - p1 - mL + 1),
        ∑ q ∈ range (a0 - (ar - p1 - mL - p2) + 1),
          ∑ m' ∈ range (a0 - (ar - p1 - mL - p2) - q + 1),
            f p1 (p2 + (ar - p1 - mL - p2)) p2 q (a0 - (ar - p1 - mL - p2) - q - m') =
      ∑ r ∈ range (N + 1), ∑ p2 ∈ range (N + 1), ∑ q ∈ range (N + 1),
        ∑ s ∈ range (N + 1), if p2 ≤ r then f p1 r p2 q s else 0 := by
    intro p1 hp1
    have h1 : ∀ mL, ∑ p2 ∈ range (ar - p1 - mL + 1),
          ∑ q ∈ range (a0 - (ar - p1 - mL - p2) + 1),
          ∑ m' ∈ range (a0 - (ar - p1 - mL - p2) - q + 1),
            f p1 (p2 + (ar - p1 - mL - p2)) p2 q (a0 - (ar - p1 - mL - p2) - q - m') =
        ∑ p2 ∈ range (ar - p1 - mL + 1), ∑ q ∈ range (N + 1), ∑ s ∈ range (N + 1),
          f p1 (ar - p1 - mL) p2 q s := fun mL =>
      sum_congr rfl fun p2 hp2 => hA p1 (ar - p1 - mL) p2 (Nat.lt_succ_iff.1 (mem_range.1 hp2))
    refine (sum_congr rfl fun mL _ => h1 mL).trans ?_
    refine (sum_range_reflect' (fun R => ∑ p2 ∈ range (R + 1), ∑ q ∈ range (N + 1),
      ∑ s ∈ range (N + 1), f p1 R p2 q s) (ar - p1)).trans ?_
    refine (sum_range_extend (n := ar - p1) (N := N) (by omega) fun R hR => sum_eq_zero fun p2 _ =>
      sum_eq_zero fun q _ =>
      sum_eq_zero fun s _ => hz1 p1 R p2 q s (by omega)).trans ?_
    refine sum_congr rfl fun R hR => ?_
    rw [sum_range_ite (Nat.lt_succ_iff.1 (mem_range.1 hR))]
    refine sum_congr rfl fun p2 _ => ?_
    split_ifs with h <;> simp [h]
  refine (sum_congr rfl fun p1 hp1 => hB p1 (Nat.lt_succ_iff.1 (mem_range.1 hp1))).trans ?_
  exact sum_range_extend har fun p1 hp1 => sum_eq_zero fun r _ => sum_eq_zero fun p2 _ =>
    sum_eq_zero fun q _ => sum_eq_zero fun s _ => by rw [hz1 p1 r p2 q s (by omega), ite_self]

end Virasoro.H13T
