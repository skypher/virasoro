import Virasoro.Proofs.Sec6H13ChainOps
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.NoncommRing

/-!
# Proposition 6.8(ii): the degree of the local bracket (paper.tex l.1322–1332)

Every part of `μ'` is at least `2` and `[L_1, L_n]` introduces no central charge, so each term of
`ad(L_1)^p(L_μ L_{−μ'}) L_{−1}^q` has at most `ℓ(μ) + ⌊p/2⌋` non-negative modes (`H13C.InW`: the
count `wt2` gives `2` to a non-negative mode and `1` to `L_{−1}`, and `ad(L_1)` raises it by at
most `1`).  Moving the rightmost non-negative mode to the right shows by induction that a vacuum
expectation of a word with `n` non-negative modes is a polynomial in `(c, Δ)` of total degree at
most `n` (`H13C.ev_opZ_polyVal`).  Together: `d_Δ + d_c ≤ ℓ(μ) + p/2` on every monomial of the
bracket (`H13C.locBr_polyVal`).
-/

namespace Virasoro.H13C

open Verma

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

/-! ### Values that are polynomials in `(c, Δ)` of bounded total degree -/

/-- `x` is the value at `(c, Δ)` of a polynomial of total degree at most `n`. -/
def PolyVal (c h : R) (n : ℕ) (x : R) : Prop :=
  ∃ P : MvPolynomial (Fin 2) ℚ, P.totalDegree ≤ n ∧ MvPolynomial.aeval ![c, h] P = x

theorem PolyVal.mono {n n' : ℕ} {x : R} (hx : PolyVal c h n x) (hn : n ≤ n') : PolyVal c h n' x :=
  let ⟨P, h1, h2⟩ := hx
  ⟨P, h1.trans hn, h2⟩

theorem PolyVal.zero (n : ℕ) : PolyVal c h n 0 :=
  ⟨0, by simp, map_zero _⟩

theorem PolyVal.one (n : ℕ) : PolyVal c h n 1 :=
  ⟨1, by simp, map_one _⟩

theorem PolyVal.add {n : ℕ} {x y : R} (hx : PolyVal c h n x) (hy : PolyVal c h n y) :
    PolyVal c h n (x + y) := by
  obtain ⟨P, h1, h2⟩ := hx
  obtain ⟨Q, h3, h4⟩ := hy
  exact ⟨P + Q, (MvPolynomial.totalDegree_add P Q).trans (max_le h1 h3), by rw [map_add, h2, h4]⟩

theorem PolyVal.smulQ {n : ℕ} {x : R} (hx : PolyVal c h n x) (q : ℚ) :
    PolyVal c h n (algebraMap ℚ R q * x) := by
  obtain ⟨P, h1, h2⟩ := hx
  refine ⟨MvPolynomial.C q * P, ?_, by rw [map_mul, MvPolynomial.aeval_C, h2]⟩
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact h1

theorem PolyVal.intMul {n : ℕ} {x : R} (hx : PolyVal c h n x) (z : ℤ) :
    PolyVal c h n ((z : R) * x) := by
  have := hx.smulQ (z : ℚ)
  rwa [map_intCast] at this

theorem PolyVal.mulH {n : ℕ} {x : R} (hx : PolyVal c h n x) : PolyVal c h (n + 1) (h * x) := by
  obtain ⟨P, h1, h2⟩ := hx
  refine ⟨MvPolynomial.X 1 * P, ?_, by rw [map_mul, MvPolynomial.aeval_X, h2]; rfl⟩
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, add_comm]
  exact Nat.add_le_add_right h1 1

theorem PolyVal.mulC {n : ℕ} {x : R} (hx : PolyVal c h n x) : PolyVal c h (n + 1) (c * x) := by
  obtain ⟨P, h1, h2⟩ := hx
  refine ⟨MvPolynomial.X 0 * P, ?_, by rw [map_mul, MvPolynomial.aeval_X, h2]; rfl⟩
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_X, add_comm]
  exact Nat.add_le_add_right h1 1

/-! ### Vacuum expectations of words in the modes -/

/-- The product `L_{w₁} ⋯ L_{w_n}` of a word of integers. -/
noncomputable def opZ (c : R) (w : List ℤ) : VirEnv R c := (w.map (VirEnv.L c)).prod

theorem opZ_nil : opZ c [] = 1 := rfl

theorem opZ_cons (a : ℤ) (w : List ℤ) : opZ c (a :: w) = VirEnv.L c a * opZ c w := by
  rw [opZ, List.map_cons, List.prod_cons]
  rfl

theorem opZ_append (u v : List ℤ) : opZ c (u ++ v) = opZ c u * opZ c v := by
  rw [opZ, List.map_append, List.prod_append]
  rfl

/-- `⟨Δ| x |Δ⟩`. -/
noncomputable def ev (c h : R) (x : VirEnv R c) : R := vacuum c h (x • (hw : Verma R c h))

theorem smul_hw (x : VirEnv R c) : x • (hw : Verma R c h) = mk x := by
  rw [hw_eq, env_smul_mk, mul_one]

theorem ev_zero : ev c h 0 = 0 := by
  have e : (0 : VirEnv R c) • (hw : Verma R c h) = 0 := zero_smul _ _
  rw [ev, e, map_zero]

theorem ev_add (x y : VirEnv R c) : ev c h (x + y) = ev c h x + ev c h y := by
  have e := add_smul x y (hw : Verma R c h)
  rw [ev, e, map_add]
  rfl

theorem ev_smul (r : R) (x : VirEnv R c) : ev c h (r • x) = r * ev c h x := by
  rw [ev, ev, smul_hw, smul_hw, ← smul_mk, map_smul, smul_eq_mul]

theorem ev_zsmul (z : ℤ) (x : VirEnv R c) : ev c h (z • x) = (z : R) * ev c h x := by
  rw [← Int.cast_smul_eq_zsmul R z x, ev_smul]

theorem ev_one : ev c h 1 = 1 := by
  rw [ev, one_smul]
  exact (isVacuum_vacuum (c := c) (h := h)).1

theorem ev_neg_mode {a : ℤ} (ha : a < 0) (x : VirEnv R c) : ev c h (VirEnv.L c a * x) = 0 := by
  rw [ev, mul_smul]
  exact (isVacuum_vacuum (c := c) (h := h)).2 a ha _

theorem ev_mul_pos {k : ℤ} (hk : 0 < k) (x : VirEnv R c) : ev c h (x * VirEnv.L c k) = 0 := by
  have e : VirEnv.L c k • (hw : Verma R c h) = 0 := L_hw_pos hk
  rw [ev, mul_smul, e, smul_zero, map_zero]

theorem ev_mul_zero (x : VirEnv R c) : ev c h (x * VirEnv.L c 0) = h * ev c h x := by
  have e : VirEnv.L c 0 • (hw : Verma R c h) = h • hw := L_hw_zero
  rw [ev, mul_smul, e, smul_comm, map_smul, smul_eq_mul]
  rfl

/-- `L_k L_y = L_y L_k + (k − y) L_{k+y} + (c/12)(k³ − k) δ_{k+y,0}` inside a word. -/
theorem opZ_swap (u v : List ℤ) (k y : ℤ) :
    opZ c (u ++ k :: y :: v) = opZ c (u ++ y :: k :: v) +
      ((k - y : ℤ) : R) • opZ c (u ++ (k + y) :: v) +
      (if k + y = 0 then centralTerm c k • opZ c (u ++ v) else 0) := by
  simp only [opZ_append, opZ_cons]
  rw [← mul_assoc (VirEnv.L c k), VirEnv.L_mul_L]
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_assoc]
  · simp only [add_zero, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, mul_assoc]

/-- The number of non-negative modes of a word. -/
def nn (w : List ℤ) : ℕ := w.countP fun x => decide (0 ≤ x)

theorem nn_append (u v : List ℤ) : nn (u ++ v) = nn u + nn v := List.countP_append ..

theorem nn_cons_nonneg {k : ℤ} (hk : 0 ≤ k) (w : List ℤ) : nn (k :: w) = nn w + 1 :=
  List.countP_cons_of_pos (by simpa using hk)

theorem nn_cons_neg {k : ℤ} (hk : k < 0) (w : List ℤ) : nn (k :: w) = nn w :=
  List.countP_cons_of_neg (by simpa using hk)

theorem nn_cons_le (k : ℤ) (w : List ℤ) : nn (k :: w) ≤ nn w + 1 := by
  rcases lt_or_ge k 0 with hk | hk
  · rw [nn_cons_neg hk]
    exact Nat.le_succ _
  · rw [nn_cons_nonneg hk]

/-- A word is all negative, or has a rightmost non-negative mode. -/
theorem word_cases (w : List ℤ) :
    (∀ x ∈ w, x < 0) ∨ ∃ u k v, w = u ++ k :: v ∧ 0 ≤ k ∧ ∀ x ∈ v, x < 0 := by
  induction w with
  | nil => exact Or.inl (by simp)
  | cons a w ih =>
    rcases ih with ih | ⟨u, k, v, rfl, hk, hv⟩
    · rcases lt_or_ge a 0 with ha | ha
      · exact Or.inl fun x hx => by
          rcases List.mem_cons.1 hx with rfl | hx
          · exact ha
          · exact ih x hx
      · exact Or.inr ⟨[], a, w, rfl, ha, ih⟩
    · exact Or.inr ⟨a :: u, k, v, rfl, hk, hv⟩

/-- Moving the rightmost non-negative mode to the right (paper.tex l.1329–1330). -/
theorem ev_opZ_step (n : ℕ)
    (IH : ∀ w : List ℤ, w.length < n → PolyVal c h (nn w) (ev c h (opZ c w))) :
    ∀ (v : List ℤ), (∀ x ∈ v, x < 0) → ∀ (u : List ℤ) (k : ℤ), 0 ≤ k →
      (u ++ k :: v).length = n → PolyVal c h (nn (u ++ k :: v)) (ev c h (opZ c (u ++ k :: v))) := by
  intro v
  induction v with
  | nil =>
    intro _ u k hk hlen
    have hu : u.length < n := by
      rw [List.length_append] at hlen
      simp at hlen
      omega
    rw [nn_append, nn_cons_nonneg hk, opZ_append, opZ_cons, opZ_nil, mul_one]
    rcases hk.lt_or_eq with hk | rfl
    · rw [ev_mul_pos hk]
      exact PolyVal.zero _
    · rw [ev_mul_zero]
      exact (IH u hu).mulH
  | cons y v ih =>
    intro hv u k hk hlen
    have hy : y < 0 := hv y (List.mem_cons_self ..)
    have hv' : ∀ x ∈ v, x < 0 := fun x hx => hv x (List.mem_cons_of_mem _ hx)
    have hlen' : u.length + v.length + 2 = n := by
      rw [List.length_append] at hlen
      simp at hlen
      omega
    have hnn : nn (u ++ k :: y :: v) = nn u + nn v + 1 := by
      rw [nn_append, nn_cons_nonneg hk, nn_cons_neg hy]
      ring
    rw [opZ_swap, ev_add, ev_add, ev_smul, hnn]
    refine (PolyVal.add ?_ ?_).add ?_
    · have h1 := ih hv' (u ++ [y]) k hk (by simp; omega)
      rw [List.append_assoc, List.singleton_append] at h1
      have e : nn (u ++ y :: k :: v) = nn u + nn v + 1 := by
        rw [nn_append, nn_cons_neg hy, nn_cons_nonneg hk]
        ring
      rwa [e] at h1
    · have h1 := IH (u ++ (k + y) :: v) (by simp; omega)
      refine (h1.mono ?_).intMul _
      rw [nn_append]
      have := nn_cons_le (k + y) v
      omega
    · split_ifs with h0
      · have h1 := IH (u ++ v) (by simp; omega)
        rw [ev_smul, centralTerm, mul_assoc]
        rw [nn_append] at h1
        exact h1.mulC.smulQ _
      · rw [ev_zero]
        exact PolyVal.zero _

/-- A vacuum expectation of a word with `n` non-negative modes is a polynomial in `(c, Δ)` of
total degree at most `n` (paper.tex l.1329–1332). -/
theorem ev_opZ_polyVal (w : List ℤ) : PolyVal c h (nn w) (ev c h (opZ c w)) := by
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n IH =>
    have IH' : ∀ w' : List ℤ, w'.length < n → PolyVal c h (nn w') (ev c h (opZ c w')) :=
      fun w' hw' => IH w'.length hw' w' rfl
    rcases word_cases w with hneg | ⟨u, k, v, rfl, hk, hv⟩
    · cases w with
      | nil =>
        rw [opZ_nil, ev_one]
        exact PolyVal.one _
      | cons a w =>
        rw [opZ_cons, ev_neg_mode (hneg a (List.mem_cons_self ..))]
        exact PolyVal.zero _
    · exact ev_opZ_step n IH' v hv u k hk hn

/-! ### The modes of `ad(L_1)^p(L_μ L_{−μ'})` (l.1325–1329) -/

/-- `2` for a non-negative mode, `1` for `L_{−1}`, `0` for `L_n`, `n ≤ −2`. -/
def f2 (a : ℤ) : ℕ := if 0 ≤ a then 2 else if a = -1 then 1 else 0

/-- The sum of `f2` over the modes of a word. -/
def wt2 (w : List ℤ) : ℕ := (w.map f2).sum

theorem f2_succ_le (a : ℤ) : f2 (1 + a) ≤ f2 a + 1 := by
  unfold f2
  split_ifs <;> omega

theorem two_nn_le (w : List ℤ) : 2 * nn w ≤ wt2 w := by
  induction w with
  | nil => simp [nn, wt2]
  | cons a w ih =>
    have e : wt2 (a :: w) = f2 a + wt2 w := by simp [wt2]
    rcases lt_or_ge a 0 with ha | ha
    · rw [nn_cons_neg ha, e]
      omega
    · rw [nn_cons_nonneg ha, e, f2, if_pos ha]
      omega

/-- Integer combinations of words `w` with `wt2 w ≤ m`. -/
inductive InW (c : R) : ℕ → VirEnv R c → Prop
  | word (m : ℕ) (w : List ℤ) : wt2 w ≤ m → InW c m (opZ c w)
  | zero (m : ℕ) : InW c m 0
  | add {m : ℕ} {x y : VirEnv R c} : InW c m x → InW c m y → InW c m (x + y)
  | zsmul {m : ℕ} {x : VirEnv R c} (z : ℤ) : InW c m x → InW c m (z • x)

theorem InW.mono {m m' : ℕ} {x : VirEnv R c} (hx : InW c m x) (hm : m ≤ m') : InW c m' x := by
  induction hx with
  | word w hw => exact InW.word _ w (hw.trans hm)
  | zero => exact InW.zero _
  | add _ _ ih1 ih2 => exact ih1.add ih2
  | zsmul z _ ih => exact ih.zsmul z

theorem InW.sub {m : ℕ} {x y : VirEnv R c} (hx : InW c m x) (hy : InW c m y) :
    InW c m (x - y) := by
  have := hx.add (hy.zsmul (-1))
  rwa [neg_one_zsmul, ← sub_eq_add_neg] at this

theorem InW.mulL {m : ℕ} {x : VirEnv R c} (hx : InW c m x) (a : ℤ) :
    InW c (m + f2 a) (VirEnv.L c a * x) := by
  induction hx with
  | word w hw =>
    rw [← opZ_cons]
    refine InW.word _ _ ?_
    have e : wt2 (a :: w) = f2 a + wt2 w := by simp [wt2]
    omega
  | zero =>
    rw [mul_zero]
    exact InW.zero _
  | add _ _ ih1 ih2 =>
    rw [mul_add]
    exact ih1.add ih2
  | zsmul z _ ih =>
    rw [mul_smul_comm]
    exact ih.zsmul z

/-- `[L_1, L_{w₁} ⋯ L_{w_n}]` raises `wt2` by at most `1`; `[L_1, L_n] = (1 − n) L_{n+1}` has no
central term. -/
theorem InW.ad_word (w : List ℤ) :
    InW c (wt2 w + 1) (VirEnv.L c 1 * opZ c w - opZ c w * VirEnv.L c 1) := by
  induction w with
  | nil =>
    rw [opZ_nil, mul_one, one_mul, sub_self]
    exact InW.zero _
  | cons a w ih =>
    have e : VirEnv.L c 1 * opZ c (a :: w) - opZ c (a :: w) * VirEnv.L c 1 =
        ((1 - a : ℤ)) • opZ c ((1 + a) :: w) +
          VirEnv.L c a * (VirEnv.L c 1 * opZ c w - opZ c w * VirEnv.L c 1) := by
      have h1 : VirEnv.L c 1 * VirEnv.L c a = VirEnv.L c a * VirEnv.L c 1 +
          ((1 - a : ℤ)) • VirEnv.L c (1 + a) := by
        rw [VirEnv.L_mul_L, centralTerm_one, map_zero, ite_self, add_zero]
        congr 1
      rw [opZ_cons, opZ_cons, ← mul_assoc (VirEnv.L c 1), h1, zsmul_eq_mul,
        zsmul_eq_mul, add_mul, mul_sub, mul_assoc, mul_assoc, mul_assoc]
      abel
    have hwt : wt2 (a :: w) = f2 a + wt2 w := by simp [wt2]
    have hwt' : wt2 ((1 + a) :: w) = f2 (1 + a) + wt2 w := by simp [wt2]
    rw [e]
    refine InW.add ((InW.word _ _ ?_).zsmul _) ((ih.mulL a).mono (by omega))
    have := f2_succ_le a
    omega

theorem InW.ad {m : ℕ} {x : VirEnv R c} (hx : InW c m x) :
    InW c (m + 1) (VirEnv.L c 1 * x - x * VirEnv.L c 1) := by
  induction hx with
  | word w hw => exact (InW.ad_word w).mono (by omega)
  | zero =>
    rw [mul_zero, zero_mul, sub_self]
    exact InW.zero _
  | add _ _ ih1 ih2 =>
    rw [mul_add, add_mul, add_sub_add_comm]
    exact ih1.add ih2
  | zsmul z _ ih =>
    rename_i y _
    have e : VirEnv.L c 1 * (z • y) - z • y * VirEnv.L c 1 =
        z • (VirEnv.L c 1 * y - y * VirEnv.L c 1) := by
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_sub, ← mul_assoc,
        (Int.commute_cast (VirEnv.L c 1) z).eq, mul_assoc, mul_assoc]
    rw [e]
    exact ih.zsmul z

theorem InW.adp {m : ℕ} {x : VirEnv R c} (hx : InW c m x) (p : ℕ) :
    InW c (m + p) (adp (VirEnv.L c 1) p x) := by
  induction p with
  | zero => exact hx
  | succ p ih =>
    rw [adp_succ, ← add_assoc]
    exact ih.ad

theorem negOp_cons (y : ℕ) (w : List ℕ) :
    VirEnv.negOp c (y :: w) = VirEnv.L c (-(y : ℤ)) * VirEnv.negOp c w := by
  simp [VirEnv.negOp]

theorem posOp_cons (y : ℕ) (w : List ℕ) :
    VirEnv.posOp c (y :: w) = VirEnv.posOp c w * VirEnv.L c (y : ℤ) := by
  simp [VirEnv.posOp]

theorem InW.negOp (μ' : List ℕ) (hμ' : ∀ y ∈ μ', 2 ≤ y) : InW c 0 (VirEnv.negOp c μ') := by
  induction μ' with
  | nil =>
    have e : VirEnv.negOp c [] = opZ c [] := by simp [VirEnv.negOp, opZ]
    rw [e]
    exact InW.word 0 [] (by simp [wt2])
  | cons y w ih =>
    have hy := hμ' y (List.mem_cons_self ..)
    have h1 := (ih fun z hz => hμ' z (List.mem_cons_of_mem _ hz)).mulL (-(y : ℤ))
    have e : f2 (-(y : ℤ)) = 0 := by
      unfold f2
      rw [if_neg (by omega), if_neg (by omega)]
    rw [e] at h1
    rw [negOp_cons]
    exact h1

theorem InW.posOp_mul (μ : List ℕ) : ∀ {m : ℕ} {x : VirEnv R c}, InW c m x →
    InW c (m + 2 * μ.length) (VirEnv.posOp c μ * x) := by
  induction μ with
  | nil =>
    intro m x hx
    have e : VirEnv.posOp c [] = 1 := by simp [VirEnv.posOp]
    rw [e, one_mul]
    exact hx
  | cons y w ih =>
    intro m x hx
    have h1 := hx.mulL (y : ℤ)
    have e : f2 (y : ℤ) = 2 := by
      unfold f2
      rw [if_pos (by omega)]
    rw [e] at h1
    rw [posOp_cons, mul_assoc]
    exact (ih h1).mono (by simp; omega)

/-! ### The local bracket (l.1322–1332) -/

theorem opZ_ones (q : ℕ) : opZ c (List.replicate q (-1)) = VirEnv.L c (-1) ^ q := by
  rw [opZ, List.map_replicate, List.prod_replicate]

theorem nn_ones (q : ℕ) : nn (List.replicate q (-1)) = 0 := by
  induction q with
  | zero => rfl
  | succ q ih => rw [List.replicate_succ, nn_cons_neg (by decide), ih]

theorem InW.ev_polyVal {m : ℕ} {x : VirEnv R c} (hx : InW c m x) (q : ℕ) :
    PolyVal c h (m / 2) (ev c h (x * VirEnv.L c (-1) ^ q)) := by
  induction hx with
  | word w hw =>
    rw [← opZ_ones, ← opZ_append]
    refine (ev_opZ_polyVal _).mono ?_
    rw [nn_append, nn_ones, add_zero]
    have := two_nn_le w
    omega
  | zero =>
    rw [zero_mul, ev_zero]
    exact PolyVal.zero _
  | add _ _ ih1 ih2 =>
    rw [add_mul, ev_add]
    exact ih1.add ih2
  | zsmul z _ ih =>
    rw [zsmul_eq_mul, mul_assoc, ← zsmul_eq_mul, ev_zsmul]
    exact ih.intMul z

/-- Every monomial `c^{d_c} Δ^{d_Δ}` of the local bracket
`⟨Δ|ad(L_1)^p(L_μ L_{−μ'}) L_{−1}^q|Δ⟩` has `d_Δ + d_c ≤ ℓ(μ) + p/2`, when every part of `μ'` is
at least `2` (paper.tex l.1325–1332). -/
theorem locBr_polyVal (c h : R) (μ μ' : List ℕ) (hμ' : ∀ y ∈ μ', 2 ≤ y) (p q : ℕ) :
    PolyVal c h (μ.length + p / 2) (locBr c h μ μ' p q) := by
  have h1 := ((InW.posOp_mul μ (InW.negOp (c := c) μ' hμ')).adp p).ev_polyVal (h := h) q
  refine h1.mono ?_
  omega

end Virasoro.H13C
