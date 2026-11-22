import Virasoro.Proofs.Sec6FockPair
import Virasoro.Proofs.VermaSpan
import Virasoro.Proofs.GramDet
import Virasoro.Sphere.Proofs.Sec3FockLevel

/-!
# `G_M = B_M(q₀, 2q₀−α)ᵀ D_M B_M(q₀, α)` (paper.tex l.1264–1270)

`B_M(q₀,α)` expresses `L_{-λ}|α⟩` in the monomials `a_{-μ}|α⟩`, and
`D_M = diag((−1)^{ℓ(λ)} ∏_n m_n! n^{m_n})`.  The matrix elements of the pairing between
`𝓕(2q₀−α)` and `𝓕(α)` on the vectors `L_{-λ}|·⟩` are the Shapovalov matrix elements, by
contravariance, the Virasoro relations and the highest-weight property.

In this file `Bm al q N` has rows indexed by `λ` (the vector `L_{-λ}|α⟩`) and columns by the
monomials, so it is the transpose of the paper's `B_M`.
-/

namespace Virasoro.TFock

open MvPolynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `L_{-w₁} ⋯ L_{-w_r} |α⟩`. -/
noncomputable def wordF (al q : R) : List ℕ → MvPolynomial ℕ+ R
  | [] => 1
  | y :: w => LOp al q (-(y : ℤ)) (wordF al q w)

/-- `∑ a • L_{-w}|α⟩` for a list of (word, coefficient) pairs. -/
noncomputable def toF (al q : R) (s : St R) : MvPolynomial ℕ+ R :=
  (s.map fun t => t.2 • wordF al q t.1).sum

theorem toF_nil (al q : R) : toF al q [] = 0 := rfl

theorem toF_cons (al q : R) (t : List ℕ × R) (s : St R) :
    toF al q (t :: s) = t.2 • wordF al q t.1 + toF al q s := by
  simp [toF]

theorem toF_append (al q : R) (s s' : St R) : toF al q (s ++ s') = toF al q s + toF al q s' := by
  simp [toF]

theorem toF_single (al q : R) (w : List ℕ) (a : R) : toF al q [(w, a)] = a • wordF al q w := by
  simp [toF]

theorem toF_map_cons (al q : R) (y : ℕ) (s : St R) :
    toF al q (s.map fun t => (y :: t.1, t.2)) = LOp al q (-(y : ℤ)) (toF al q s) := by
  induction s with
  | nil => rw [List.map_nil, toF_nil, map_zero]
  | cons t s ih => rw [List.map_cons, toF_cons, toF_cons, ih, map_add, map_smul]; rfl

theorem toF_map_smul (al q : R) (a : R) (s : St R) :
    toF al q (s.map fun t => (t.1, a * t.2)) = a • toF al q s := by
  induction s with
  | nil => rw [List.map_nil, toF_nil, smul_zero]
  | cons t s ih => rw [List.map_cons, toF_cons, toF_cons, ih, smul_add, mul_smul]

theorem LOp_zero_wordF (al q : R) (w : List ℕ) :
    LOp al q 0 (wordF al q w) = (wt al q + ((w.sum : ℕ) : R)) • wordF al q w := by
  induction w with
  | nil =>
    rw [List.sum_nil, Nat.cast_zero, add_zero]
    exact LOp_one_zero al q
  | cons y w ih =>
    show LOp al q 0 (LOp al q (-(y : ℤ)) (wordF al q w)) = _ • LOp al q (-(y : ℤ)) (wordF al q w)
    rw [LOp_vir, ih, map_smul, List.sum_cons]
    have e : (0 : ℤ) + -(y : ℤ) = -(y : ℤ) := by ring
    rw [e]
    by_cases hy : -(y : ℤ) = 0
    · rw [if_pos hy]
      have hy0 : (y : ℤ) = 0 := by omega
      simp only [centralTerm_zero, zero_smul, add_zero]
      push_cast
      rw [hy0]
      module
    · rw [if_neg hy, add_zero]
      push_cast
      module

/-- The normal-ordering procedure computes `L_k L_{-w}|α⟩` (Virasoro relations with
`c = 1 − 12q₀²` and the highest-weight property). -/
theorem LOp_wordF_actWord (al q : R) (w : List ℕ) : ∀ k : ℤ,
    LOp al q k (wordF al q w) = toF al q (actWord (1 - 12 * q ^ 2) (wt al q) k w) := by
  induction w with
  | nil =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk, toF_single, one_smul]
      have : -((k.natAbs : ℕ) : ℤ) = k := by omega
      show _ = LOp al q (-((k.natAbs : ℕ) : ℤ)) (wordF al q [])
      rw [this]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0, toF_single, hk0]
        exact LOp_one_zero al q
      · rw [if_neg hk0, toF_nil]
        exact LOp_one_pos al q (by omega)
  | cons y w ih =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk, toF_single, one_smul]
      have : -((k.natAbs : ℕ) : ℤ) = k := by omega
      show _ = LOp al q (-((k.natAbs : ℕ) : ℤ)) (wordF al q (y :: w))
      rw [this]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0, toF_single, hk0, LOp_zero_wordF, List.sum_cons]
      · rw [if_neg hk0, toF_append, toF_append, toF_map_cons, toF_map_smul, ← ih k, ← ih (k - y)]
        show LOp al q k (LOp al q (-(y : ℤ)) (wordF al q w)) = _
        rw [LOp_vir]
        have e1 : k + -(y : ℤ) = k - y := by ring
        have e2 : k - -(y : ℤ) = k + y := by ring
        rw [e1, e2]
        congr 1
        by_cases hky : k = y
        · rw [if_pos hky, if_pos (by omega), toF_single]
        · rw [if_neg hky, if_neg (by omega), toF_nil]

theorem toF_actSt (al q : R) (k : ℤ) (s : St R) :
    toF al q (actSt (1 - 12 * q ^ 2) (wt al q) k s) = LOp al q k (toF al q s) := by
  induction s with
  | nil => simp [actSt, toF_nil]
  | cons t s ih =>
    have e : actSt (1 - 12 * q ^ 2) (wt al q) k (t :: s)
        = ((actWord (1 - 12 * q ^ 2) (wt al q) k t.1).map fun u => (u.1, t.2 * u.2)) ++
          actSt (1 - 12 * q ^ 2) (wt al q) k s := by
      simp [actSt]
    rw [e, toF_append, ih, toF_map_smul, toF_cons, map_add, map_smul, LOp_wordF_actWord]

/-- `⟨2q₀−α| ∑ a • L_{-w}|α⟩` is the coefficient of the empty word. -/
theorem pair_one_toF (al q : R) (s : St R) (hs : PosSt s) : pair 1 (toF al q s) = vac s := by
  induction s with
  | nil => simp [toF_nil, vac]
  | cons t s ih =>
    have hs' : PosSt s := fun u hu => hs u (List.mem_cons_of_mem _ hu)
    have ht : PosWord t.1 := hs t List.mem_cons_self
    rw [toF_cons, map_add, map_smul, ih hs']
    have hv : vac (t :: s) = (if t.1.isEmpty then t.2 else 0) + vac s := by simp [vac]
    rw [hv]
    congr 1
    obtain ⟨w, a⟩ := t
    cases w with
    | nil =>
      show a • pair 1 (1 : MvPolynomial ℕ+ R) = _
      rw [pair_one_one]
      simp
    | cons y w =>
      have hy : 0 < y := ht y List.mem_cons_self
      have h1 := pair_L al q (y : ℤ) 1 (wordF al q w)
      rw [LOp_one_pos _ q (by exact_mod_cast hy), map_zero, LinearMap.zero_apply] at h1
      show a • pair 1 (LOp al q (-(y : ℤ)) (wordF al q w)) = _
      rw [← h1]
      simp

theorem pair_wordF_toF (al q : R) : ∀ (Y : List ℕ) (s : St R),
    pair (wordF (2 * q - al) q Y) (toF al q s) =
      pair 1 (toF al q
        (Y.foldl (fun (s : St R) (y : ℕ) => actSt (1 - 12 * q ^ 2) (wt al q) (y : ℤ) s) s)) := by
  intro Y
  induction Y with
  | nil => intro s; rfl
  | cons y Y ih =>
    intro s
    have h1 := pair_L al q (-(y : ℤ)) (wordF (2 * q - al) q Y) (toF al q s)
    rw [neg_neg] at h1
    show pair (LOp (2 * q - al) q (-(y : ℤ)) (wordF (2 * q - al) q Y)) (toF al q s) = _
    rw [h1, ← toF_actSt, ih, List.foldl_cons]

theorem posSt_foldl (c h : R) : ∀ (Y : List ℕ) (s : St R), PosSt s →
    PosSt (Y.foldl (fun (s : St R) (y : ℕ) => actSt c h (y : ℤ) s) s) := by
  intro Y
  induction Y with
  | nil => intro s hs; exact hs
  | cons y Y ih => intro s hs; exact ih _ (posSt_actSt c h _ hs)

/-- `⟨L_{-Y}(2q₀−α), L_{-Y'} α⟩ = ⟨Δ| L_Y L_{-Y'} |Δ⟩` (paper.tex l.1264–1268). -/
theorem pair_wordF (al q : R) (Y Y' : List ℕ) (hY' : PosWord Y') :
    pair (wordF (2 * q - al) q Y) (wordF al q Y') =
      gramWord (1 - 12 * q ^ 2) (wt al q) Y Y' := by
  have h0 : wordF al q Y' = toF al q [(Y', 1)] := by rw [toF_single, one_smul]
  have hp : PosSt ([(Y', 1)] : St R) := by
    intro t ht
    rw [List.mem_singleton] at ht
    rw [ht]
    exact hY'
  rw [h0, pair_wordF_toF, pair_one_toF al q _ (posSt_foldl _ _ Y _ hp)]
  rfl

/-! ### The level: `L_0 = Δ + ∑ n x_n ∂_n` -/

theorem int_mul_cancel {k : ℤ} (hk : k ≠ 0) {x : R} (h : x * (k : R) = 0) : x = 0 := by
  have h1 : (k : R) * algebraMap ℚ R (1 / (k : ℚ)) = 1 := by
    rw [← map_intCast (algebraMap ℚ R) k, ← map_mul,
      mul_one_div_cancel (by exact_mod_cast hk), map_one]
  calc x = x * ((k : R) * algebraMap ℚ R (1 / (k : ℚ))) := by rw [h1, mul_one]
    _ = 0 := by rw [← mul_assoc, h, zero_mul]

omit [Algebra ℚ R] in
theorem weight_sub_single {e : ℕ+ →₀ ℕ} {i : ℕ+} (hi : i ∈ e.support) :
    Finsupp.weight Sphere.fockWeight (e - Finsupp.single i 1) + (i : ℕ) =
      Finsupp.weight Sphere.fockWeight e := by
  have hle : Finsupp.single i 1 ≤ e := by
    intro k
    rw [Finsupp.single_apply]
    split_ifs with hk
    · subst hk
      have := Finsupp.mem_support_iff.1 hi
      omega
    · omega
  have h2 : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  conv_rhs => rw [← h2]
  rw [map_add, Finsupp.weight_single]
  simp [Sphere.fockWeight]

omit [Algebra ℚ R] in
/-- `∑_n n x_n ∂_n` multiplies the monomial `x^e` by its weight. -/
theorem coeff_dOp_zero (f : MvPolynomial ℕ+ R) : ∀ e : ℕ+ →₀ ℕ,
    coeff e (dOp 0 f) = ((Finsupp.weight Sphere.fockWeight e : ℕ) : R) * coeff e f := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro e
    rw [← algebraMap_eq, Derivation.map_algebraMap, coeff_zero, algebraMap_eq, coeff_C]
    split_ifs with h
    · subst h
      simp
    · rw [mul_zero]
  | add p q hp hq =>
    intro e
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
  | mul_X p i hp =>
    intro e
    have hi : (0 : ℤ) < ((i : ℕ) : ℤ) := by exact_mod_cast i.pos
    have hX : dOp 0 (X i : MvPolynomial ℕ+ R) = ((i : ℕ) : R) • X i := by
      rw [dOp, mkDerivation_X, if_pos hi, sub_zero, pn_coe]
    rw [Derivation.leibniz, hX, coeff_add, smul_eq_mul, smul_eq_mul, mul_smul_comm, coeff_smul,
      mul_comm (X i) (dOp 0 p), coeff_mul_X', coeff_mul_X']
    split_ifs with h
    · rw [hp, ← weight_sub_single h]
      push_cast
      simp only [smul_eq_mul]
      ring
    · simp

/-- `L_{-w}|α⟩` has level `|w|`: its coefficients of other weights vanish. -/
theorem coeff_wordF_eq_zero (al q : R) (w : List ℕ) (e : ℕ+ →₀ ℕ)
    (he : Finsupp.weight Sphere.fockWeight e ≠ w.sum) : coeff e (wordF al q w) = 0 := by
  have h1 := LOp_zero_wordF al q w
  have h2 : LOp al q 0 (wordF al q w) = dOp 0 (wordF al q w) + wt al q • wordF al q w := by
    rw [LOp_apply]
    have hq : qOp al 0 (wordF al q w) = 0 := by
      rw [qOp_apply]
      simp
    rw [hq, smul_zero, add_zero]
    unfold zOp wt
    rw [if_pos rfl]
    rfl
  rw [h2] at h1
  have h3 := congrArg (coeff e) h1
  rw [coeff_add, coeff_smul, coeff_smul, coeff_dOp_zero, smul_eq_mul, smul_eq_mul] at h3
  apply int_mul_cancel
    (k := ((Finsupp.weight Sphere.fockWeight e : ℕ) : ℤ) - ((w.sum : ℕ) : ℤ)) (by omega)
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  linear_combination h3

/-! ### Monomials and partitions -/

/-- The exponent vector of the monomial `a_{-μ}`. -/
noncomputable def expOf {N : ℕ} (Y : Nat.Partition N) : ℕ+ →₀ ℕ :=
  Multiset.toFinsupp (Y.parts.map Nat.toPNat')

theorem expOf_partOfExp (d : ℕ+ →₀ ℕ) {N : ℕ} (hd : Finsupp.weight Sphere.fockWeight d = N) :
    expOf (Sphere.partOfExp d hd) = d := by
  unfold expOf Sphere.partOfExp
  simp only [Multiset.map_map]
  have : (Finsupp.toMultiset d).map (Nat.toPNat' ∘ fun m : ℕ+ => (m : ℕ)) =
      Finsupp.toMultiset d := by
    conv_rhs => rw [← Multiset.map_id (Finsupp.toMultiset d)]
    apply Multiset.map_congr rfl
    intro m _
    exact PNat.coe_toPNat' m
  rw [this, Finsupp.toMultiset_toFinsupp]

theorem expOf_injective {N : ℕ} : Function.Injective (expOf (N := N)) := by
  intro Y Y' h
  have h1 : Y.parts.map Nat.toPNat' = Y'.parts.map Nat.toPNat' := Multiset.toFinsupp.injective h
  have h2 : ∀ Z : Nat.Partition N,
      (Z.parts.map Nat.toPNat').map (fun m : ℕ+ => (m : ℕ)) = Z.parts := by
    intro Z
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id Z.parts]
    apply Multiset.map_congr rfl
    intro m hm
    exact PNat.toPNat'_coe (Z.parts_pos hm)
  apply Nat.Partition.ext
  rw [← h2 Y, ← h2 Y', h1]

omit [Algebra ℚ R] in
theorem pair_eq_sum (f g : MvPolynomial ℕ+ R) :
    pair f g = ∑ e ∈ f.support, coeff e f * (wgt e : R) * coeff e g := by
  conv_lhs => rw [← support_sum_monomial_coeff f]
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun e _ => pair_monomial e _ g

omit [Algebra ℚ R] in
/-- The pairing as a sum over the monomials `a_{-μ}`, `μ ⊢ N`, for `f` of level `N`. -/
theorem pair_sum_partitions {N : ℕ} (f g : MvPolynomial ℕ+ R)
    (hf : ∀ e, Finsupp.weight Sphere.fockWeight e ≠ N → coeff e f = 0) :
    pair f g = ∑ Z : Nat.Partition N,
      coeff (expOf Z) f * (wgt (expOf Z) : R) * coeff (expOf Z) g := by
  classical
  rw [pair_eq_sum]
  have hsub : f.support ⊆ (Finset.univ : Finset (Nat.Partition N)).image expOf := by
    intro e he
    rw [mem_support_iff] at he
    have hw : Finsupp.weight Sphere.fockWeight e = N := by
      by_contra h
      exact he (hf e h)
    rw [Finset.mem_image]
    exact ⟨Sphere.partOfExp e hw, Finset.mem_univ _, expOf_partOfExp e hw⟩
  rw [Finset.sum_subset hsub (fun e _ he => by rw [notMem_support_iff.1 he]; ring),
    Finset.sum_image (fun _ _ _ _ h => expOf_injective h)]

/-- The matrix of `L_{-λ}|α⟩` in the monomials `a_{-μ}|α⟩` (rows `λ`, columns `μ`). -/
noncomputable def Bm (al q : R) (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) R :=
  Matrix.of fun Y Z => coeff (expOf Z) (wordF al q Y.word)

/-- `D_M = diag((−1)^{ℓ(λ)} ∏_n m_n! n^{m_n})`. -/
noncomputable def Dm {N : ℕ} (Z : Nat.Partition N) : ℤ := wgt (expOf Z)

theorem word_sum {N : ℕ} (Y : Nat.Partition N) : Y.word.sum = N := by
  have h : ((Y.word : List ℕ) : Multiset ℕ).sum = N := by
    rw [Nat.Partition.word, Multiset.sort_eq]
    exact Y.parts_sum
  rwa [Multiset.sum_coe] at h

/-- `G_M = B_M(q₀, 2q₀−α)ᵀ D_M B_M(q₀, α)` (paper.tex l.1268), with `c = 1 − 12q₀²` and
`Δ = ½α(α − 2q₀)`. -/
theorem gram_factor (al q : R) (N : ℕ) :
    gram (1 - 12 * q ^ 2) (wt al q) N =
      Bm (2 * q - al) q N * Matrix.diagonal (fun Z : Nat.Partition N => ((Dm Z : ℤ) : R)) *
        (Bm al q N).transpose := by
  ext Y Y'
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, gram, Matrix.of_apply, Bm, Dm]
  rw [← pair_wordF al q _ _ (word_pos Y')]
  exact pair_sum_partitions _ _ fun e he =>
    coeff_wordF_eq_zero _ q Y.word e (by rw [word_sum]; exact he)

end Virasoro.TFock
