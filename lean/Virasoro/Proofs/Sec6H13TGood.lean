import Virasoro.Proofs.Sec6H13DegRed

/-!
# Proposition 6.8(ii): the degree calculus (paper.tex l.1366–1378)

Families `G : ℕ → ℚ[Y,Y⁻¹]⸨t⸩` indexed by the level `M`.  `Good G D V`: every `[t^i Y^j] G_M` is
a polynomial in `M` of degree at most `2i + 2j − D` (for all `M ≥ 0`), it vanishes when
`2i + 2j < V`, and the `t`-order is bounded below uniformly in `M`.  Products add `(D, V)`: this is
the paper's bookkeeping "deg_M ≤ 2i + 2j" with the base exponents of the factors.
-/

namespace Virasoro.H13T

open Virasoro.H13D Finset

/-- `ℚ[Y,Y⁻¹]⸨t⸩`. -/
abbrev LL : Type := HahnSeries ℤ LQ

/-- `[t^i Y^j] F`. -/
noncomputable def cfL (F : LL) (i j : ℤ) : ℚ := (F.coeff i).coeff j

theorem cfL_add (F G : LL) (i j : ℤ) : cfL (F + G) i j = cfL F i j + cfL G i j := by
  simp [cfL]

theorem cfL_zero (i j : ℤ) : cfL 0 i j = 0 := by simp [cfL]

theorem cfL_sum {ι : Type*} (S : Finset ι) (F : ι → LL) (i j : ℤ) :
    cfL (∑ a ∈ S, F a) i j = ∑ a ∈ S, cfL (F a) i j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [cfL_zero]
  | insert a S ha ih => rw [sum_insert ha, sum_insert ha, cfL_add, ih]

/-! ### Coefficients of products over `ℤ` with bounded-below supports -/

theorem hahn_coeff_mul {R : Type*} [CommRing R] {x y : HahnSeries ℤ R} {b b' : ℤ}
    (hx : ∀ n < b, x.coeff n = 0) (hy : ∀ n < b', y.coeff n = 0) (a : ℤ) :
    (x * y).coeff a = ∑ n ∈ Icc b (a - b'), x.coeff n * y.coeff (a - n) := by
  classical
  rw [HahnSeries.coeff_mul]
  have hinj : Set.InjOn Prod.fst
      (↑(Finset.antidiagonal x.isPWO_support y.isPWO_support a) : Set (ℤ × ℤ)) := by
    intro u hu v hv huv
    have hu' := (Finset.mem_antidiagonal.1 hu).2.2
    have hv' := (Finset.mem_antidiagonal.1 hv).2.2
    ext
    · exact huv
    · omega
  have e1 : ∑ ij ∈ Finset.antidiagonal x.isPWO_support y.isPWO_support a,
      x.coeff ij.1 * y.coeff ij.2 =
      ∑ n ∈ (Finset.antidiagonal x.isPWO_support y.isPWO_support a).image Prod.fst,
        x.coeff n * y.coeff (a - n) := by
    rw [sum_image hinj]
    refine sum_congr rfl fun ij hij => ?_
    have h := (Finset.mem_antidiagonal.1 hij).2.2
    congr 2
    omega
  rw [e1]
  refine sum_subset ?_ ?_
  · intro n hn
    obtain ⟨ij, hij, rfl⟩ := mem_image.1 hn
    obtain ⟨h1, h2, h3⟩ := Finset.mem_antidiagonal.1 hij
    have h1' : b ≤ ij.1 := by
      by_contra hlt
      exact h1 (hx _ (by omega))
    have h2' : b' ≤ ij.2 := by
      by_contra hlt
      exact h2 (hy _ (by omega))
    exact mem_Icc.2 ⟨h1', by omega⟩
  · intro n _ hn
    by_contra hne
    apply hn
    have h1 : x.coeff n ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : y.coeff (a - n) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    refine mem_image.2 ⟨(n, a - n), Finset.mem_antidiagonal.2 ⟨h1, h2, by ring⟩, rfl⟩

theorem lq_coeff_mul {x y : LQ} {b b' : ℤ} (hx : ∀ n < b, x.coeff n = 0)
    (hy : ∀ n < b', y.coeff n = 0) (a : ℤ) :
    (x * y).coeff a = ∑ n ∈ Icc b (a - b'), x.coeff n * y.coeff (a - n) := by
  classical
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  unfold Finsupp.sum
  have e : ∀ n : ℤ, -n + a = a - n := fun n => by ring
  simp_rw [e]
  have h1 : ∑ n ∈ x.coeff.support, x.coeff n * y.coeff (a - n) =
      ∑ n ∈ x.coeff.support ∪ Icc b (a - b'), x.coeff n * y.coeff (a - n) :=
    sum_subset subset_union_left fun n _ hn => by rw [Finsupp.notMem_support_iff.1 hn, zero_mul]
  have h2 : ∑ n ∈ Icc b (a - b'), x.coeff n * y.coeff (a - n) =
      ∑ n ∈ x.coeff.support ∪ Icc b (a - b'), x.coeff n * y.coeff (a - n) := by
    refine sum_subset subset_union_right fun n _ hn => ?_
    by_cases hb : b ≤ n
    · have : a - b' < n := by
        by_contra hh
        exact hn (mem_Icc.2 ⟨hb, by omega⟩)
      rw [hy _ (by omega), mul_zero]
    · rw [hx _ (by omega), zero_mul]
  rw [h1, h2]

/-! ### `Good` -/

/-- `[t^i Y^j] G_M` is a polynomial in `M` of degree at most `2i + 2j − D`, vanishes when
`2i + 2j < V`, and the `t`-order is bounded below. -/
structure Good (G : ℕ → LL) (D V : ℤ) : Prop where
  poly : ∀ i j : ℤ, PolyDeg (fun M => cfL (G M) i j) (2 * i + 2 * j - D)
  val : ∀ (M : ℕ) (i j : ℤ), 2 * i + 2 * j < V → cfL (G M) i j = 0
  ord : ∃ b : ℤ, ∀ (M : ℕ) (n : ℤ), n < b → (G M).coeff n = 0

theorem Good.mono {G : ℕ → LL} {D V D' V' : ℤ} (h : Good G D V) (hD : D' ≤ D) (hV : V' ≤ V) :
    Good G D' V' :=
  ⟨fun i j => (h.poly i j).mono (by omega), fun M i j hij => h.val M i j (by omega), h.ord⟩

theorem good_zero (D V : ℤ) : Good (fun _ => 0) D V :=
  ⟨fun i j => (polyDeg_zero _).congr fun M => by simp [cfL_zero],
    fun M i j _ => cfL_zero i j, ⟨0, fun M n _ => by simp⟩⟩

theorem Good.add {G G' : ℕ → LL} {D V : ℤ} (h : Good G D V) (h' : Good G' D V) :
    Good (fun M => G M + G' M) D V := by
  obtain ⟨b, hb⟩ := h.ord
  obtain ⟨b', hb'⟩ := h'.ord
  refine ⟨fun i j => ((h.poly i j).add (h'.poly i j)).congr fun M => cfL_add _ _ i j,
    fun M i j hij => by rw [cfL_add, h.val M i j hij, h'.val M i j hij, add_zero],
    ⟨min b b', fun M n hn => ?_⟩⟩
  rw [HahnSeries.coeff_add, hb M n (by omega), hb' M n (by omega), add_zero]

theorem Good.sum {ι : Type*} (S : Finset ι) {G : ι → ℕ → LL} {D V : ℤ}
    (h : ∀ a ∈ S, Good (G a) D V) : Good (fun M => ∑ a ∈ S, G a M) D V := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using good_zero D V
  | insert a S ha ih =>
    have h1 := (h a (mem_insert_self a S)).add (ih fun b hb => h b (mem_insert_of_mem hb))
    refine ⟨fun i j => (h1.poly i j).congr fun M => ?_, fun M i j hij => ?_, ?_⟩
    · rw [sum_insert ha]
    · rw [sum_insert ha]
      exact h1.val M i j hij
    · obtain ⟨b, hb⟩ := h1.ord
      exact ⟨b, fun M n hn => by rw [sum_insert ha]; exact hb M n hn⟩

/-- The `Y`-support of a good family at a fixed `t`-power is bounded below. -/
theorem Good.lq_low {G : ℕ → LL} {D V : ℤ} (h : Good G D V) (M : ℕ) (i n : ℤ)
    (hn : n < (V - 2 * i) / 2) : ((G M).coeff i).coeff n = 0 :=
  h.val M i n (by omega)

theorem Good.mul {G G' : ℕ → LL} {D V D' V' : ℤ} (h : Good G D V) (h' : Good G' D' V') :
    Good (fun M => G M * G' M) (D + D') (V + V') := by
  obtain ⟨b, hb⟩ := h.ord
  obtain ⟨b', hb'⟩ := h'.ord
  -- the coefficient formula with ranges independent of `M`
  have key : ∀ (M : ℕ) (i j : ℤ), cfL (G M * G' M) i j =
      ∑ n ∈ Icc b (i - b'), ∑ m ∈ Icc ((V - 2 * n) / 2) (j - (V' - 2 * (i - n)) / 2),
        cfL (G M) n m * cfL (G' M) (i - n) (j - m) := by
    intro M i j
    rw [cfL, hahn_coeff_mul (hb M) (hb' M), AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
    refine sum_congr rfl fun n _ => ?_
    rw [lq_coeff_mul (h.lq_low M n) (h'.lq_low M (i - n))]
    rfl
  refine ⟨fun i j => ?_, fun M i j hij => ?_, ⟨b + b', fun M n hn => ?_⟩⟩
  · refine PolyDeg.congr ?_ (key · i j)
    refine PolyDeg.sum _ fun n _ => PolyDeg.sum _ fun m _ => ?_
    exact ((h.poly n m).mul (h'.poly (i - n) (j - m))).mono (by omega)
  · rw [key]
    refine sum_eq_zero fun n _ => sum_eq_zero fun m _ => ?_
    by_cases h1 : 2 * n + 2 * m < V
    · rw [h.val M n m h1, zero_mul]
    · rw [h'.val M (i - n) (j - m) (by omega), mul_zero]
  · rw [hahn_coeff_mul (hb M) (hb' M)]
    refine sum_eq_zero fun k hk => ?_
    have := mem_Icc.1 hk
    omega

/-- An `M`-independent element whose nonzero coefficients satisfy `D, V ≤ 2i + 2j`. -/
theorem good_const (x : LL) {D V : ℤ}
    (hx : ∀ i j : ℤ, cfL x i j ≠ 0 → D ≤ 2 * i + 2 * j ∧ V ≤ 2 * i + 2 * j)
    (hord : ∃ b : ℤ, ∀ n < b, x.coeff n = 0) : Good (fun _ => x) D V := by
  obtain ⟨b, hb⟩ := hord
  refine ⟨fun i j => ?_, fun M i j hij => ?_, ⟨b, fun M n hn => hb n hn⟩⟩
  · by_cases h0 : cfL x i j = 0
    · exact (polyDeg_zero _).congr fun M => h0
    · exact ((polyDeg_const (cfL x i j)).mono (by have := (hx i j h0).1; omega)).congr
        fun M => rfl
  · by_contra h0
    have := (hx i j h0).2
    omega

/-- The constants `ℚ → LL`. -/
noncomputable def cL : ℚ →+* LL := HahnSeries.C.comp LaurentPolynomial.C

theorem cfL_cL_mul (q : ℚ) (F : LL) (i j : ℤ) : cfL (cL q * F) i j = q * cfL F i j := by
  rw [cfL, cL, RingHom.comp_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
    lq_coeff_C_mul]
  rfl

theorem cfL_cL (q : ℚ) (i j : ℤ) : cfL (cL q) i j = if i = 0 ∧ j = 0 then q else 0 := by
  have := cfL_cL_mul q 1 i j
  rw [mul_one] at this
  rw [this]
  unfold cfL
  rw [HahnSeries.coeff_one]
  by_cases hi : i = 0
  · rw [if_pos hi, ← LaurentPolynomial.T_zero, LaurentPolynomial.T,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hj : j = 0
    · rw [if_pos hj.symm, if_pos ⟨hi, hj⟩, mul_one]
    · rw [if_neg (Ne.symm hj), if_neg fun hh => hj hh.2, mul_zero]
  · rw [if_neg hi, if_neg fun hh => hi hh.1]
    simp

/-- A scalar polynomial in `M` of degree at most `e`. -/
theorem good_scalar (P : Polynomial ℚ) {e : ℕ} (hP : P.natDegree ≤ e) :
    Good (fun M => cL (P.eval (M : ℚ))) (-(e : ℤ)) 0 := by
  refine ⟨fun i j => ?_, fun M i j hij => ?_, ⟨0, fun M n hn => ?_⟩⟩
  · by_cases hij : i = 0 ∧ j = 0
    · refine PolyDeg.congr ⟨P, fun n hn => ?_, fun M => rfl⟩ fun M => ?_
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by obtain ⟨rfl, rfl⟩ := hij; omega)
      · rw [cfL_cL, if_pos hij]
    · exact (polyDeg_zero _).congr fun M => by rw [cfL_cL, if_neg hij]
  · rw [cfL_cL, if_neg]
    rintro ⟨rfl, rfl⟩
    omega
  · show (HahnSeries.single 0 (LaurentPolynomial.C (P.eval (M : ℚ))) : LL).coeff n = 0
    rw [HahnSeries.coeff_single, if_neg (by omega)]

theorem good_one : Good (fun _ => (1 : LL)) 0 0 := by
  have h := good_scalar (Polynomial.C 1) (e := 0) (by simp)
  simpa [cL] using h

/-! ### Thresholds: a family that is good from the level `W` on -/

theorem PolyDeg.comp_add {g : ℕ → ℚ} {D : ℤ} (h : PolyDeg g D) (s : ℕ) :
    PolyDeg (fun M => g (M + s)) D := by
  obtain ⟨f, h1, h2⟩ := h
  refine ⟨f.comp (Polynomial.X + Polynomial.C (s : ℚ)), fun n hn => ?_, fun M => ?_⟩
  · by_cases hf : f = 0
    · simp [hf]
    have hfd : (f.natDegree : ℤ) ≤ D := by
      by_contra hc
      exact (Polynomial.leadingCoeff_ne_zero.2 hf) (h1 _ (by omega))
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hb : (f.comp (Polynomial.X + Polynomial.C (s : ℚ))).natDegree ≤ f.natDegree :=
      Polynomial.natDegree_comp_le.trans
        ((Nat.mul_le_mul_left _ (Polynomial.natDegree_X_add_C _).le).trans (by rw [mul_one]))
    omega
  · beta_reduce
    rw [h2, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    push_cast
    rfl

theorem Good.shift {G : ℕ → LL} {D V : ℤ} (h : Good G D V) (s : ℕ) :
    Good (fun M => G (M + s)) D V := by
  obtain ⟨b, hb⟩ := h.ord
  exact ⟨fun i j => PolyDeg.comp_add (h.poly i j) s, fun M i j hij => h.val (M + s) i j hij,
    ⟨b, fun M n hn => hb (M + s) n hn⟩⟩

/-- A scalar polynomial vanishing on `[0, W)` times a family that is good from `W` on is good
for all `M ≥ 0` (the root sets of paper.tex l.1374–1378). -/
theorem good_pi_mul (π : Polynomial ℚ) {e : ℕ} (hπ : π.natDegree ≤ e) {W : ℕ}
    (hz : ∀ M : ℕ, M < W → π.eval (M : ℚ) = 0) {R : ℕ → LL} {D V : ℤ}
    (hR : Good (fun M => R (M + W)) D V) :
    Good (fun M => cL (π.eval (M : ℚ)) * R M) (D - e) V := by
  obtain ⟨b, hb⟩ := hR.ord
  have hlow : ∀ M : ℕ, M < W → cL (π.eval (M : ℚ)) * R M = 0 := fun M hM => by
    rw [hz M hM, map_zero, zero_mul]
  refine ⟨fun i j => ?_, fun M i j hij => ?_, ⟨b, fun M n hn => ?_⟩⟩
  · obtain ⟨f, h1, h2⟩ := hR.poly i j
    refine ⟨π * f.comp (Polynomial.X - Polynomial.C (W : ℚ)), fun n hn => ?_, fun M => ?_⟩
    · by_cases hf : f = 0
      · simp [hf]
      have hfd : (f.natDegree : ℤ) ≤ 2 * i + 2 * j - D := by
        by_contra hc
        exact (Polynomial.leadingCoeff_ne_zero.2 hf) (h1 _ (by omega))
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hb2 : (f.comp (Polynomial.X - Polynomial.C (W : ℚ))).natDegree ≤ f.natDegree :=
        Polynomial.natDegree_comp_le.trans
          ((Nat.mul_le_mul_left _ (Polynomial.natDegree_X_sub_C_le _)).trans (by rw [mul_one]))
      have h3 := Polynomial.natDegree_mul_le (p := π) (q := f.comp (Polynomial.X -
        Polynomial.C (W : ℚ)))
      omega
    · beta_reduce
      rw [cfL_cL_mul, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      by_cases hM : W ≤ M
      · have e1 := h2 (M - W)
        beta_reduce at e1
        rw [Nat.sub_add_cancel hM] at e1
        rw [e1, Nat.cast_sub hM]
      · rw [hz M (by omega), zero_mul, zero_mul]
  · by_cases hM : W ≤ M
    · rw [cfL_cL_mul]
      have e1 := hR.val (M - W) i j hij
      simp only [Nat.sub_add_cancel hM] at e1
      rw [e1, mul_zero]
    · rw [hlow M (by omega), cfL_zero]
  · by_cases hM : W ≤ M
    · rw [cL, RingHom.comp_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul]
      have e1 := hb (M - W) n hn
      rw [Nat.sub_add_cancel hM] at e1
      rw [e1, smul_zero]
    · rw [hlow M (by omega), HahnSeries.coeff_zero]

end Virasoro.H13T
