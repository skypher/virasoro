import Virasoro.Proofs.Sec6H13TProd
import Virasoro.Proofs.Sec6H13ChainDeg
import Virasoro.Proofs.Sec6H13Comb

/-!
# Proposition 6.8(ii): the Gram step (paper.tex l.1306–1332)

For `λ = (1^a, μ)`, `λ' = (1^{a'}, μ')` with all parts of `μ, μ'` at least `2`, `w = |μ|`,
`w' = |μ'|`:
`(G̃D₀⁻¹)_{λ,λ'} = ∑_p C(a,p)/(q! 2^q K_{μ'}) ∏_{s=q}^{a'−1}(1 + s t²/(2Y)) t^{p+q+ℓ(μ)+ℓ(μ')}
Y^{−q−ℓ(μ')} ⟨Δ|ad(L_1)^p(L_μ L_{−μ'}) L_{−1}^q|Δ⟩`, `q = w + p − w'` (l.1313–1322), and the
`p`-term without `C(a,p)` is `Good p p` from the level `w + p` on (l.1322–1332, 1369–1370).
-/

namespace Virasoro.H13T

open Virasoro.H13D Virasoro.H13C Finset

/-! ### Monomials -/

theorem mono_mul (e f e' f' : ℤ) (r r' : ℚ) :
    mono e f r * mono e' f' r' = mono (e + e') (f + f') (r * r') := by
  rw [mono, mono, mono, HahnSeries.single_mul_single]
  congr 1
  rw [LaurentPolynomial.T_add, map_mul]
  ring

theorem mono_zero_one : mono 0 0 1 = 1 := by
  rw [mono, map_one, LaurentPolynomial.T_zero, one_mul, HahnSeries.single_zero_one]

theorem cL_mul_mono (q : ℚ) (e f : ℤ) (r : ℚ) : cL q * mono e f r = mono e f (q * r) := by
  have : cL q = mono 0 0 q := by
    rw [mono, LaurentPolynomial.T_zero, mul_one]
    rfl
  rw [this, mono_mul, zero_add, zero_add]

theorem cL_eq_mono (q : ℚ) : cL q = mono 0 0 q := by
  rw [mono, LaurentPolynomial.T_zero, mul_one]
  rfl

/-- `t ∈ LL`. -/
noncomputable abbrev tL : LL := mono 1 0 1

/-- `c(b) = 6/t + 13 + 6t`. -/
noncomputable def cLc : LL := mono (-1) 0 6 + cL 13 + mono 1 0 6

/-- `Δ = Y/t²`. -/
noncomputable def DL : LL := mono (-2) 1 1

/-- `ℚ[Y,Y⁻¹][[t]] → ℚ[Y,Y⁻¹]⸨t⸩`. -/
noncomputable def jL : LS →+* LL := HahnSeries.ofPowerSeries ℤ LQ

theorem cfL_jL (F : LS) (i : ℕ) (j : ℤ) : cfL (jL F) i j = cf F i j := by
  rw [cfL, jL, HahnSeries.ofPowerSeries_apply_coeff]
  rfl

/-- `ℚ[t][Y] → LL`. -/
noncomputable def fL : PS →+* LL := jL.comp iM

theorem fL_tS : fL tS = tL := by
  show HahnSeries.ofPowerSeries ℤ LQ (iM tS) = mono 1 0 1
  rw [iM_tS, HahnSeries.ofPowerSeries_X, mono, LaurentPolynomial.T_zero, mul_one]
  congr 1

theorem fL_X : fL Polynomial.X = mono 0 1 1 := by
  show HahnSeries.ofPowerSeries ℤ LQ (iM Polynomial.X) = mono 0 1 1
  rw [iM_X, Yp, HahnSeries.ofPowerSeries_C, mono, map_one, one_mul]
  rfl

theorem fL_CC (q : ℚ) : fL (Polynomial.C (Polynomial.C q)) = cL q := by
  show HahnSeries.ofPowerSeries ℤ LQ (iM (Polynomial.C (Polynomial.C q))) = cL q
  rw [iM_CC, cQ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C]
  rfl

theorem fL_cS : fL cS = tL * cLc := by
  have e1 : cS = Polynomial.C (Polynomial.C 6) + Polynomial.C (Polynomial.C 13) * tS +
      Polynomial.C (Polynomial.C 6) * tS ^ 2 := by
    rw [cS, tS]
    simp only [map_add, map_mul, map_pow, map_ofNat]
  rw [e1, map_add, map_add, map_mul, map_mul, map_pow, fL_CC, fL_CC, fL_tS, cLc]
  rw [cL_eq_mono, cL_eq_mono]
  simp only [mul_add, mono_mul, pow_two]
  norm_num

theorem tL_sq_DL : tL ^ 2 * DL = mono 0 1 1 := by
  rw [pow_two, DL, mono_mul, mono_mul]
  norm_num

/-- `G̃_{Y,w} = t^{ℓ(Y)+ℓ(w)} ⟨Δ|L_Y L_{−w}|Δ⟩` in `LL`. -/
theorem fL_gramT (Y w : List ℕ) (hY : ∀ y ∈ Y, 0 < y) :
    fL (gramT tS cS Polynomial.X Y w) = tL ^ (Y.length + w.length) * gramWord cLc DL Y w := by
  rw [← gramT_map fL, fL_tS, fL_cS, fL_X, ← tL_sq_DL, gramT_eq tL cLc DL Y w hY]

/-! ### `K_{(1^a, μ)} = a! 2^a K_μ` -/

theorem facs_append_ones (μ : List ℕ) (hμ : ∀ y ∈ μ, 2 ≤ y) (a : ℕ) :
    facs ((μ ++ List.replicate a 1 : List ℕ) : Multiset ℕ) = facs (μ : Multiset ℕ) * a.factorial := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e1 : ((μ ++ List.replicate (a + 1) 1 : List ℕ) : Multiset ℕ) =
        1 ::ₘ ((μ ++ List.replicate a 1 : List ℕ) : Multiset ℕ) := by
      rw [List.replicate_succ', ← List.append_assoc, ← Multiset.coe_add, ← Multiset.coe_add,
        Multiset.coe_singleton, add_comm, Multiset.singleton_add]
    have hc : ((μ ++ List.replicate a 1 : List ℕ) : Multiset ℕ).count 1 = a := by
      rw [Multiset.coe_count, List.count_append, List.count_replicate_self]
      have : μ.count 1 = 0 := List.count_eq_zero.2 fun h => by have := hμ 1 h; omega
      omega
    rw [e1, facs_cons, hc, ih, Nat.factorial_succ]
    ring

theorem topNat_append_ones (μ : List ℕ) (hμ : ∀ y ∈ μ, 2 ≤ y) (a : ℕ) :
    topNat (μ ++ List.replicate a 1) (μ ++ List.replicate a 1) =
      a.factorial * 2 ^ a * topNat μ μ := by
  rw [topNat_perm _ _ (List.Perm.refl _), topNat_perm _ _ (List.Perm.refl _),
    facs_append_ones μ hμ a, List.length_append, List.length_replicate, List.prod_append,
    List.prod_replicate, one_pow, mul_one, pow_add]
  ring

/-! ### Constants and the local bracket -/

theorem algebraMap_LL (q : ℚ) : algebraMap ℚ LL q = cL q :=
  DFunLike.congr_fun (RingHom.ext_rat (algebraMap ℚ LL) cL) q

theorem Good.pow {G : ℕ → LL} {D V : ℤ} (h : Good G D V) (k : ℕ) :
    Good (fun M => G M ^ k) (k * D) (k * V) := by
  induction k with
  | zero => simpa using good_one
  | succ k ih =>
    have h1 := ih.mul h
    have e1 : ((k + 1 : ℕ) : ℤ) * D = k * D + D := by push_cast; ring
    have e2 : ((k + 1 : ℕ) : ℤ) * V = k * V + V := by push_cast; ring
    rw [e1, e2]
    exact ⟨fun i j => (h1.poly i j).congr fun M => by rw [pow_succ],
      fun M i j hij => by rw [pow_succ]; exact h1.val M i j hij,
      let ⟨b, hb⟩ := h1.ord; ⟨b, fun M n hn => by rw [pow_succ]; exact hb M n hn⟩⟩

theorem good_cLc : Good (fun _ => cLc) (-2) (-2) := by
  unfold cLc
  have h1 := (good_mono (-1) 0 6).mono (by norm_num : (-2 : ℤ) ≤ 2 * -1 + 2 * 0)
    (by norm_num : (-2 : ℤ) ≤ 2 * -1 + 2 * 0)
  have h2 : Good (fun _ => cL 13) (-2) (-2) := by
    rw [cL_eq_mono]
    exact (good_mono 0 0 13).mono (by norm_num) (by norm_num)
  have h3 := (good_mono 1 0 6).mono (by norm_num : (-2 : ℤ) ≤ 2 * 1 + 2 * 0)
    (by norm_num : (-2 : ℤ) ≤ 2 * 1 + 2 * 0)
  exact (h1.add h2).add h3

theorem good_DL : Good (fun _ => DL) (-2) (-2) := by
  have := good_mono (-2) 1 1
  norm_num at this
  exact this

/-- The value at `(c, Δ)` of a polynomial of total degree at most `n`: `Good (−2n) (−2n)`. -/
theorem good_polyVal {x : LL} {n : ℕ} (hx : PolyVal cLc DL n x) :
    Good (fun _ => x) (-2 * n) (-2 * n) := by
  obtain ⟨P, hP, rfl⟩ := hx
  conv => enter [1, M]; rw [P.as_sum]
  simp only [map_sum]
  refine Good.sum _ fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_two]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    algebraMap_LL]
  have hdeg : m 0 + m 1 ≤ n := by
    have h1 := MvPolynomial.le_totalDegree hm
    have h2 : m.sum (fun _ e => e) = m 0 + m 1 := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    omega
  have h1 := ((good_scalar (Polynomial.C (P.coeff m)) (e := 0) (by simp)).mul
    ((good_cLc.pow (m 0)).mul (good_DL.pow (m 1))))
  simp only [Polynomial.eval_C] at h1
  refine (h1.mono ?_ ?_)
  · push_cast; nlinarith
  · push_cast; nlinarith

end Virasoro.H13T

/-! ### The Gram step -/

namespace Virasoro.H13T

open Virasoro.H13D Virasoro.H13C Finset

/-- `x = t²/(2Y)`. -/
noncomputable abbrev xA : LL := mono 2 (-1) (1 / 2)

/-- The `p`-term of `(G̃D₀⁻¹)_{(1^a,μ),(1^{a'},μ')}` without the binomial `C(a,p)`. -/
noncomputable def stepT (μ μ' : List ℕ) (a a' p : ℕ) : LL :=
  if a - p ≤ a' then
    cL (1 / (((a' - (a - p)).factorial : ℚ) * 2 ^ (a' - (a - p)) * (topNat μ' μ' : ℚ))) *
      (∏ u ∈ range (a - p), (1 + cL (((a' - (a - p) : ℕ) : ℚ) + 1 * (u : ℚ)) * xA)) *
      mono (μ.length + μ'.length + (a' - (a - p) : ℕ) + p) (-((a' - (a - p) : ℕ) + μ'.length)) 1 *
      locBr cLc DL μ μ' p (a' - (a - p))
  else 0

theorem two_DL_add (s : ℚ) : 2 * DL + cL s = mono (-2) 1 2 * (1 + cL s * xA) := by
  have h1 : mono (-2) 1 2 * xA = 1 := by
    rw [xA, mono_mul]
    norm_num
    exact mono_zero_one
  have h2 : (2 : LL) * DL = mono (-2) 1 2 := by
    rw [DL, show (2 : LL) = cL 2 from (map_ofNat cL 2).symm, cL_mul_mono, mul_one]
  rw [mul_add, mul_one, mul_comm (cL s) xA, ← mul_assoc, h1, one_mul, h2]

theorem cast_LL (n : ℕ) : ((n : ℕ) : LL) = cL (n : ℚ) := (map_natCast cL n).symm

/-- `(G̃D₀⁻¹)_{(1^a,μ),(1^{a'},μ')} = ∑_p C(a,p) · stepT` (paper.tex l.1313–1322). -/
theorem gram_step (μ μ' : List ℕ) (hμ : ∀ y ∈ μ, 2 ≤ y) (hμ' : ∀ y ∈ μ', 2 ≤ y) (a a' : ℕ) :
    fL (gramT tS cS Polynomial.X (μ ++ List.replicate a 1) (μ' ++ List.replicate a' 1)) *
        cL (1 / (topNat (μ' ++ List.replicate a' 1) (μ' ++ List.replicate a' 1) : ℚ)) *
        mono 0 (-((μ'.length + a' : ℕ) : ℤ)) 1 =
      ∑ p ∈ range (a + 1), cL (a.choose p : ℚ) * stepT μ μ' a a' p := by
  have hpos : ∀ y ∈ μ ++ List.replicate a 1, 0 < y := by
    intro y hy
    rcases List.mem_append.1 hy with h | h
    · have := hμ y h; omega
    · rw [List.eq_of_mem_replicate h]; exact one_pos
  have hpos' : PosWord μ' := fun y hy => by have := hμ' y hy; omega
  have hK : (topNat μ' μ' : ℚ) ≠ 0 := by
    rw [topNat_perm _ _ (List.Perm.refl _)]
    have : 0 < μ'.prod := List.prod_pos fun y hy => by have := hμ' y hy; omega
    have : 0 < facs (μ' : Multiset ℕ) := Finset.prod_pos fun n _ => Nat.factorial_pos _
    positivity
  rw [fL_gramT _ _ hpos, gramWord_ones cLc DL μ μ' hpos' a a', mul_sum, sum_mul, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  have hpa : p ≤ a := Nat.lt_succ_iff.1 (mem_range.1 hp)
  rw [topNat_append_ones μ' hμ' a', stepT]
  simp only [List.length_append, List.length_replicate]
  split_ifs with hle
  · have hq' : a' = (a' - (a - p)) + (a - p) := by omega
    have hdesc : (a'.descFactorial (a - p) : ℚ) =
        (a'.factorial : ℚ) / ((a' - (a - p)).factorial : ℚ) := by
      have := Nat.factorial_mul_descFactorial hle
      have hq0 : ((a' - (a - p)).factorial : ℚ) ≠ 0 := by positivity
      rw [eq_div_iff hq0, mul_comm]
      exact_mod_cast this
    have hprod : ∏ s ∈ Ico (a' - (a - p)) a', (2 * DL + ((s : ℕ) : LL)) =
        cL (2 ^ (a - p)) * mono (-2 * (a - p : ℕ)) (a - p : ℕ) 1 *
          ∏ u ∈ range (a - p), (1 + cL (((a' - (a - p) : ℕ) : ℚ) + 1 * (u : ℚ)) * xA) := by
      rw [prod_Ico_eq_prod_range, show a' - (a' - (a - p)) = a - p by omega]
      have e1 : ∀ u ∈ range (a - p), 2 * DL + (((a' - (a - p) + u : ℕ)) : LL) =
          mono (-2) 1 2 * (1 + cL (((a' - (a - p) : ℕ) : ℚ) + 1 * (u : ℚ)) * xA) := by
        intro u _
        rw [← two_DL_add, cast_LL]
        push_cast
        ring_nf
      rw [prod_congr rfl e1, prod_mul_distrib, prod_const, card_range, mono_pow, cL_mul_mono,
        mul_one]
      congr 2 <;> push_cast <;> ring
    rw [hprod]
    have hmono : mono 1 0 1 ^ ((μ.length + a) + (μ'.length + a')) *
        mono (-2 * (a - p : ℕ)) (a - p : ℕ) 1 * mono 0 (-((μ'.length + a' : ℕ) : ℤ)) 1 =
        mono (μ.length + μ'.length + (a' - (a - p) : ℕ) + p)
          (-((a' - (a - p) : ℕ) + μ'.length)) 1 := by
      rw [mono_pow, mono_mul, mono_mul]
      congr 1
      · push_cast
        omega
      · push_cast
        omega
      · ring
    have hscal : (a.choose p : ℚ) * (a'.descFactorial (a - p) : ℚ) * 2 ^ (a - p) *
        (1 / ((a'.factorial * 2 ^ a' * topNat μ' μ' : ℕ) : ℚ)) =
        (a.choose p : ℚ) * (1 / (((a' - (a - p)).factorial : ℚ) * 2 ^ (a' - (a - p)) *
          (topNat μ' μ' : ℚ))) := by
      rw [hdesc]
      have h2 : (2 : ℚ) ^ a' = 2 ^ (a' - (a - p)) * 2 ^ (a - p) := by
        rw [← pow_add]
        congr 1
      have hf : (a'.factorial : ℚ) ≠ 0 := by positivity
      have hq0 : ((a' - (a - p)).factorial : ℚ) ≠ 0 := by positivity
      push_cast
      rw [h2]
      field_simp
    rw [cast_LL, cast_LL]
    calc _ = cL ((a.choose p : ℚ) * (a'.descFactorial (a - p) : ℚ) * 2 ^ (a - p) *
          (1 / ((a'.factorial * 2 ^ a' * topNat μ' μ' : ℕ) : ℚ))) *
          (mono 1 0 1 ^ ((μ.length + a) + (μ'.length + a')) *
            mono (-2 * (a - p : ℕ)) (a - p : ℕ) 1 * mono 0 (-((μ'.length + a' : ℕ) : ℤ)) 1) *
          (∏ u ∈ range (a - p), (1 + cL (((a' - (a - p) : ℕ) : ℚ) + 1 * (u : ℚ)) * xA)) *
          locBr cLc DL μ μ' p (a' - (a - p)) := by
          simp only [map_mul]
          push_cast
          ring
      _ = _ := by
          rw [hscal, hmono, map_mul]
          ring
  · have h0 : a'.descFactorial (a - p) = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    simp [h0]

/-- The `p`-term along the levels, from the level `w + p` on (`a = M + p`, `a' = M + q`):
`Good p p` (paper.tex l.1322–1332, 1369–1370). -/
theorem good_stepT (μ μ' : List ℕ) (hμ' : ∀ y ∈ μ', 2 ≤ y) (p q : ℕ) :
    Good (fun M => stepT μ μ' (M + p) (M + q) p) p p := by
  have e1 : ∀ M : ℕ, stepT μ μ' (M + p) (M + q) p =
      cL (1 / ((q.factorial : ℚ) * 2 ^ q * (topNat μ' μ' : ℚ))) *
        (∏ u ∈ range (M + 0), (1 + cL ((q : ℚ) + 1 * (u : ℚ)) * mono (2 : ℕ) (-1) (1 / 2))) *
        mono (μ.length + μ'.length + q + p) (-(q + μ'.length)) 1 *
        locBr cLc DL μ μ' p q := by
    intro M
    rw [stepT, if_pos (by omega), show M + p - p = M by omega, show M + q - M = q by omega,
      add_zero]
    rfl
  have hc := good_scalar (Polynomial.C (1 / ((q.factorial : ℚ) * 2 ^ q * (topNat μ' μ' : ℚ))))
    (e := 0) (Polynomial.natDegree_C _).le
  simp only [Polynomial.eval_C] at hc
  have hP := good_prod (q : ℚ) 1 0 2 (by norm_num) (-1) (by norm_num) (1 / 2)
  have hm := good_mono (μ.length + μ'.length + q + p) (-(q + μ'.length)) 1
  have hb := good_polyVal (locBr_polyVal cLc DL μ μ' hμ' p q)
  have h := ((hc.mul hP).mul hm).mul hb
  refine ⟨fun i j => (h.poly i j).mono (by omega) |>.congr fun M => by rw [e1],
    fun M i j hij => by rw [e1]; exact h.val M i j (by omega), ?_⟩
  obtain ⟨b, hb'⟩ := h.ord
  exact ⟨b, fun M n hn => by rw [e1]; exact hb' M n hn⟩

end Virasoro.H13T
