import Virasoro.Proofs.Sec6H13TTorus
import Virasoro.Proofs.DefMatrices

/-!
# Proposition 6.8(ii): the degree of the local bracket of `ρ̃` (paper.tex l.1349–1352)

"This bracket has `ℓ(μ_r) + ℓ(μ_0)` modes and hence satisfies `d_d + d_Δ + d_c ≤ ℓ(μ_r) + ℓ(μ_0)`."
* `L_k L_{−w}|Δ⟩` is a combination of `L_{−u}|Δ⟩` whose coefficients have total degree in `(c, Δ)`
  at most `1 + ℓ(w) − ℓ(u)` (`actWord_deg`: a contraction consumes a mode);
* so a word `w` of modes applied to `|Δ⟩` has coefficients of degree at most `ℓ(w) − ℓ(u)`;
* `⟨Δ|L_Y V_d(1) L_{−w}|Δ⟩` has degree at most `ℓ(Y) + ℓ(w)` in `(c, Δ, d)` (`torusWord_deg`);
* `ad(L_{±1})` maps a combination of words of length `n` to one (`[L_{±1}, L_a]` is a multiple of
  one mode, the central term vanishes).
-/

namespace Virasoro.H13C

open Verma Finset

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h d : R}

/-! ### Polynomial values in `(c, Δ, d)` -/

/-- `x` is the value at `(c, Δ, d)` of a polynomial of total degree at most `n`. -/
def PolyVal3 (c h d : R) (n : ℕ) (x : R) : Prop :=
  ∃ P : MvPolynomial (Fin 3) ℚ, P.totalDegree ≤ n ∧ MvPolynomial.aeval ![c, h, d] P = x

theorem PolyVal3.mono {n n' : ℕ} {x : R} (hx : PolyVal3 c h d n x) (hn : n ≤ n') :
    PolyVal3 c h d n' x :=
  let ⟨P, h1, h2⟩ := hx
  ⟨P, h1.trans hn, h2⟩

theorem PolyVal3.zero (n : ℕ) : PolyVal3 c h d n 0 := ⟨0, by simp, map_zero _⟩

theorem PolyVal3.one : PolyVal3 c h d 0 1 := ⟨1, by simp, map_one _⟩

theorem PolyVal3.add {n : ℕ} {x y : R} (hx : PolyVal3 c h d n x) (hy : PolyVal3 c h d n y) :
    PolyVal3 c h d n (x + y) := by
  obtain ⟨P, h1, h2⟩ := hx
  obtain ⟨Q, h3, h4⟩ := hy
  exact ⟨P + Q, (MvPolynomial.totalDegree_add P Q).trans (max_le h1 h3), by rw [map_add, h2, h4]⟩

theorem PolyVal3.mul {n m : ℕ} {x y : R} (hx : PolyVal3 c h d n x) (hy : PolyVal3 c h d m y) :
    PolyVal3 c h d (n + m) (x * y) := by
  obtain ⟨P, h1, h2⟩ := hx
  obtain ⟨Q, h3, h4⟩ := hy
  exact ⟨P * Q, (MvPolynomial.totalDegree_mul P Q).trans (Nat.add_le_add h1 h3),
    by rw [map_mul, h2, h4]⟩

theorem PolyVal3.const (q : ℚ) : PolyVal3 c h d 0 (algebraMap ℚ R q) :=
  ⟨MvPolynomial.C q, by simp, by simp⟩

theorem PolyVal3.intCast (z : ℤ) : PolyVal3 c h d 0 ((z : R)) := by
  have := PolyVal3.const (c := c) (h := h) (d := d) (z : ℚ)
  rwa [map_intCast] at this

theorem PolyVal3.natCast (z : ℕ) : PolyVal3 c h d 0 ((z : R)) := by
  have := PolyVal3.intCast (c := c) (h := h) (d := d) (z : ℤ)
  rwa [Int.cast_natCast] at this

theorem PolyVal3.var (i : Fin 3) : PolyVal3 c h d 1 (![c, h, d] i) :=
  ⟨MvPolynomial.X i, by simp, by simp⟩

theorem PolyVal3.vc : PolyVal3 c h d 1 c := PolyVal3.var 0
theorem PolyVal3.vh : PolyVal3 c h d 1 h := PolyVal3.var 1
theorem PolyVal3.vd : PolyVal3 c h d 1 d := PolyVal3.var 2

theorem PolyVal3.sum {ι : Type*} (s : Finset ι) {n : ℕ} {x : ι → R}
    (hx : ∀ i ∈ s, PolyVal3 c h d n (x i)) : PolyVal3 c h d n (∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolyVal3.zero n
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (hx a (mem_insert_self a s)).add (ih fun i hi => hx i (mem_insert_of_mem hi))

theorem PolyVal3.list_sum {n : ℕ} {l : List R} (hl : ∀ x ∈ l, PolyVal3 c h d n x) :
    PolyVal3 c h d n l.sum := by
  induction l with
  | nil => simpa using PolyVal3.zero n
  | cons x l ih =>
    rw [List.sum_cons]
    exact (hl x List.mem_cons_self).add (ih fun y hy => hl y (List.mem_cons_of_mem _ hy))

/-! ### The mode action on basis vectors -/

/-- A contraction consumes a mode: the coefficients of `L_k L_{−w}|Δ⟩` in `L_{−u}|Δ⟩` have degree
at most `1 + ℓ(w) − ℓ(u)`, with `ℓ(u) ≤ ℓ(w) + 1`. -/
theorem actWord_deg (w : List ℕ) : ∀ (k : ℤ), ∀ t ∈ actWord c h k w,
    t.1.length ≤ w.length + 1 ∧ PolyVal3 c h d (1 + w.length - t.1.length) t.2 := by
  induction w with
  | nil =>
    intro k t ht
    rw [actWord] at ht
    split_ifs at ht with h1 h2
    · rw [List.mem_singleton] at ht
      subst ht
      exact ⟨by simp, PolyVal3.one.mono (Nat.zero_le _)⟩
    · rw [List.mem_singleton] at ht
      subst ht
      exact ⟨by simp, PolyVal3.vh.mono (by simp)⟩
    · simp at ht
  | cons y w ih =>
    intro k t ht
    have hAB : ∀ t ∈ ((actWord c h k w).map fun t => (y :: t.1, t.2)) ++
        ((actWord c h (k - y) w).map fun t => (t.1, ((k + y : ℤ) : R) * t.2)),
        t.1.length ≤ (y :: w).length + 1 ∧
          PolyVal3 c h d (1 + (y :: w).length - t.1.length) t.2 := by
      intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
        obtain ⟨h1', h2'⟩ := ih k u hu
        exact ⟨by simp only [List.length_cons]; omega,
          h2'.mono (by simp only [List.length_cons]; omega)⟩
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 ht
        obtain ⟨h1', h2'⟩ := ih (k - y) u hu
        exact ⟨by simp only [List.length_cons]; omega,
          ((PolyVal3.intCast (k + y)).mul h2').mono (by simp only [List.length_cons]; omega)⟩
    rw [actWord] at ht
    split_ifs at ht with h1 h2 h3
    · rw [List.mem_singleton] at ht
      subst ht
      exact ⟨by simp, PolyVal3.one.mono (Nat.zero_le _)⟩
    · rw [List.mem_singleton] at ht
      subst ht
      refine ⟨by simp, ?_⟩
      have := (PolyVal3.vh (c := c) (h := h) (d := d)).add
        ((PolyVal3.natCast (c := c) (h := h) (d := d) (y + w.sum)).mono (Nat.zero_le 1))
      exact this.mono (by simp)
    · rcases List.mem_append.1 ht with ht | ht
      · exact hAB t ht
      · rw [List.mem_singleton] at ht
        subst ht
        refine ⟨by simp only [List.length_cons]; omega, ?_⟩
        have := (PolyVal3.const (c := c) (h := h) (d := d) (((k ^ 3 - k : ℤ) : ℚ) / 12)).mul
          PolyVal3.vc
        unfold centralTerm
        exact this.mono (by dsimp only; simp only [List.length_cons]; omega)
    · rw [List.append_nil] at ht
      exact hAB t ht

/-! ### Words of modes applied to `|Δ⟩` -/

theorem actSt_cons (k : ℤ) (t : List ℕ × R) (s : St R) :
    actSt c h k (t :: s) = (actWord c h k t.1).map (fun u => (u.1, t.2 * u.2)) ++ actSt c h k s := by
  simp [actSt]

theorem L_toVerma (k : ℤ) (s : St R) :
    L k (St.toVerma (c := c) (h := h) s) = St.toVerma (actSt c h k s) := by
  induction s with
  | nil => rw [St.toVerma_nil, map_zero]; rfl
  | cons t s ih =>
    rw [St.toVerma_cons, map_add, map_smul, L_neg_actWord, ih, actSt_cons, St.toVerma_append,
      St.toVerma_map_smul]

theorem opZ_expand (w : List ℤ) : ∃ s : St R,
    opZ c w • (hw : Verma R c h) = St.toVerma s ∧ PosSt s ∧
      ∀ t ∈ s, t.1.length ≤ w.length ∧ PolyVal3 c h d (w.length - t.1.length) t.2 := by
  induction w with
  | nil =>
    refine ⟨[([], 1)], ?_, ?_, ?_⟩
    · rw [opZ_nil, one_smul, St.toVerma_single, neg_nil]
      exact (one_smul R (hw : Verma R c h)).symm
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      intro y hy
      simp at hy
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact ⟨by simp, PolyVal3.one⟩
  | cons k w ih =>
    obtain ⟨s, hs1, hs2, hs3⟩ := ih
    refine ⟨actSt c h k s, ?_, ?_, ?_⟩
    · rw [opZ_cons, mul_smul, hs1, ← L_toVerma]
      rfl
    · intro u hu
      obtain ⟨t, ht, hu⟩ := List.mem_flatMap.1 hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
      exact posSt_actWord c h (hs2 t ht) k v hv
    · intro u hu
      obtain ⟨t, ht, hu⟩ := List.mem_flatMap.1 hu
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
      obtain ⟨h1, h2⟩ := hs3 t ht
      obtain ⟨h3, h4⟩ := actWord_deg (d := d) t.1 k v hv
      refine ⟨by simp only [List.length_cons]; omega, (h2.mul h4).mono ?_⟩
      simp only [List.length_cons]
      omega

theorem phi_deg (w : List ℕ) : PolyVal3 c h d w.length (phi d w) := by
  induction w with
  | nil => exact PolyVal3.one
  | cons m w ih =>
    rw [phi]
    have h1 : PolyVal3 c h d 1 (((w.sum : ℕ) : R) + (m : R) * d) :=
      ((PolyVal3.natCast (c := c) (h := h) (d := d) _).mono (Nat.zero_le 1)).add
        (((PolyVal3.natCast (c := c) (h := h) (d := d) m).mul PolyVal3.vd).mono (by omega))
    exact (h1.mul ih).mono (by simp; omega)

theorem torusWord_deg (Y : List ℕ) : ∀ w : List ℕ, PosWord Y → PosWord w →
    PolyVal3 c h d (Y.length + w.length) (torusWord c h d Y w) := by
  induction Y with
  | nil =>
    intro w _ _
    rw [torusWord]
    exact (phi_deg w).mono (by simp)
  | cons y Y ih =>
    intro w hY hw
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    rw [torusWord]
    refine PolyVal3.add (PolyVal3.list_sum fun x hx => ?_) ?_
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      obtain ⟨h1, h2⟩ := actWord_deg (d := d) w (y : ℤ) t ht
      have h3 := ih t.1 hY' (posSt_actWord c h hw (y : ℤ) t ht)
      exact (h2.mul h3).mono (by simp only [List.length_cons]; omega)
    · have hA : PolyVal3 c h d 0 (((Y.sum : ℕ) : R) - ((w.sum : ℕ) : R)) := by
        have := PolyVal3.intCast (c := c) (h := h) (d := d) ((Y.sum : ℤ) - (w.sum : ℤ))
        rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at this
        exact this
      have hB : PolyVal3 c h d 1 ((y : R) * d) :=
        ((PolyVal3.natCast (c := c) (h := h) (d := d) y).mul PolyVal3.vd).mono (by omega)
      have h1 := (hA.mono (Nat.zero_le 1)).add hB
      exact (h1.mul (ih w hY' hw)).mono (by simp only [List.length_cons]; omega)

theorem T_toVerma_left {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (s : St R) (v : Verma R c h) :
    T (St.toVerma s) v = (s.map fun t => t.2 * T (neg t.1) v).sum := by
  induction s with
  | nil => rw [St.toVerma_nil, map_zero, LinearMap.zero_apply]; rfl
  | cons t s ih =>
    rw [St.toVerma_cons, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, ih,
      List.map_cons, List.sum_cons, smul_eq_mul]

/-- `⟨Δ|(word w)^† V_d(1) (word w')|Δ⟩` has degree at most `ℓ(w) + ℓ(w')` in `(c, Δ, d)`. -/
theorem T_opZ_deg {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hT : IsPrimaryPairing d T)
    (w w' : List ℤ) :
    PolyVal3 c h d (w.length + w'.length)
      (T (opZ c w • (hw : Verma R c h)) (opZ c w' • (hw : Verma R c h))) := by
  obtain ⟨s, hs1, hs2, hs3⟩ := opZ_expand (c := c) (h := h) (d := d) w
  obtain ⟨s', hs1', hs2', hs3'⟩ := opZ_expand (c := c) (h := h) (d := d) w'
  rw [hs1, hs1', T_toVerma_left]
  refine PolyVal3.list_sum fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  rw [primary_toVerma]
  obtain ⟨h1, h2⟩ := hs3 t ht
  have h0 : PolyVal3 c h d (w'.length + t.1.length)
      ((s'.map fun t' => t'.2 * T (neg t.1) (neg t'.1)).sum) := by
    refine PolyVal3.list_sum fun y hy => ?_
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hy
    obtain ⟨h1', h2'⟩ := hs3' t' ht'
    rw [primary_torusWord hT t.1 (hs2 t ht) t'.1 (hs2' t' ht')]
    have h3 := torusWord_deg (c := c) (h := h) (d := d) t.1 t'.1 (hs2 t ht) (hs2' t' ht')
    exact (h2'.mul h3).mono (by omega)
  exact (h2.mul h0).mono (by omega)

/-! ### Combinations of words of bounded length -/

/-- `x` is an integer combination of words of at most `n` modes. -/
inductive InL (c : R) : ℕ → VirEnv R c → Prop
  | word {n : ℕ} (w : List ℤ) (hw : w.length ≤ n) : InL c n (opZ c w)
  | zero (n : ℕ) : InL c n 0
  | add {n : ℕ} {x y : VirEnv R c} : InL c n x → InL c n y → InL c n (x + y)
  | zsmul {n : ℕ} (z : ℤ) {x : VirEnv R c} : InL c n x → InL c n (z • x)

theorem InL.mono {n m : ℕ} {x : VirEnv R c} (hx : InL c n x) (hnm : n ≤ m) : InL c m x := by
  revert hnm
  induction hx with
  | word w hw => intro hnm; exact InL.word w (hw.trans hnm)
  | zero => intro _; exact InL.zero m
  | add _ _ ih1 ih2 => intro hnm; exact InL.add (ih1 hnm) (ih2 hnm)
  | zsmul z _ ih => intro hnm; exact InL.zsmul z (ih hnm)

theorem InL.sub {n : ℕ} {x y : VirEnv R c} (hx : InL c n x) (hy : InL c n y) :
    InL c n (x - y) := by
  rw [sub_eq_add_neg, ← neg_one_zsmul]
  exact hx.add (InL.zsmul (-1) hy)

theorem InL.mulL {n : ℕ} {x : VirEnv R c} (hx : InL c n x) (a : ℤ) :
    InL c (n + 1) (VirEnv.L c a * x) := by
  induction hx with
  | word w hw =>
    rw [← opZ_cons]
    exact InL.word (a :: w) (by simp; omega)
  | zero => rw [mul_zero]; exact InL.zero _
  | add _ _ ih1 ih2 => rw [mul_add]; exact ih1.add ih2
  | zsmul z _ ih => rw [mul_smul_comm]; exact InL.zsmul z ih

theorem comm_L_pm {m : ℤ} (hm : m = 1 ∨ m = -1) (a : ℤ) :
    VirEnv.L c m * VirEnv.L c a - VirEnv.L c a * VirEnv.L c m = (m - a) • VirEnv.L c (m + a) := by
  rw [VirEnv.L_mul_L]
  have hz : (if m + a = 0 then algebraMap R (VirEnv R c) (centralTerm c m) else 0) = 0 := by
    split_ifs
    · rcases hm with rfl | rfl <;> simp
    · rfl
  rw [hz, add_zero, add_sub_cancel_left]
  exact Int.cast_smul_eq_zsmul R (m - a) (VirEnv.L c (m + a))

theorem InL.ad_word {m : ℤ} (hm : m = 1 ∨ m = -1) (w : List ℤ) :
    InL c w.length (VirEnv.L c m * opZ c w - opZ c w * VirEnv.L c m) := by
  induction w with
  | nil =>
    rw [opZ_nil, mul_one, one_mul, sub_self]
    exact InL.zero _
  | cons a w ih =>
    have e : VirEnv.L c m * opZ c (a :: w) - opZ c (a :: w) * VirEnv.L c m =
        (VirEnv.L c m * VirEnv.L c a - VirEnv.L c a * VirEnv.L c m) * opZ c w +
          VirEnv.L c a * (VirEnv.L c m * opZ c w - opZ c w * VirEnv.L c m) := by
      rw [opZ_cons]
      simp only [sub_mul, mul_sub, mul_assoc]
      abel
    rw [e, comm_L_pm hm, smul_mul_assoc, ← opZ_cons]
    have h1 : InL c (a :: w).length ((m - a) • opZ c ((m + a) :: w)) :=
      InL.zsmul _ (InL.word _ (by simp))
    have h2 : InL c (a :: w).length
        (VirEnv.L c a * (VirEnv.L c m * opZ c w - opZ c w * VirEnv.L c m)) := by
      have := ih.mulL a
      simpa only [List.length_cons] using this
    exact h1.add h2

theorem InL.ad {m : ℤ} (hm : m = 1 ∨ m = -1) {n : ℕ} {x : VirEnv R c} (hx : InL c n x) :
    InL c n (VirEnv.L c m * x - x * VirEnv.L c m) := by
  induction hx with
  | word w hw => exact (InL.ad_word hm w).mono hw
  | zero => rw [mul_zero, zero_mul, sub_zero]; exact InL.zero _
  | add _ _ ih1 ih2 =>
    have := ih1.add ih2
    convert this using 1
    rw [mul_add, add_mul]
    abel
  | zsmul z _ ih =>
    rw [mul_smul_comm, smul_mul_assoc, ← zsmul_sub]
    exact InL.zsmul z ih

theorem InL.adp {n : ℕ} {x : VirEnv R c} (hx : InL c n x) (p : ℕ) :
    InL c n (adp (VirEnv.L c 1) p x) := by
  induction p with
  | zero => rw [adp_zero]; exact hx
  | succ p ih => rw [adp_succ]; exact InL.ad (Or.inl rfl) ih

theorem InL.nadp {n : ℕ} {x : VirEnv R c} (hx : InL c n x) (q : ℕ) :
    InL c n (nadp (VirEnv.L c (-1)) q x) := by
  induction q with
  | zero => exact hx
  | succ q ih =>
    rw [nadp_succ]
    have := InL.zsmul (-1) (InL.ad (Or.inr rfl) ih)
    rw [neg_one_zsmul, neg_sub] at this
    exact this

theorem InL.negOp (μ : List ℕ) : InL c μ.length (VirEnv.negOp c μ) := by
  have : VirEnv.negOp c μ = opZ c (μ.map fun y => -(y : ℤ)) := by
    simp [VirEnv.negOp, opZ, List.map_map, Function.comp_def]
  rw [this]
  exact InL.word _ (by simp)

theorem T_InL_deg {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hT : IsPrimaryPairing d T)
    {n m : ℕ} {x y : VirEnv R c} (hx : InL c n x) (hy : InL c m y) :
    PolyVal3 c h d (n + m) (T (x • (hw : Verma R c h)) (y • (hw : Verma R c h))) := by
  induction hx with
  | word w hw =>
    induction hy with
    | word w' hw' => exact (T_opZ_deg hT w w').mono (by omega)
    | zero => rw [zero_smul, map_zero]; exact PolyVal3.zero _
    | add _ _ ih1 ih2 => rw [add_smul, map_add]; exact ih1.add ih2
    | zsmul z _ ih =>
      rw [smul_assoc, ← Int.cast_smul_eq_zsmul R z, LinearMap.map_smul, smul_eq_mul]
      exact ((PolyVal3.intCast z).mul ih).mono (by omega)
  | zero => rw [zero_smul, map_zero, LinearMap.zero_apply]; exact PolyVal3.zero _
  | add _ _ ih1 ih2 => rw [add_smul, map_add, LinearMap.add_apply]; exact ih1.add ih2
  | zsmul z _ ih =>
    rw [smul_assoc, ← Int.cast_smul_eq_zsmul R z, LinearMap.map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    exact ((PolyVal3.intCast z).mul ih).mono (by omega)

/-- The local bracket has degree at most `ℓ(μ_r) + ℓ(μ_0)` in `(c, Δ, d)` (paper.tex l.1349–1352). -/
theorem torBr_deg {T : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R} (hT : IsPrimaryPairing d T)
    (μr μ0 : List ℕ) (p1 s p2 q : ℕ) :
    PolyVal3 c h d (μr.length + μ0.length) (torBr T μr μ0 p1 s p2 q) :=
  T_InL_deg hT (((InL.negOp μr).nadp p1).adp s) (((InL.negOp μ0).adp p2).nadp q)

end Virasoro.H13C
