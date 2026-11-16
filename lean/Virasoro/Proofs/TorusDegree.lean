import Virasoro.Proofs.DefMatrices
import Virasoro.Proofs.Shapovalov

/-!
# Degree of the torus matrix entries in the internal weight

Over `𝔽[X]` with internal weight `X`: the entries `⟨Δ|L_Y V_d(1) L_{-w}|Δ⟩` have degree at most
`min(ℓ(Y), ℓ(w))`, and for words of equal level the difference between the torus entry and the
Shapovalov entry has degree strictly below `min(ℓ(Y), ℓ(w))`: a term using a Ward commutator has
consumed a mode without producing a factor of the weight.
-/

namespace Virasoro

open Polynomial

section General

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Level conservation: every word of `L_k w` has level `|w| - k`. -/
theorem actWord_sum (c h : R) : ∀ (w : List ℕ) (k : ℤ), ∀ t ∈ actWord c h k w,
    ((t.1.sum : ℕ) : ℤ) = (w.sum : ℕ) - k
  | [], k => by
    intro t ht
    unfold actWord at ht
    split_ifs at ht with h1 h2
    · simp only [List.mem_singleton] at ht
      subst ht
      simp only [List.sum_cons, List.sum_nil, Nat.cast_add, Nat.cast_zero]
      omega
    · simp only [List.mem_singleton] at ht
      subst ht
      simp only [List.sum_nil, Nat.cast_zero]
      omega
    · simp at ht
  | y :: w, k => by
    intro t ht
    unfold actWord at ht
    split_ifs at ht with h1 h2 h3
    · simp only [List.mem_singleton] at ht
      subst ht
      simp only [List.sum_cons, Nat.cast_add]
      omega
    · simp only [List.mem_singleton] at ht
      subst ht
      simp only [List.sum_cons, Nat.cast_add]
      omega
    · simp only [List.mem_append, List.mem_map, List.mem_singleton] at ht
      rcases ht with (⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩) | rfl
      · have := actWord_sum c h w k t' ht'
        simp only [List.sum_cons, Nat.cast_add]
        omega
      · have := actWord_sum c h w (k - y) t' ht'
        simp only [List.sum_cons, Nat.cast_add]
        omega
      · simp only [List.sum_cons, Nat.cast_add]
        omega
    · simp only [List.append_nil, List.mem_append, List.mem_map] at ht
      rcases ht with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
      · have := actWord_sum c h w k t' ht'
        simp only [List.sum_cons, Nat.cast_add]
        omega
      · have := actWord_sum c h w (k - y) t' ht'
        simp only [List.sum_cons, Nat.cast_add]
        omega

omit [Algebra ℚ R] in
theorem list_sum_map_sub {α : Type*} (l : List α) (f g : α → R) :
    (l.map fun t => f t - g t).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

/-- `⟨h| L_Y L_y L_{-w} |h⟩` expanded through `L_y L_{-w}|h⟩`. -/
theorem gramWord_cons (c h : R) (y : ℕ) (Y w : List ℕ) (hw : PosWord w) :
    gramWord c h (y :: Y) w
      = ((actWord c h (y : ℤ) w).map fun t => t.2 * gramWord c h Y t.1).sum := by
  have hB := Verma.isShapovalov_shap (c := c) (h := h)
  rw [← hB.gramWord (y :: Y) w hw, Verma.neg_cons, hB.2, neg_neg, Verma.L_neg_actWord,
    Verma.primary_toVerma]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [hB.gramWord Y t.1 (posSt_actWord c h hw (y : ℤ) t ht)]

end General

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- `p.degree < m`. -/
def DLt (p : 𝔽[X]) (m : ℕ) : Prop := p.degree < (m : WithBot ℕ)

omit [CharZero 𝔽] in
theorem dlt_zero (m : ℕ) : DLt (0 : 𝔽[X]) m := by
  rw [DLt, degree_zero]
  exact WithBot.bot_lt_coe m

omit [CharZero 𝔽] in
theorem dlt_of_natDegree_lt {p : 𝔽[X]} {m : ℕ} (h : p.natDegree < m) : DLt p m :=
  lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 h)

omit [CharZero 𝔽] in
theorem DLt.natDegree_lt {p : 𝔽[X]} {m : ℕ} (h : DLt p m) (hp : p ≠ 0) : p.natDegree < m :=
  (natDegree_lt_iff_degree_lt hp).2 h

omit [CharZero 𝔽] in
theorem DLt.add {p q : 𝔽[X]} {m : ℕ} (hp : DLt p m) (hq : DLt q m) : DLt (p + q) m :=
  lt_of_le_of_lt (degree_add_le p q) (max_lt hp hq)

omit [CharZero 𝔽] in
theorem DLt.mono {p : 𝔽[X]} {m m' : ℕ} (hp : DLt p m) (hm : m ≤ m') : DLt p m' :=
  lt_of_lt_of_le hp (WithBot.coe_le_coe.2 hm)

omit [CharZero 𝔽] in
theorem DLt.mul {a p : 𝔽[X]} {e k : ℕ} (ha : a.natDegree ≤ e) (hp : DLt p k) :
    DLt (a * p) (e + k) := by
  by_cases h0 : p = 0
  · rw [h0, mul_zero]; exact dlt_zero _
  · have h1 := hp.natDegree_lt h0
    have h2 := natDegree_mul_le (p := a) (q := p)
    exact dlt_of_natDegree_lt (by omega)

omit [CharZero 𝔽] in
theorem dlt_list_sum {l : List 𝔽[X]} {m : ℕ} (h : ∀ p ∈ l, DLt p m) : DLt l.sum m := by
  induction l with
  | nil => exact dlt_zero m
  | cons a l ih =>
    rw [List.sum_cons]
    exact (h a List.mem_cons_self).add (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

omit [CharZero 𝔽] in
theorem dlt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → 𝔽[X]) {m : ℕ}
    (h : ∀ i ∈ s, DLt (f i) m) : DLt (∑ i ∈ s, f i) m := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact dlt_zero m
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

section Torus

variable (c₀ d₀ : 𝔽)

theorem natDegree_phi (w : List ℕ) : (phi (C d₀ : 𝔽[X]) w).natDegree = 0 := by
  rw [phi_map (C : 𝔽 →+* 𝔽[X]) d₀ w, natDegree_C]

omit [CharZero 𝔽] in
theorem wardScalar_eq (Y w : List ℕ) (y : ℕ) :
    (((Y.sum : ℕ) : 𝔽[X]) - ((w.sum : ℕ) : 𝔽[X]) + (y : 𝔽[X]) * C d₀)
      = C (((Y.sum : ℕ) : 𝔽) - ((w.sum : ℕ) : 𝔽) + (y : 𝔽) * d₀) := by
  simp only [map_add, map_sub, map_mul, map_natCast]

/-- `deg_Δ ⟨Δ|L_Y V_d(1) L_{-w}|Δ⟩ ≤ ℓ(Y)`. -/
theorem natDegree_torusWord_le_left : ∀ (Y : List ℕ), PosWord Y → ∀ w : List ℕ,
    (torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w).natDegree ≤ Y.length
  | [], _, w => by rw [torusWord, natDegree_phi]; exact Nat.zero_le _
  | y :: Y, hY, w => by
    have hy : 0 < y := hY y List.mem_cons_self
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    rw [torusWord, wardScalar_eq]
    refine natDegree_add_le_of_degree_le (natDegree_list_sum_le_of fun p hp => ?_) ?_
    · rw [List.mem_map] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      have h1 := actWord_degree_pos c₀ w (show (0 : ℤ) < (y : ℤ) by exact_mod_cast hy) ht
      have h2 := natDegree_torusWord_le_left Y hY' t.1
      have h3 := natDegree_mul_le (p := t.2) (q := torusWord (C c₀ : 𝔽[X]) X (C d₀) Y t.1)
      simp only [List.length_cons]
      omega
    · have h2 := natDegree_torusWord_le_left Y hY' w
      have h3 := natDegree_C_mul_le (((Y.sum : ℕ) : 𝔽) - ((w.sum : ℕ) : 𝔽) + (y : 𝔽) * d₀)
        (torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w)
      simp only [List.length_cons]
      omega

/-- `deg_Δ ⟨Δ|L_Y V_d(1) L_{-w}|Δ⟩ ≤ ℓ(w)`. -/
theorem natDegree_torusWord_le_right : ∀ (Y : List ℕ), PosWord Y → ∀ w : List ℕ,
    (torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w).natDegree ≤ w.length
  | [], _, w => by rw [torusWord, natDegree_phi]; exact Nat.zero_le _
  | y :: Y, hY, w => by
    have hy : 0 < y := hY y List.mem_cons_self
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    rw [torusWord, wardScalar_eq]
    refine natDegree_add_le_of_degree_le (natDegree_list_sum_le_of fun p hp => ?_) ?_
    · rw [List.mem_map] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      have h1 := actWord_degree_pos c₀ w (show (0 : ℤ) < (y : ℤ) by exact_mod_cast hy) ht
      have h2 := natDegree_torusWord_le_right Y hY' t.1
      have h3 := natDegree_mul_le (p := t.2) (q := torusWord (C c₀ : 𝔽[X]) X (C d₀) Y t.1)
      omega
    · have h2 := natDegree_torusWord_le_right Y hY' w
      have h3 := natDegree_C_mul_le (((Y.sum : ℕ) : 𝔽) - ((w.sum : ℕ) : 𝔽) + (y : 𝔽) * d₀)
        (torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w)
      omega

/-- If the level of `w` exceeds the level of `Y`, not every letter of `w` can be contracted:
`deg_Δ ⟨Δ|L_Y V_d(1) L_{-w}|Δ⟩ < ℓ(w)`. -/
theorem natDegree_torusWord_lt : ∀ (Y : List ℕ), PosWord Y → ∀ w : List ℕ, Y.sum < w.sum →
    (torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w).natDegree < w.length
  | [], _, w => by
    intro hw
    rw [torusWord, natDegree_phi]
    cases w with
    | nil => simp at hw
    | cons a w => simp
  | y :: Y, hY, w => by
    intro hw
    have hy : 0 < y := hY y List.mem_cons_self
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    rw [List.sum_cons] at hw
    have hlen : 0 < w.length := by
      cases w with
      | nil => simp at hw
      | cons a w => simp
    rw [torusWord, wardScalar_eq]
    have key : ((((actWord (C c₀ : 𝔽[X]) X (y : ℤ) w).map fun t =>
        t.2 * torusWord (C c₀ : 𝔽[X]) X (C d₀) Y t.1).sum
        + C (((Y.sum : ℕ) : 𝔽) - ((w.sum : ℕ) : 𝔽) + (y : 𝔽) * d₀)
          * torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w)).natDegree ≤ w.length - 1 := by
      refine natDegree_add_le_of_degree_le (natDegree_list_sum_le_of fun p hp => ?_) ?_
      · rw [List.mem_map] at hp
        obtain ⟨t, ht, rfl⟩ := hp
        have h1 := actWord_degree_pos c₀ w (show (0 : ℤ) < (y : ℤ) by exact_mod_cast hy) ht
        have hs := actWord_sum (C c₀ : 𝔽[X]) X w (y : ℤ) t ht
        have h2 := natDegree_torusWord_lt Y hY' t.1 (by omega)
        have h3 := natDegree_mul_le (p := t.2) (q := torusWord (C c₀ : 𝔽[X]) X (C d₀) Y t.1)
        omega
      · have h2 := natDegree_torusWord_lt Y hY' w (by omega)
        have h3 := natDegree_C_mul_le (((Y.sum : ℕ) : 𝔽) - ((w.sum : ℕ) : 𝔽) + (y : 𝔽) * d₀)
          (torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w)
        omega
    omega

/-- For words of equal level, the torus entry and the Shapovalov entry agree in degree
`min(ℓ(Y), ℓ(w))`. -/
theorem dlt_torusWord_sub_gramWord : ∀ (Y : List ℕ), PosWord Y → ∀ w : List ℕ, PosWord w →
    Y.sum = w.sum →
    DLt (torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w - gramWord (C c₀ : 𝔽[X]) X Y w)
      (min Y.length w.length)
  | [], _, w => by
    intro hw hsum
    have hw0 : w = [] := by
      cases w with
      | nil => rfl
      | cons a w =>
        have ha : 0 < a := hw a List.mem_cons_self
        simp at hsum
        omega
    subst hw0
    have : torusWord (C c₀ : 𝔽[X]) X (C d₀) [] [] - gramWord (C c₀ : 𝔽[X]) X [] [] = 0 := by
      simp [torusWord, phi, gramWord, vac]
    rw [this]
    exact dlt_zero _
  | y :: Y, hY, w => by
    intro hw hsum
    have hy : 0 < y := hY y List.mem_cons_self
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    rw [List.sum_cons] at hsum
    rw [torusWord, wardScalar_eq, gramWord_cons _ _ y Y w hw, add_sub_right_comm,
      ← list_sum_map_sub]
    refine DLt.add (dlt_list_sum fun p hp => ?_) ?_
    · rw [List.mem_map] at hp
      obtain ⟨t, ht, rfl⟩ := hp
      have h1 := actWord_degree_pos c₀ w (show (0 : ℤ) < (y : ℤ) by exact_mod_cast hy) ht
      have hs := actWord_sum (C c₀ : 𝔽[X]) X w (y : ℤ) t ht
      have hpos := posSt_actWord (C c₀ : 𝔽[X]) X hw (y : ℤ) t ht
      have h2 := dlt_torusWord_sub_gramWord Y hY' t.1 hpos (by omega)
      rw [← mul_sub]
      refine (DLt.mul (le_refl _) h2).mono ?_
      simp only [List.length_cons]
      omega
    · have h2 := natDegree_torusWord_lt c₀ d₀ Y hY' w (by omega)
      have h4 := natDegree_torusWord_le_left c₀ d₀ Y hY' w
      have h3 := natDegree_C_mul_le (((Y.sum : ℕ) : 𝔽) - ((w.sum : ℕ) : 𝔽) + (y : 𝔽) * d₀)
        (torusWord (C c₀ : 𝔽[X]) X (C d₀) Y w)
      refine dlt_of_natDegree_lt ?_
      simp only [List.length_cons]
      omega

end Torus

end Virasoro
