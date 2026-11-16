import Virasoro.Proofs.VermaBasic
import Virasoro.Proofs.NegAlg

/-!
# Normal ordering in the Verma module and the spanning property

The normal-ordering procedure `actWord` computes the action of the modes on the vectors
`L_{-w₁} ⋯ L_{-w_r} |h⟩`, and these vectors, for words of positive integers, span the Verma
module.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace St

theorem toVerma_nil : St.toVerma (c := c) (h := h) ([] : St R) = 0 := rfl

theorem toVerma_cons (t : List ℕ × R) (s : St R) :
    St.toVerma (c := c) (h := h) (t :: s) = t.2 • Verma.neg t.1 + St.toVerma s := by
  simp [St.toVerma]

theorem toVerma_append (s s' : St R) :
    St.toVerma (c := c) (h := h) (s ++ s') = St.toVerma s + St.toVerma s' := by
  simp [St.toVerma]

theorem toVerma_single (w : List ℕ) (a : R) :
    St.toVerma (c := c) (h := h) [(w, a)] = a • Verma.neg w := by
  rw [toVerma_cons, toVerma_nil, add_zero]

theorem toVerma_map_cons (y : ℕ) (s : St R) :
    St.toVerma (c := c) (h := h) (s.map fun t => (y :: t.1, t.2))
      = Verma.L (-(y : ℤ)) (St.toVerma s) := by
  induction s with
  | nil => rw [List.map_nil, toVerma_nil, map_zero]
  | cons t s ih =>
    rw [List.map_cons, toVerma_cons, toVerma_cons, ih, map_add, map_smul, Verma.neg_cons]

theorem toVerma_map_smul (a : R) (s : St R) :
    St.toVerma (c := c) (h := h) (s.map fun t => (t.1, a * t.2)) = a • St.toVerma s := by
  induction s with
  | nil => rw [List.map_nil, toVerma_nil, smul_zero]
  | cons t s ih =>
    rw [List.map_cons, toVerma_cons, toVerma_cons, ih, smul_add, smul_smul]

theorem toVerma_map_smul_right (a : R) (s : St R) :
    St.toVerma (c := c) (h := h) (s.map fun t => (t.1, a * t.2)) = a • St.toVerma s :=
  toVerma_map_smul a s

end St

namespace Verma

/-- `L_0` acts on `L_{-w}|h⟩` by `h + |w|`. -/
theorem L_zero_neg (w : List ℕ) :
    L 0 (neg (c := c) (h := h) w) = (h + ((w.sum : ℕ) : R)) • neg w := by
  induction w with
  | nil => rw [neg_nil, L_hw_zero, List.sum_nil, Nat.cast_zero, add_zero]
  | cons y w ih =>
    rw [neg_cons, L_L, ih, map_smul, List.sum_cons]
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

/-- The normal-ordering procedure computes the action of the modes. -/
theorem L_neg_actWord (w : List ℕ) : ∀ k : ℤ,
    L k (neg (c := c) (h := h) w) = St.toVerma (actWord c h k w) := by
  induction w with
  | nil =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk, St.toVerma_single, one_smul, neg_cons, neg_nil]
      have : -((k.natAbs : ℕ) : ℤ) = k := by omega
      rw [this]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0, St.toVerma_single, neg_nil, hk0, L_hw_zero]
      · rw [if_neg hk0, St.toVerma_nil, neg_nil, L_hw_pos (by omega)]
  | cons y w ih =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk, St.toVerma_single, one_smul, neg_cons (k.natAbs)]
      have : -((k.natAbs : ℕ) : ℤ) = k := by omega
      rw [this]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0, St.toVerma_single, hk0, L_zero_neg, List.sum_cons]
      · rw [if_neg hk0, St.toVerma_append, St.toVerma_append, St.toVerma_map_cons,
          St.toVerma_map_smul, ← ih k, ← ih (k - y), neg_cons, L_L]
        have e1 : k + -(y : ℤ) = k - y := by ring
        have e2 : k - -(y : ℤ) = k + y := by ring
        rw [e1, e2]
        congr 1
        by_cases hky : k = y
        · rw [if_pos hky, if_pos (by omega), St.toVerma_single]
        · rw [if_neg hky, if_neg (by omega), St.toVerma_nil]

end Verma

/-- The normal-ordering procedure on linear combinations of words. -/
theorem St.toVerma_actSt (k : ℤ) (s : St R) :
    St.toVerma (c := c) (h := h) (actSt c h k s) = Verma.L k (St.toVerma s) := by
  induction s with
  | nil => simp [actSt, St.toVerma_nil]
  | cons t s ih =>
    have e : actSt c h k (t :: s)
        = ((actWord c h k t.1).map fun u => (u.1, t.2 * u.2)) ++ actSt c h k s := by
      simp [actSt]
    rw [e, St.toVerma_append, ih, St.toVerma_map_smul, St.toVerma_cons, map_add, map_smul,
      Verma.L_neg_actWord]

/-- Words of positive integers. -/
def PosWord (w : List ℕ) : Prop := ∀ y ∈ w, 0 < y

/-- Lists of (word, coefficient) pairs all of whose words consist of positive integers. -/
def PosSt (s : St R) : Prop := ∀ t ∈ s, PosWord t.1

theorem posSt_actWord (c h : R) {w : List ℕ} (hw : PosWord w) :
    ∀ k : ℤ, PosSt (actWord c h k w) := by
  induction w with
  | nil =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk]
      intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      intro y hy
      rw [List.mem_singleton] at hy
      omega
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0]
        intro t ht
        rw [List.mem_singleton] at ht
        subst ht
        intro y hy
        simp at hy
      · rw [if_neg hk0]
        intro t ht
        simp at ht
  | cons y w ih =>
    intro k
    have hy : 0 < y := hw y (List.mem_cons_self)
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk]
      intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      intro z hz
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · exact hw z hz
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0]
        intro t ht
        rw [List.mem_singleton] at ht
        subst ht
        exact hw
      · rw [if_neg hk0]
        intro t ht
        rw [List.mem_append, List.mem_append] at ht
        rcases ht with (ht | ht) | ht
        · rw [List.mem_map] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          intro z hz
          rw [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hy
          · exact ih hw' k u hu z hz
        · rw [List.mem_map] at ht
          obtain ⟨u, hu, rfl⟩ := ht
          exact ih hw' (k - y) u hu
        · by_cases hky : k = y
          · rw [if_pos hky, List.mem_singleton] at ht
            subst ht
            exact hw'
          · rw [if_neg hky] at ht
            simp at ht

theorem posSt_actSt (c h : R) (k : ℤ) {s : St R} (hs : PosSt s) : PosSt (actSt c h k s) := by
  intro t ht
  rw [actSt, List.mem_flatMap] at ht
  obtain ⟨u, hu, ht⟩ := ht
  rw [List.mem_map] at ht
  obtain ⟨v, hv, rfl⟩ := ht
  exact posSt_actWord c h (hs u hu) k v hv

namespace Verma

/-- The span of the vectors `L_{-w}|h⟩` over words of positive integers. -/
noncomputable def posSpan : Submodule R (Verma R c h) :=
  Submodule.span R {v | ∃ w : List ℕ, PosWord w ∧ v = neg w}

theorem toVerma_mem_posSpan {s : St R} (hs : PosSt s) :
    St.toVerma (c := c) (h := h) s ∈ posSpan := by
  induction s with
  | nil => rw [St.toVerma_nil]; exact Submodule.zero_mem _
  | cons t s ih =>
    rw [St.toVerma_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_)) (ih ?_)
    · exact ⟨t.1, hs t (List.mem_cons_self), rfl⟩
    · exact fun u hu => hs u (List.mem_cons_of_mem _ hu)

theorem L_mem_posSpan (k : ℤ) {v : Verma R c h} (hv : v ∈ posSpan) : L k v ∈ posSpan := by
  refine Submodule.span_induction (p := fun v _ => L k v ∈ posSpan) ?_ ?_ ?_ ?_ hv
  · rintro v ⟨w, hw, rfl⟩
    rw [L_neg_actWord]
    exact toVerma_mem_posSpan (posSt_actWord c h hw k)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem env_smul_mem_posSpan (x : VirEnv R c) {v : Verma R c h} (hv : v ∈ posSpan) :
    x • v ∈ posSpan := by
  obtain ⟨x, rfl⟩ := RingQuot.mkAlgHom_surjective R (VirRel R c) x
  induction x using FreeAlgebra.induction generalizing v with
  | grade0 r =>
    rw [AlgHom.commutes, algebraMap_smul]
    exact Submodule.smul_mem _ _ hv
  | grade1 n => exact L_mem_posSpan n hv
  | add x y hx hy =>
    rw [map_add, add_smul]
    exact Submodule.add_mem _ (hx hv) (hy hv)
  | mul x y hx hy =>
    rw [map_mul, mul_smul]
    exact hx (hy hv)

/-- The vectors `L_{-w}|h⟩`, for words `w` of positive integers, span the Verma module. -/
theorem posSpan_eq_top : (posSpan : Submodule R (Verma R c h)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  induction v using Submodule.Quotient.induction_on with
  | H x =>
    have h1 : (hw : Verma R c h) ∈ posSpan :=
      Submodule.subset_span ⟨[], fun y hy => by simp at hy, neg_nil.symm⟩
    have := env_smul_mem_posSpan x h1
    rwa [hw_eq, env_smul_mk, mul_one] at this

/-- Induction over the Verma module through the spanning vectors `L_{-w}|h⟩`. -/
theorem induction_neg {P : Verma R c h → Prop} (hneg : ∀ w : List ℕ, PosWord w → P (neg w))
    (hadd : ∀ u v, P u → P v → P (u + v)) (hsmul : ∀ (r : R) v, P v → P (r • v)) :
    ∀ v, P v := by
  intro v
  have hv : v ∈ (posSpan : Submodule R (Verma R c h)) := by rw [posSpan_eq_top]; trivial
  refine Submodule.span_induction (p := fun v _ => P v) ?_ ?_ ?_ ?_ hv
  · rintro v ⟨w, hw, rfl⟩
    exact hneg w hw
  · have := hsmul 0 _ (hneg [] (fun y hy => by simp at hy))
    rwa [zero_smul] at this
  · intro x y _ _ hx hy
    exact hadd x y hx hy
  · intro a x _ hx
    exact hsmul a x hx

/-- Induction over the Verma module by the action of the negative modes. -/
theorem induction_L {P : Verma R c h → Prop} (hhw : P hw)
    (hadd : ∀ u v, P u → P v → P (u + v)) (hsmul : ∀ (r : R) v, P v → P (r • v))
    (hL : ∀ m : ℤ, 0 < m → ∀ v, P v → P (L (-m) v)) : ∀ v, P v := by
  refine induction_neg (fun w hw => ?_) hadd hsmul
  induction w with
  | nil => rw [neg_nil]; exact hhw
  | cons y w ih =>
    rw [neg_cons]
    have hy : 0 < y := hw y List.mem_cons_self
    exact hL y (by omega) _ (ih fun z hz => hw z (List.mem_cons_of_mem _ hz))

/-- `L_k L_0 = L_0 L_k + k L_k`. -/
theorem L_L_zero (k : ℤ) (v : Verma R c h) : L k (L 0 v) = L 0 (L k v) + (k : R) • L k v := by
  rw [L_L, add_zero, sub_zero]
  by_cases hk : k = 0
  · rw [if_pos hk, hk, centralTerm_zero, zero_smul, add_zero]
  · rw [if_neg hk, add_zero]

/-- The Virasoro relation with the central term written through `ct`. -/
theorem L_L_ct (a b : ℤ) (v : Verma R c h) :
    L b (L a v) = L a (L b v) + ((b - a : ℤ) : R) • L (a + b) v + ct c b (-a) • v := by
  rw [L_L, add_comm b a, ct]
  congr 1
  by_cases hab : a + b = 0
  · rw [if_pos hab, if_pos (by omega)]
  · rw [if_neg hab, if_neg (by omega), zero_smul]

/-- Two linear maps on the Verma module agree if they agree on the vectors `L_{-w}|h⟩`. -/
theorem linearMap_ext {W : Type*} [AddCommGroup W] [Module R W] {f g : Verma R c h →ₗ[R] W}
    (hfg : ∀ w : List ℕ, PosWord w → f (neg w) = g (neg w)) : f = g := by
  refine LinearMap.ext fun v => ?_
  refine induction_neg (P := fun v => f v = g v) hfg ?_ ?_ v
  · intro u v hu hv
    rw [map_add, map_add, hu, hv]
  · intro r v hv
    rw [map_smul, map_smul, hv]

end Verma

end Virasoro
