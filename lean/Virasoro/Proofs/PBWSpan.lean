import Virasoro.Proofs.VermaSpan
import Mathlib.Data.List.Perm.Basic

/-!
# The Poincaré–Birkhoff–Witt vectors span the Verma module

Reordering the negative modes with `[L_{-a}, L_{-b}] = (b - a) L_{-a-b}` shows that every vector
`L_{-w}|h⟩`, for a word `w` of positive integers of level `N`, is a combination of the vectors
`L_{-Y}|h⟩` with `Y` a partition of `N`.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

namespace Verma

/-- The span of the vectors `L_{-u}|h⟩` over words of positive integers of level `N` and length
at most `r`. -/
noncomputable def lowSpan (N r : ℕ) : Submodule R (Verma R c h) :=
  Submodule.span R {v | ∃ u : List ℕ, PosWord u ∧ u.sum = N ∧ u.length ≤ r ∧ v = neg u}

theorem lowSpan_mono {N r r' : ℕ} (hr : r ≤ r') :
    (lowSpan N r : Submodule R (Verma R c h)) ≤ lowSpan N r' := by
  refine Submodule.span_mono ?_
  rintro v ⟨u, hu, hs, hl, rfl⟩
  exact ⟨u, hu, hs, hl.trans hr, rfl⟩

theorem L_neg_mem_lowSpan {N r : ℕ} {x : ℕ} (hx : 0 < x) {v : Verma R c h}
    (hv : v ∈ lowSpan N r) : L (-(x : ℤ)) v ∈ lowSpan (x + N) (r + 1) := by
  refine Submodule.span_induction (p := fun v _ => L (-(x : ℤ)) v ∈ lowSpan (x + N) (r + 1))
    ?_ ?_ ?_ ?_ hv
  · rintro v ⟨u, hu, hs, hl, rfl⟩
    refine Submodule.subset_span ⟨x :: u, ?_, ?_, ?_, (neg_cons x u).symm⟩
    · intro z hz
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hx
      · exact hu z hz
    · rw [List.sum_cons, hs]
    · rw [List.length_cons]; omega
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro a b _ hb
    rw [map_smul]; exact Submodule.smul_mem _ _ hb

/-- Rearranging the letters of a word changes `L_{-w}|h⟩` by a combination of shorter words of
the same level. -/
theorem neg_perm_sub_mem {w w' : List ℕ} (hp : w.Perm w') (hw : PosWord w) :
    neg (c := c) (h := h) w - neg w' ∈ lowSpan w.sum (w.length - 1) := by
  induction hp with
  | nil => rw [sub_self]; exact Submodule.zero_mem _
  | cons x hl ih =>
    rename_i l l'
    have hx : 0 < x := hw x List.mem_cons_self
    have hl' : PosWord l := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    by_cases h0 : l = []
    · subst h0
      rw [List.nil_perm.1 hl, sub_self]
      exact Submodule.zero_mem _
    · have hlen : 0 < l.length := List.length_pos_iff.2 h0
      have := L_neg_mem_lowSpan (c := c) (h := h) hx (ih hl')
      rw [map_sub, ← neg_cons, ← neg_cons] at this
      rw [List.sum_cons, List.length_cons]
      refine lowSpan_mono ?_ this
      omega
  | swap x y l =>
    have hx : 0 < x := hw x (List.mem_cons_of_mem _ List.mem_cons_self)
    have hy : 0 < y := hw y List.mem_cons_self
    have hl' : PosWord l := fun z hz =>
      hw z (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz))
    have e : neg (c := c) (h := h) (y :: x :: l) - neg (x :: y :: l)
        = (((-(y : ℤ)) - (-(x : ℤ)) : ℤ) : R) • neg ((y + x) :: l) := by
      rw [neg_cons, neg_cons, neg_cons x, neg_cons y, neg_cons (y + x), L_L,
        if_neg (by omega)]
      push_cast
      rw [show -(y : ℤ) + -(x : ℤ) = -((y : ℤ) + x) by ring]
      module
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨(y + x) :: l, ?_, ?_, ?_, rfl⟩)
    · intro z hz
      rw [List.mem_cons] at hz
      rcases hz with rfl | hz
      · omega
      · exact hl' z hz
    · simp only [List.sum_cons]; omega
    · simp only [List.length_cons]; omega
  | trans h1 h2 ih1 ih2 =>
    rename_i l₁ l₂ l₃
    have hw2 : PosWord l₂ := fun z hz => hw z (h1.symm.subset hz)
    have e : neg (c := c) (h := h) l₁ - neg l₃ = (neg l₁ - neg l₂) + (neg l₂ - neg l₃) := by abel
    rw [e]
    refine Submodule.add_mem _ (ih1 hw) ?_
    have := ih2 hw2
    rwa [← h1.sum_eq, ← h1.length_eq] at this

/-- The partition whose parts are the letters of a word of positive integers. -/
def partOfWord (w : List ℕ) (hw : PosWord w) : Nat.Partition w.sum where
  parts := (w : Multiset ℕ)
  parts_pos := fun {i} hi => hw i (Multiset.mem_coe.1 hi)
  parts_sum := Multiset.sum_coe w

theorem partOfWord_word_perm (w : List ℕ) (hw : PosWord w) :
    (partOfWord w hw).word.Perm w := by
  have h : (((partOfWord w hw).word : List ℕ) : Multiset ℕ) = (w : Multiset ℕ) := by
    rw [Nat.Partition.word, Multiset.sort_eq]
    rfl
  exact Multiset.coe_eq_coe.1 h

theorem neg_word_mem_level {N : ℕ} (Y : Nat.Partition N) :
    neg (c := c) (h := h) Y.word ∈ level N := by
  classical
  refine ⟨Pi.single Y 1, ?_⟩
  simp only [pbwCoord, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_eq_single Y]
  · rw [Pi.single_eq_same, one_smul]
  · intro Y' _ hne
    rw [Pi.single_eq_of_ne hne, zero_smul]
  · intro hY
    exact absurd (Finset.mem_univ Y) hY

/-- Every vector `L_{-w}|h⟩`, for a word of positive integers, lies in the level `|w|`. -/
theorem neg_mem_level : ∀ (r : ℕ) (w : List ℕ), PosWord w → w.length ≤ r →
    neg (c := c) (h := h) w ∈ level w.sum := by
  intro r
  induction r with
  | zero =>
    intro w hw hlen
    have hperm := partOfWord_word_perm w hw
    have h0 : w = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
    have h1 : (partOfWord w hw).word = w := by
      subst h0
      exact List.perm_nil.1 hperm
    have h3 := neg_word_mem_level (c := c) (h := h) (partOfWord w hw)
    rwa [h1] at h3
  | succ r ih =>
    intro w hw hlen
    have hperm := partOfWord_word_perm w hw
    have hsub := neg_perm_sub_mem (c := c) (h := h) hperm.symm hw
    have hle : (lowSpan w.sum (w.length - 1) : Submodule R (Verma R c h)) ≤ level w.sum := by
      refine Submodule.span_le.2 ?_
      rintro v ⟨u, hu, hs, hl, rfl⟩
      have := ih u hu (by omega)
      rwa [hs] at this
    have h2 := hle hsub
    have h3 := neg_word_mem_level (c := c) (h := h) (partOfWord w hw)
    have e : neg (c := c) (h := h) w
        = (neg w - neg (partOfWord w hw).word) + neg (partOfWord w hw).word := by abel
    rw [e]
    exact Submodule.add_mem _ h2 h3

/-- The levels span the Verma module. -/
theorem iSup_level_eq_top : (⨆ N : ℕ, (level N : Submodule R (Verma R c h))) = ⊤ := by
  rw [eq_top_iff, ← posSpan_eq_top]
  refine Submodule.span_le.2 ?_
  rintro v ⟨w, hw, rfl⟩
  exact Submodule.mem_iSup_of_mem w.sum (neg_mem_level w.length w hw le_rfl)

end Verma

end Virasoro
