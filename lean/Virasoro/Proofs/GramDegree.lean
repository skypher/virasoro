import Virasoro.Proofs.ActDegree
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.List.Perm.Basic

/-!
# Degree of the Shapovalov matrix entries in the internal weight

For words `Y`, `Y'`: `deg_Δ ⟨Δ|L_Y L_{-Y'}|Δ⟩ ≤ min(|Y|, |Y'|)` (lengths), and for words of equal
length `r` the coefficient of `Δ^r` counts the complete matchings of equal letters, weighted by
`∏ 2 y_i`; it vanishes unless `Y'` is a rearrangement of `Y` and is nonzero for `Y' = Y`.
-/

namespace Virasoro

open Polynomial

variable {𝔽 : Type*} [Field 𝔽] [CharZero 𝔽]

/-- A state reached after `i` positive modes from a word of length `L`: every coefficient has
degree at most `i`, and degree plus word length at most `L`. -/
def Adm (L i : ℕ) (s : St 𝔽[X]) : Prop :=
  ∀ t ∈ s, t.2.natDegree ≤ i ∧ t.2.natDegree + t.1.length ≤ L

theorem adm_step (c₀ : 𝔽) {L i : ℕ} {s : St 𝔽[X]} (hs : Adm L i s) {k : ℤ} (hk : 0 < k) :
    Adm L (i + 1) (actSt (C c₀ : 𝔽[X]) X k s) := by
  intro t ht
  unfold actSt at ht
  simp only [List.mem_flatMap, List.mem_map] at ht
  obtain ⟨t0, ht0, u, hu, rfl⟩ := ht
  have h1 := hs t0 ht0
  have h2 := actWord_degree_pos c₀ t0.1 hk hu
  have hmul := natDegree_mul_le (p := t0.2) (q := u.2)
  dsimp only
  constructor <;> omega

/-- The symbol of a state: the coefficients of `Δ^i` of the terms whose word has length
`L - i`, tested against a function `φ` on words. -/
noncomputable def sym (L i : ℕ) (φ : List ℕ → 𝔽) (s : St 𝔽[X]) : 𝔽 :=
  (s.map fun t => if t.1.length + i = L then t.2.coeff i * φ t.1 else 0).sum

theorem sym_nil (L i : ℕ) (φ : List ℕ → 𝔽) : sym L i φ [] = 0 := by simp [sym]

theorem sym_append (L i : ℕ) (φ : List ℕ → 𝔽) (s t : St 𝔽[X]) :
    sym L i φ (s ++ t) = sym L i φ s + sym L i φ t := by
  simp [sym]

/-- The deletion operator on test functions: `(D_k φ)(w) = ∑ 2k φ(w with one k deleted)`. -/
noncomputable def delFun (k : ℕ) (φ : List ℕ → 𝔽) : List ℕ → 𝔽 := fun w =>
  ((delOne k w).map fun u => 2 * (k : 𝔽) * φ u).sum

theorem sym_step_one (c₀ : 𝔽) {L i : ℕ} {t : List ℕ × 𝔽[X]}
    (ht : t.2.natDegree ≤ i ∧ t.2.natDegree + t.1.length ≤ L) {k : ℕ} (hk : 0 < k)
    (φ : List ℕ → 𝔽) :
    sym L (i + 1) φ ((actWord (C c₀ : 𝔽[X]) X (k : ℤ) t.1).map fun u => (u.1, t.2 * u.2)) =
      if t.1.length + i = L then t.2.coeff i * delFun k φ t.1 else 0 := by
  unfold sym
  rw [List.map_map]
  by_cases hL : t.1.length + i = L
  · rw [if_pos hL, delFun, ← actWord_top c₀ t.1 k hk φ, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro u hu
    have hd := actWord_degree_pos c₀ t.1 (show (0 : ℤ) < (k : ℤ) by exact_mod_cast hk) hu
    simp only [Function.comp_apply]
    by_cases hlen : u.1.length + 1 = t.1.length
    · rw [if_pos (by omega), if_pos hlen, coeff_mul_add_eq_of_natDegree_le ht.1 hd.1]
      ring
    · rw [if_neg (by omega), if_neg hlen, mul_zero]
  · rw [if_neg hL]
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map, Function.comp_apply] at hx
    obtain ⟨u, hu, rfl⟩ := hx
    have hd := actWord_degree_pos c₀ t.1 (show (0 : ℤ) < (k : ℤ) by exact_mod_cast hk) hu
    split_ifs with hlen
    · have hmul := natDegree_mul_le (p := t.2) (q := u.2)
      have : (t.2 * u.2).natDegree < i + 1 := by omega
      rw [coeff_eq_zero_of_natDegree_lt this, zero_mul]
    · rfl

theorem sym_step (c₀ : 𝔽) {L i : ℕ} {s : St 𝔽[X]} (hs : Adm L i s) {k : ℕ} (hk : 0 < k)
    (φ : List ℕ → 𝔽) :
    sym L (i + 1) φ (actSt (C c₀ : 𝔽[X]) X (k : ℤ) s) = sym L i (delFun k φ) s := by
  induction s with
  | nil => simp [actSt, sym]
  | cons t s ih =>
    have hs' : Adm L i s := fun x hx => hs x (List.mem_cons_of_mem _ hx)
    have ht := hs t (List.mem_cons_self ..)
    have e : actSt (C c₀ : 𝔽[X]) X (k : ℤ) (t :: s) =
        ((actWord (C c₀ : 𝔽[X]) X (k : ℤ) t.1).map fun u => (u.1, t.2 * u.2)) ++
          actSt (C c₀ : 𝔽[X]) X (k : ℤ) s := by
      simp [actSt]
    rw [e, sym_append, sym_step_one c₀ ht hk φ, ih hs']
    simp [sym]

/-- The test function obtained by deleting the letters of `Y` in turn. -/
noncomputable def topFun : List ℕ → (List ℕ → 𝔽) → (List ℕ → 𝔽)
  | [], φ => φ
  | y :: Y, φ => delFun y (topFun Y φ)

theorem sym_fold (c₀ : 𝔽) (L : ℕ) : ∀ (Y : List ℕ) (i : ℕ) (s : St 𝔽[X]),
    (∀ y ∈ Y, 0 < y) → Adm L i s →
      Adm L (i + Y.length)
        (Y.foldl (fun (s : St 𝔽[X]) (y : ℕ) => actSt (C c₀ : 𝔽[X]) X (y : ℤ) s) s) ∧
      ∀ φ : List ℕ → 𝔽,
        sym L (i + Y.length) φ
            (Y.foldl (fun (s : St 𝔽[X]) (y : ℕ) => actSt (C c₀ : 𝔽[X]) X (y : ℤ) s) s) =
          sym L i (topFun Y φ) s
  | [], i, s, _, hs => ⟨by simpa using hs, fun φ => by simp [topFun]⟩
  | y :: Y, i, s, hY, hs => by
    have hy : 0 < y := hY y (List.mem_cons_self ..)
    have hY' : ∀ z ∈ Y, 0 < z := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    have hadm := adm_step c₀ hs (show (0 : ℤ) < (y : ℤ) by exact_mod_cast hy)
    obtain ⟨h1, h2⟩ := sym_fold c₀ L Y (i + 1) _ hY' hadm
    have hlen : i + (y :: Y).length = i + 1 + Y.length := by simp; omega
    rw [List.foldl_cons, hlen]
    refine ⟨h1, fun φ => ?_⟩
    rw [h2 φ, sym_step c₀ hs hy]
    rfl

theorem natDegree_list_sum_le_of {l : List 𝔽[X]} {n : ℕ} (h : ∀ p ∈ l, p.natDegree ≤ n) :
    l.sum.natDegree ≤ n := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.sum_cons]
    exact natDegree_add_le_of_degree_le (h a (List.mem_cons_self ..))
      (ih fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem adm_init (Y' : List ℕ) : Adm (𝔽 := 𝔽) Y'.length 0 [(Y', 1)] := by
  intro t ht
  simp only [List.mem_singleton] at ht
  subst ht
  simp

/-- `deg_Δ ⟨Δ|L_Y L_{-Y'}|Δ⟩ ≤ min(|Y|, |Y'|)`. -/
theorem natDegree_gramWord_le (c₀ : 𝔽) (Y Y' : List ℕ) (hY : ∀ y ∈ Y, 0 < y) :
    (gramWord (C c₀ : 𝔽[X]) X Y Y').natDegree ≤ min Y.length Y'.length := by
  obtain ⟨hadm, -⟩ := sym_fold c₀ Y'.length Y 0 [(Y', 1)] hY (adm_init Y')
  unfold gramWord vac
  apply natDegree_list_sum_le_of
  intro p hp
  simp only [List.mem_map] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  have := hadm t ht
  split_ifs
  · simp only [zero_add] at this
    exact le_min this.1 (by omega)
  · simp

/-- The coefficient of `Δ^r` of `⟨Δ|L_Y L_{-Y'}|Δ⟩` for words of equal length `r`. -/
theorem coeff_gramWord_top (c₀ : 𝔽) (Y Y' : List ℕ) (hY : ∀ y ∈ Y, 0 < y)
    (hlen : Y.length = Y'.length) :
    (gramWord (C c₀ : 𝔽[X]) X Y Y').coeff Y.length = topFun Y (fun _ => (1 : 𝔽)) Y' := by
  obtain ⟨-, hsym⟩ := sym_fold c₀ Y'.length Y 0 [(Y', 1)] hY (adm_init Y')
  have h := hsym fun _ => (1 : 𝔽)
  rw [zero_add] at h
  have hinit : sym Y'.length 0 (topFun Y fun _ => (1 : 𝔽)) [(Y', (1 : 𝔽[X]))] =
      topFun Y (fun _ => (1 : 𝔽)) Y' := by
    simp [sym]
  rw [← hinit, ← h]
  unfold gramWord vac sym
  rw [coeff_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, mul_one]
  by_cases he : t.1.isEmpty
  · have : t.1.length = 0 := by simpa [List.isEmpty_iff] using he
    rw [if_pos he, if_pos (by omega)]
    rfl
  · have : t.1.length ≠ 0 := by simpa [List.isEmpty_iff] using he
    rw [if_neg he, if_neg (by omega)]
    simp

/-! ### The matching count -/

/-- The number of complete matchings of the letters of `Y` with letters of `w`, weighted by
`∏ 2 y_i`. -/
def topNat : List ℕ → List ℕ → ℕ
  | [], _ => 1
  | y :: Y, w => ((delOne y w).map fun u => 2 * y * topNat Y u).sum

theorem topFun_eq_topNat (Y : List ℕ) (w : List ℕ) :
    topFun Y (fun _ => (1 : 𝔽)) w = (topNat Y w : 𝔽) := by
  induction Y generalizing w with
  | nil => simp [topFun, topNat]
  | cons y Y ih =>
    simp only [topFun, delFun, topNat, Nat.cast_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u _
    simp [ih u]

theorem delOne_perm {k : ℕ} : ∀ {w u : List ℕ}, u ∈ delOne k w → List.Perm w (k :: u)
  | [], u, h => by simp [delOne] at h
  | y :: w, u, h => by
    simp only [delOne, List.mem_append, List.mem_map] at h
    rcases h with h | ⟨v, hv, rfl⟩
    · split_ifs at h with hy
      · simp only [List.mem_singleton] at h
        subst h; subst hy
        exact List.Perm.refl _
      · simp at h
    · exact ((delOne_perm hv).cons y).trans (List.Perm.swap k y v)

theorem topNat_ne_zero_perm : ∀ (Y w : List ℕ), topNat Y w ≠ 0 →
    ∃ rest : List ℕ, List.Perm w (Y ++ rest)
  | [], w, _ => ⟨w, by simp⟩
  | y :: Y, w, h => by
    simp only [topNat] at h
    have : ∃ u ∈ delOne y w, 2 * y * topNat Y u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply h
      apply List.sum_eq_zero
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      exact hcon u hu
    obtain ⟨u, hu, hne⟩ := this
    have hne' : topNat Y u ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
    obtain ⟨rest, hrest⟩ := topNat_ne_zero_perm Y u hne'
    exact ⟨rest, (delOne_perm hu).trans (hrest.cons y)⟩

theorem topNat_self_pos : ∀ (Y : List ℕ), (∀ y ∈ Y, 0 < y) → 0 < topNat Y Y
  | [], _ => by simp [topNat]
  | y :: Y, hY => by
    have hy : 0 < y := hY y (List.mem_cons_self ..)
    have ih := topNat_self_pos Y fun z hz => hY z (List.mem_cons_of_mem _ hz)
    simp only [topNat, delOne, if_true, List.singleton_append, List.map_cons, List.sum_cons]
    positivity

/-- The top coefficient vanishes unless `Y'` is a rearrangement of `Y`. -/
theorem topNat_eq_zero_of_not_perm {Y Y' : List ℕ} (hlen : Y.length = Y'.length)
    (h : ¬ List.Perm Y' Y) : topNat Y Y' = 0 := by
  by_contra hne
  obtain ⟨rest, hrest⟩ := topNat_ne_zero_perm Y Y' hne
  have hl := hrest.length_eq
  rw [List.length_append] at hl
  have : rest = [] := List.length_eq_zero_iff.1 (by omega)
  rw [this, List.append_nil] at hrest
  exact h hrest

end Virasoro
