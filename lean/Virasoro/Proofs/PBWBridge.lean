import Virasoro.Proofs.PBWState
import Virasoro.Proofs.Jet3
import Virasoro.Proofs.CoordTools
import Virasoro.Proofs.Vacuum
import Virasoro.Proofs.Shapovalov
import Virasoro.Proofs.Sec5Spin

/-!
# From engine computations to statements in the Verma module

Explicit computations are carried out over `ℚ` or `T3 ℚ` and transported along ring
homomorphisms.  This file collects the transport lemmas: levels and coordinates of mapped
states, singularity from vanishing engine output, and Shapovalov matrix–vector products as
vacuum expectation values.
-/

namespace Virasoro

open Verma

variable {A R : Type*} [CommRing A] [Algebra ℚ A] [CommRing R] [Algebra ℚ R]

theorem isLevelSt_mapSt (φ : A →+* R) {N : ℕ} {s : List (List ℕ × A)} (h : IsLevelSt N s) :
    IsLevelSt N (mapSt φ s) := by
  intro t ht
  simp only [mapSt, List.mem_map] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  exact h u hu

theorem coords_mapSt (φ : A →+* R) (N : ℕ) (s : List (List ℕ × A)) (Y : Nat.Partition N) :
    St.coords N (mapSt φ s) Y = φ (St.coords N s Y) := by
  unfold St.coords mapSt
  rw [List.filter_map, List.map_map, map_list_sum, List.map_map]
  rfl

theorem toVerma_perm {c h : R} {s s' : St R} (hp : s.Perm s') :
    St.toVerma (c := c) (h := h) s = St.toVerma s' :=
  (hp.map _).sum_eq

theorem word_onesPartition (N : ℕ) : (onesPartition N).word = List.replicate N 1 := by
  refine word_eq_of_parts _ _ (List.pairwise_replicate.2 (Or.inr le_rfl)) ?_
  simp only [onesPartition, Nat.Partition.ofSums]
  rw [Multiset.filter_eq_self.2 fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; norm_num]
  rfl

/-- The coefficient of `L_{-1}^N` of an explicit vector. -/
theorem coords_ones {N : ℕ} (s : St R) :
    St.coords N s (onesPartition N) =
      ((s.filter fun t => t.1 = List.replicate N 1).map Prod.snd).sum := by
  unfold St.coords
  rw [word_onesPartition]

/-- The engine applies `L_{y₁}`, then `L_{y₂}`, … . -/
theorem toVerma_posN_foldl [DecidableEq A] (φ : A →+* R) (f : ℕ) (c h : A) (Y : List ℕ) :
    ∀ s : List (List ℕ × A),
      St.toVerma (c := φ c) (h := φ h) (mapSt φ (posN f c h Y s))
        = Y.foldl (fun v (y : ℕ) => L (y : ℤ) v) (St.toVerma (mapSt φ s)) := by
  induction Y with
  | nil => intro s; rfl
  | cons y Y ih =>
    intro s
    have e : posN f c h (y :: Y) s = posN f c h Y (actN f c h (y : ℤ) s) := rfl
    rw [e, ih, toVerma_actN, List.foldl_cons]

theorem toVerma_posN_posOp [DecidableEq A] (φ : A →+* R) (f : ℕ) (c h : A) (Y : List ℕ)
    (s : List (List ℕ × A)) :
    St.toVerma (c := φ c) (h := φ h) (mapSt φ (posN f c h Y s))
      = VirEnv.posOp (φ c) Y • St.toVerma (mapSt φ s) := by
  rw [toVerma_posN_foldl, posOp_smul]

/-- An explicit vector over `ℚ` whose engine images under `L_1, …, L_N` vanish is singular. -/
theorem isSingular_ofQ {N : ℕ} (f : ℕ) (cq hq : ℚ) {c h : R} (hc : algebraMap ℚ R cq = c)
    (hh : algebraMap ℚ R hq = h) (s : List (List ℕ × ℚ)) (hs : IsLevelSt N s)
    (hne : St.coords N s ≠ 0) [Nontrivial R]
    (hL : ∀ n : ℕ, 1 ≤ n → n ≤ N → actN f cq hq (n : ℤ) s = []) :
    Verma.IsSingular (St.toVerma (c := c) (h := h) (mapSt (algebraMap ℚ R) s)) N := by
  subst hc hh
  refine isSingular_of_actSt _ (isLevelSt_mapSt _ hs) ?_ fun n h1 h2 => ?_
  · intro h0
    apply hne
    funext Y
    have := congrFun h0 Y
    rw [coords_mapSt] at this
    exact (algebraMap ℚ R).injective (by simpa using this)
  · rw [St.toVerma_actSt, ← toVerma_actN (algebraMap ℚ R) f cq hq (n : ℤ) s, hL n h1 h2]
    rfl

/-- Shapovalov matrix–vector products are vacuum expectation values. -/
theorem gram_mulVec_coords (c h : R) {N : ℕ} (s : St R) (hs : IsLevelSt N s)
    (Y : Nat.Partition N) :
    (gram c h N).mulVec (St.coords N s) Y
      = vacuum c h (VirEnv.posOp c Y.word • St.toVerma (c := c) (h := h) s) := by
  simp only [Matrix.mulVec, dotProduct, gram, Matrix.of_apply]
  rw [Finset.sum_congr rfl (fun i _ => mul_comm _ _), sum_coords_mul s hs fun w => gramWord c h Y.word w]
  induction s with
  | nil => simp [St.toVerma_nil]
  | cons t s ih =>
    have hs' : IsLevelSt N s := fun u hu => hs u (List.mem_cons_of_mem _ hu)
    have ht : PosWord t.1 := (hs t List.mem_cons_self).1
    rw [List.map_cons, List.sum_cons, ih hs', St.toVerma_cons, smul_add, map_add]
    congr 1
    rw [← smul_comm t.2 (VirEnv.posOp c Y.word) (neg t.1), map_smul,
      vacuum_gramWord isVacuum_vacuum Y.word t.1 ht, smul_eq_mul]


/-! ### Enumerating weakly decreasing words -/

/-- The weakly decreasing words of positive integers of sum `n` with parts at most `k`
(`f` is fuel). -/
def decWordsAux : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => []
  | _ + 1, 0, _ => [[]]
  | f + 1, n + 1, k =>
      (List.range (min k (n + 1))).flatMap fun i =>
        (decWordsAux f (n + 1 - (i + 1)) (i + 1)).map fun w => (i + 1) :: w

/-- The weakly decreasing words of positive integers of sum `n`. -/
def decWords (n : ℕ) : List (List ℕ) := decWordsAux (n + 1) n n

theorem mem_decWordsAux : ∀ (f n k : ℕ) (w : List ℕ), n < f → PosWord w → w.sum = n →
    w.Pairwise (· ≥ ·) → (∀ y ∈ w, y ≤ k) → w ∈ decWordsAux f n k
  | 0, n, _, _, hf, _, _, _, _ => absurd hf (Nat.not_lt_zero n)
  | f + 1, 0, k, w, _, hw, hs, _, _ => by
    have : w = [] := by
      cases w with
      | nil => rfl
      | cons y w =>
        have := hw y List.mem_cons_self
        simp only [List.sum_cons] at hs
        omega
    subst this
    simp [decWordsAux]
  | f + 1, n + 1, k, w, hf, hw, hs, hp, hk => by
    cases w with
    | nil => simp at hs
    | cons j w =>
      have hj : 0 < j := hw j List.mem_cons_self
      have hjk : j ≤ k := hk j List.mem_cons_self
      simp only [List.sum_cons] at hs
      rw [List.pairwise_cons] at hp
      simp only [decWordsAux, List.mem_flatMap, List.mem_range, List.mem_map]
      refine ⟨j - 1, by omega, w, ?_, by congr 1; omega⟩
      have e : j - 1 + 1 = j := by omega
      rw [e]
      exact mem_decWordsAux f (n + 1 - j) j w (by omega)
        (fun y hy => hw y (List.mem_cons_of_mem _ hy)) (by omega) hp.2
        (fun y hy => hp.1 y hy)

theorem word_mem_decWords {N : ℕ} (Y : Nat.Partition N) : Y.word ∈ decWords N := by
  have hmem : ∀ y ∈ Y.word, y ∈ Y.parts := by
    intro y hy
    rw [← Verma.word_coe Y]
    exact Multiset.mem_coe.2 hy
  refine mem_decWordsAux (N + 1) N N Y.word (by omega) (fun y hy => Y.parts_pos (hmem y hy))
    (word_sum' Y) (word_pairwise Y) fun y hy => ?_
  have := Multiset.le_sum_of_mem (hmem y hy)
  rwa [Y.parts_sum] at this


theorem isEnum_decWords (N : ℕ) (hnd : (decWords N).Nodup)
    (hp : ∀ w ∈ decWords N, PosWord w ∧ w.sum = N ∧ w.Pairwise (· ≥ ·)) :
    IsEnum N (decWords N) where
  nodup := hnd
  pos := fun w hw => (hp w hw).1
  sum := fun w hw => (hp w hw).2.1
  sorted := fun w hw => (hp w hw).2.2
  complete := fun w hw hs hpw => mem_decWordsAux (N + 1) N N w (by omega) hw hs hpw
    fun y hy => by have := List.le_sum_of_mem hy; omega

theorem card_partition_of_isEnum {N : ℕ} {ws : List (List ℕ)} (h : IsEnum N ws) :
    Fintype.card (Nat.Partition N) = ws.length := by
  rw [Fintype.card_congr h.equiv, Fintype.card_fin]

end Virasoro
