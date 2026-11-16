import Virasoro.Proofs.Sec8Smith7
import Virasoro.Proofs.RegEvalK
import Virasoro.Statements.Sec8

/-!
# Lemma 8.4: the generic theory

For a level `m`, `L_1` and `L_2` act on `M(c,h)_m` by matrices `S_1(c,h)`, `S_2(c,h)` whose
entries are affine in `(h, c)` (`Sfun`, from the engine's `posActAff`).  `Bmat m c h` is the
matrix `B_m(c,h)` of the paper: the first `p(m)-1` rows of the stacked `S_1, S_2`, then the
coordinate row of `L_{-1}^m`.  A normalized singular vector `p` solves `B_m p = e_last`
(`Bmat_mulVec_singular`); if `det B_m ≠ 0` after evaluation at `b₀`, Cramer's rule over the
functions regular at `b₀` shows that the coordinates of `p` are regular there
(`regular_of_B`), and the specialized vector is singular (`specialized_singular`).
-/

namespace Virasoro

open Verma Module

/-- The affine coefficient of the word `Z` in `L_k L_{-Y}|h⟩`. -/
def affCoef (k : ℤ) (Z Y : List ℕ) : Aff :=
  (((posActAff 40 k Y).filter fun t => t.1 = Z).map Prod.snd).sum

section Generic

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The coefficient `S_k(c,h)_{Z,Y}`. -/
def Sfun (k : ℤ) (c h : R) (Z Y : List ℕ) : R := evalAff c h (affCoef k Z Y)

theorem evalAff_add (c h : R) (x y : Aff) :
    evalAff c h (x + y) = evalAff c h x + evalAff c h y := by
  simp only [evalAff, Prod.fst_add, Prod.snd_add, map_add]
  ring

theorem evalAff_zero (c h : R) : evalAff c h 0 = 0 := by simp [evalAff]

theorem evalAff_one (c h : R) : evalAff c h ((1 : ℚ), (0 : ℚ), (0 : ℚ)) = 1 := by simp [evalAff]

theorem sum_ite_mem {M : Type*} [AddCommMonoid M] {Ws : List (List ℕ)} (hnd : Ws.Nodup)
    {a : List ℕ} (ha : a ∈ Ws) (g : List ℕ → M) :
    (Ws.map fun Z => if a = Z then g Z else 0).sum = g a := by
  induction Ws with
  | nil => simp at ha
  | cons W Ws ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.sum_cons]
    by_cases haW : a = W
    · subst haW
      rw [if_pos rfl]
      have : (Ws.map fun Z => if a = Z then g Z else 0).sum = 0 := by
        refine List.sum_eq_zero fun x hx => ?_
        rw [List.mem_map] at hx
        obtain ⟨Z, hZ, rfl⟩ := hx
        rw [if_neg]
        rintro rfl
        exact hnd.1 hZ
      rw [this, add_zero]
    · rw [if_neg haW, zero_add]
      exact ih hnd.2 (by simpa [haW] using ha)

variable {c h : R}

/-- A combination of words from `Ws` in coordinates. -/
theorem toVerma_ofAff_eq_sum (l : List (List ℕ × Aff)) {Ws : List (List ℕ)} (hnd : Ws.Nodup)
    (hW : ∀ t ∈ l, t.1 ∈ Ws) :
    St.toVerma (c := c) (h := h) (ofAff c h l) =
      (Ws.map fun Z => evalAff c h (((l.filter fun t => t.1 = Z).map Prod.snd).sum) •
        neg (c := c) (h := h) Z).sum := by
  induction l with
  | nil => simp [ofAff, St.toVerma_nil, evalAff_zero]
  | cons t l ih =>
    have ih' := ih fun u hu => hW u (List.mem_cons_of_mem _ hu)
    have ht := hW t List.mem_cons_self
    have e1 : St.toVerma (c := c) (h := h) (ofAff c h (t :: l))
        = evalAff c h t.2 • neg t.1 + St.toVerma (ofAff c h l) := by
      simp only [ofAff, List.map_cons, St.toVerma_cons]
    have e2 : (Ws.map fun Z => evalAff c h ((((t :: l).filter fun u => u.1 = Z).map
          Prod.snd).sum) • neg (c := c) (h := h) Z)
        = Ws.map fun Z => (if t.1 = Z then evalAff c h t.2 • neg Z else 0) +
          evalAff c h (((l.filter fun u => u.1 = Z).map Prod.snd).sum) • neg Z := by
      refine List.map_congr_left fun Z _ => ?_
      by_cases hZ : t.1 = Z
      · simp [List.filter_cons, hZ, evalAff_add, add_smul]
      · simp [List.filter_cons, hZ]
    rw [e1, ih', e2, List.sum_map_add, sum_ite_mem hnd ht fun Z => evalAff c h t.2 • neg Z]

/-- `L_k L_{-Y}|h⟩ = ∑_Z S_k(c,h)_{Z,Y} L_{-Z}|h⟩`. -/
theorem L_neg_expand (k : ℤ) (Y : List ℕ) {Ws : List (List ℕ)} (hnd : Ws.Nodup)
    (hW : ∀ t ∈ posActAff 40 k Y, t.1 ∈ Ws) :
    L k (neg (c := c) (h := h) Y) = (Ws.map fun Z => Sfun k c h Z Y • neg Z).sum := by
  rw [← posActAff_spec 40 Y k, toVerma_ofAff_eq_sum _ hnd hW]
  rfl

theorem listSum_eq_finSum {M : Type*} [AddCommMonoid M] (f : List ℕ → M) :
    ∀ ws : List (List ℕ), (ws.map f).sum = ∑ i : Fin ws.length, f ws[i]
  | [] => by simp
  | W :: ws => by
    rw [List.map_cons, List.sum_cons, listSum_eq_finSum f ws]
    show _ = ∑ i : Fin (ws.length + 1), f (W :: ws)[i]
    rw [Fin.sum_univ_succ]
    rfl

theorem getD_map' {α β : Type*} (g : α → β) (d : α) :
    ∀ (l : List α) (i : ℕ), (l.map g).getD i (g d) = g (l.getD i d)
  | [], i => by simp
  | a :: l, 0 => by simp
  | a :: l, i + 1 => by simp [getD_map' g d l i]

theorem listSum_eq_pbwCoord {n : ℕ} {ws : List (List ℕ)} (hE : IsEnum n ws) (a : List ℕ → R) :
    (ws.map fun Z => a Z • neg (c := c) (h := h) Z).sum = pbwCoord n (fun Y => a Y.word) := by
  rw [pbwCoord_apply, ← Equiv.sum_comp hE.equiv.symm]
  simp only [IsEnum.word_symm]
  exact listSum_eq_finSum (fun Z => a Z • neg (c := c) (h := h) Z) ws

theorem coeffs_zero {n : ℕ} {ws : List (List ℕ)} (hE : IsEnum n ws) (a : List ℕ → R)
    (h0 : (ws.map fun Z => a Z • neg (c := c) (h := h) Z).sum = 0) : ∀ Z ∈ ws, a Z = 0 := by
  rw [listSum_eq_pbwCoord hE] at h0
  have hv := pbwCoord_injective n (h0.trans (map_zero _).symm)
  intro Z hZ
  have := congrFun hv (partOf Z (hE.pos Z hZ) (hE.sum Z hZ))
  rwa [partOf_word (hE.pos Z hZ) (hE.sum Z hZ) (hE.sorted Z hZ)] at this

theorem sum_smul_listSum {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module R M]
    (ws : List (List ℕ)) (p : ι → R) (S : List ℕ → ι → R) (v : List ℕ → M) :
    ∑ i, p i • (ws.map fun Z => S Z i • v Z).sum =
      (ws.map fun Z => (∑ i, S Z i * p i) • v Z).sum := by
  induction ws with
  | nil => simp
  | cons W ws ih =>
    simp only [List.map_cons, List.sum_cons, smul_add, Finset.sum_add_distrib, ih]
    congr 1
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, mul_comm]

/-- The rows of `S_k` annihilate the coordinates of a vector killed by `L_k`. -/
theorem rows_of_L {m n : ℕ} (k : ℤ) {wsm wsk : List (List ℕ)} (hEm : IsEnum m wsm)
    (hEk : IsEnum n wsk) (hT : ∀ Y ∈ wsm, ∀ t ∈ posActAff 40 k Y, t.1 ∈ wsk)
    (p : Nat.Partition m → R) (hL : L k (pbwCoord (c := c) (h := h) m p) = 0) :
    ∀ Z ∈ wsk, ∑ Y : Nat.Partition m, Sfun k c h Z Y.word * p Y = 0 := by
  have hexp : L k (pbwCoord (c := c) (h := h) m p) =
      (wsk.map fun Z => (∑ Y : Nat.Partition m, Sfun k c h Z Y.word * p Y) • neg Z).sum := by
    rw [pbwCoord_apply, map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl fun Y _ => by
      rw [L_neg_expand k Y.word hEk.nodup (hT _ (hEm.word_mem Y))]]
    exact sum_smul_listSum wsk p (fun Z Y => Sfun k c h Z Y.word) neg
  exact coeffs_zero hEk _ (hexp ▸ hL)

/-- The vector with the rows `∑_Y S_k Z Y p_Y = 0` is killed by `L_k`. -/
theorem L_of_rows {m n : ℕ} (k : ℤ) {wsm wsk : List (List ℕ)} (hEm : IsEnum m wsm)
    (hEk : IsEnum n wsk) (hT : ∀ Y ∈ wsm, ∀ t ∈ posActAff 40 k Y, t.1 ∈ wsk)
    (p : Nat.Partition m → R)
    (hrows : ∀ Z ∈ wsk, ∑ Y : Nat.Partition m, Sfun k c h Z Y.word * p Y = 0) :
    L k (pbwCoord (c := c) (h := h) m p) = 0 := by
  rw [pbwCoord_apply, map_sum]
  simp only [map_smul]
  rw [Finset.sum_congr rfl fun Y _ => by
    rw [L_neg_expand k Y.word hEk.nodup (hT _ (hEm.word_mem Y))],
    sum_smul_listSum wsk p (fun Z Y => Sfun k c h Z Y.word) neg]
  refine List.sum_eq_zero fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨Z, hZ, rfl⟩ := hx
  rw [hrows Z hZ, zero_smul]

/-! ### The matrix `B_m` -/

/-- The rows `S_1`, then `S_2`. -/
def Srows (m : ℕ) (c h : R) : List (List ℕ → R) :=
  ((lexWords (m - 1)).map fun Z => Sfun 1 c h Z) ++ ((lexWords (m - 2)).map fun Z => Sfun 2 c h Z)

/-- The rows of `B_m`. -/
def Brows (m : ℕ) (c h : R) : List (List ℕ → R) :=
  (Srows m c h).take ((lexWords m).length - 1) ++
    [fun Y => if Y = List.replicate m 1 then 1 else 0]

/-- The matrix `B_m(c,h)`. -/
def Bmat (m : ℕ) (c h : R) : Matrix (Fin (lexWords m).length) (Fin (lexWords m).length) R :=
  Matrix.of fun i j => ((Brows m c h).getD i 0) ((lexWords m).getD j [])

/-- The affine rows of `B_m`. -/
def BrowsAff (m : ℕ) : List (List ℕ → Aff) :=
  (((lexWords (m - 1)).map fun Z => affCoef 1 Z) ++ ((lexWords (m - 2)).map fun Z => affCoef 2 Z)).take
    ((lexWords m).length - 1) ++
    [fun Y => if Y = List.replicate m 1 then ((1 : ℚ), (0 : ℚ), (0 : ℚ)) else 0]

theorem Brows_eq (m : ℕ) (c h : R) :
    Brows m c h = (BrowsAff m).map fun f Y => evalAff c h (f Y) := by
  unfold Brows BrowsAff Srows
  rw [List.map_append, List.map_take, List.map_append, List.map_map, List.map_map,
    List.map_cons, List.map_nil]
  congr 2
  funext Y
  dsimp only
  split_ifs
  · exact (evalAff_one c h).symm
  · exact (evalAff_zero c h).symm

theorem Bmat_eq (m : ℕ) (c h : R) :
    Bmat m c h = Matrix.of fun (i j : Fin (lexWords m).length) =>
      evalAff c h (((BrowsAff m).getD i 0) ((lexWords m).getD j [])) := by
  ext i j
  simp only [Bmat, Matrix.of_apply, Brows_eq]
  have e : (0 : List ℕ → R) = fun Y => evalAff c h ((0 : List ℕ → Aff) Y) := by
    funext Y
    exact (evalAff_zero c h).symm
  rw [e, getD_map']

end Generic

end Virasoro
