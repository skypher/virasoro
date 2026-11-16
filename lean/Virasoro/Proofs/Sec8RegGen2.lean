import Virasoro.Proofs.Sec8RegGen
import Mathlib.Data.List.GetD

/-!
# Lemma 8.4: the system `B_m p = e`, regularity and specialization
-/

namespace Virasoro

open Verma Module

/-- The finite data at a level `m` that the argument uses: enumerations by `lexWords` and the
words occurring in `L_1`, `L_2` of the basis vectors. -/
structure LevelData (m : ℕ) : Prop where
  em : IsEnum m (lexWords m)
  e1 : IsEnum (m - 1) (lexWords (m - 1))
  e2 : IsEnum (m - 2) (lexWords (m - 2))
  t1 : ∀ Y ∈ lexWords m, ∀ t ∈ posActAff 40 1 Y, t.1 ∈ lexWords (m - 1)
  t2 : ∀ Y ∈ lexWords m, ∀ t ∈ posActAff 40 2 Y, t.1 ∈ lexWords (m - 2)
  rows : (lexWords m).length - 1 ≤ (lexWords (m - 1)).length + (lexWords (m - 2)).length
  pos : 0 < (lexWords m).length

theorem LevelData.lastIdx {m : ℕ} (hD : LevelData m) : (lexWords m).length - 1 < (lexWords m).length := by
  have := hD.pos
  omega

theorem word_eq_ones_iff {m : ℕ} (Y : Nat.Partition m) :
    Y.word = List.replicate m 1 ↔ Y = onesPartition m := by
  constructor
  · intro hY
    apply Nat.Partition.ext
    rw [← Verma.word_coe, ← Verma.word_coe, hY, word_onesPartition]
  · rintro rfl
    exact word_onesPartition m

section Generic

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R}

theorem sum_fin_enum {m : ℕ} (hE : IsEnum m (lexWords m)) {M : Type*} [AddCommMonoid M]
    (F : List ℕ → Nat.Partition m → M) :
    ∑ j : Fin (lexWords m).length, F ((lexWords m).getD j []) (hE.equiv.symm j) =
      ∑ Y, F Y.word Y := by
  rw [← Equiv.sum_comp hE.equiv]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [Equiv.symm_apply_apply, List.getD_eq_getElem _ _ (hE.equiv Y).2, hE.getElem_equiv]

/-- A normalized singular vector solves `B_m p = e_last`. -/
theorem Bmat_mulVec_singular {m : ℕ} (hD : LevelData m) (p : Nat.Partition m → R)
    (h1 : p (onesPartition m) = 1) (hL1 : L 1 (pbwCoord (c := c) (h := h) m p) = 0)
    (hL2 : L 2 (pbwCoord (c := c) (h := h) m p) = 0) :
    (Bmat m c h).mulVec (fun j => p (hD.em.equiv.symm j)) =
      Pi.single ⟨(lexWords m).length - 1, hD.lastIdx⟩ 1 := by
  have r1 := rows_of_L 1 hD.em hD.e1 hD.t1 p hL1
  have r2 := rows_of_L 2 hD.em hD.e2 hD.t2 p hL2
  have hrow : ∀ f ∈ Srows m c h, ∑ Y, f Y.word * p Y = 0 := by
    intro f hf
    rcases List.mem_append.1 hf with hf | hf
    · obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hf
      exact r1 Z hZ
    · obtain ⟨Z, hZ, rfl⟩ := List.mem_map.1 hf
      exact r2 Z hZ
  have hSlen : (Srows m c h).length = (lexWords (m - 1)).length + (lexWords (m - 2)).length := by
    simp [Srows]
  have htake : ((Srows m c h).take ((lexWords m).length - 1)).length = (lexWords m).length - 1 := by
    rw [List.length_take]
    have := hD.rows
    omega
  funext i
  simp only [Matrix.mulVec, dotProduct, Bmat, Matrix.of_apply]
  rw [sum_fin_enum hD.em (fun w Y => (Brows m c h).getD i 0 w * p Y)]
  by_cases hi : i.1 < (lexWords m).length - 1
  · have hg : (Brows m c h).getD i 0 = (Srows m c h)[i.1]'(by have := hD.rows; omega) := by
      unfold Brows
      rw [List.getD_append _ _ _ _ (by rw [htake]; exact hi),
        List.getD_eq_getElem _ _ (by rw [htake]; exact hi), List.getElem_take]
    have hne : i ≠ ⟨(lexWords m).length - 1, hD.lastIdx⟩ := by
      intro hieq
      rw [hieq] at hi
      exact lt_irrefl _ hi
    rw [hg, hrow _ (List.getElem_mem _), Pi.single_eq_of_ne hne]
  · have hi' : i.1 = (lexWords m).length - 1 := by have := i.2; omega
    have hg : (Brows m c h).getD i 0 = fun Y => if Y = List.replicate m 1 then 1 else 0 := by
      unfold Brows
      rw [List.getD_append_right _ _ _ _ (by omega), htake, hi', Nat.sub_self]
      rfl
    have hieq : i = ⟨(lexWords m).length - 1, hD.lastIdx⟩ := Fin.ext hi'
    rw [hg, hieq, Pi.single_eq_same]
    dsimp only
    rw [Finset.sum_eq_single (onesPartition m)]
    · rw [if_pos (word_onesPartition m), one_mul, h1]
    · intro Y _ hY
      rw [if_neg (fun hw => hY ((word_eq_ones_iff Y).1 hw)), zero_mul]
    · intro h0
      exact absurd (Finset.mem_univ _) h0

end Generic

/-! ### `L_1` and `L_2` generate the positive modes -/

theorem L_pos_zero_of_L12 {c h : ℂ} {v : Verma ℂ c h} (h1 : L 1 v = 0) (h2 : L 2 v = 0) :
    ∀ n : ℤ, 0 < n → L n v = 0 := by
  have key : ∀ k : ℕ, L ((k + 1 : ℕ) : ℤ) v = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k
        · simpa using h1
        · simpa using h2
      · have hprev := ih (k - 1) (by omega)
        have e := L_L (c := c) (h := h) ((k : ℕ) : ℤ) 1 v
        have ek : ((k - 1 + 1 : ℕ) : ℤ) = (k : ℤ) := by omega
        rw [ek] at hprev
        rw [h1, map_zero, hprev, map_zero, zero_add, if_neg (by omega), add_zero] at e
        have hne : (((k : ℤ) - 1 : ℤ) : ℂ) ≠ 0 := by
          have : ((k : ℤ) - 1) ≠ 0 := by omega
          exact_mod_cast this
        have := (smul_eq_zero.1 e.symm).resolve_left hne
        have ek1 : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
        rwa [ek1] at this
  intro n hn
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = ((k + 1 : ℕ) : ℤ) := ⟨(n - 1).toNat, by omega⟩
  rw [hk]
  exact key k

/-! ### Regularity at `b₀` -/

section Regular

variable {K : Type} [Field K] [CharZero K] [Algebra K ℂ]

theorem evToK_ratCast (q : ℚ) :
    EvToK b0 (algebraMap ℚ (RatFunc K) q) (algebraMap ℚ ℂ q) := by
  have e1 : algebraMap ℚ (RatFunc K) q = RatFunc.C (q : K) := by
    rw [eq_ratCast (algebraMap ℚ (RatFunc K)), map_ratCast]
  have e2 : algebraMap ℚ ℂ q = algebraMap K ℂ (q : K) := by
    rw [eq_ratCast (algebraMap ℚ ℂ), map_ratCast]
  rw [e1, e2]
  exact evToK_C (q : K)

theorem evToK_evalAff {c h : RatFunc K} {cv hv : ℂ} (hc : EvToK b0 c cv) (hh : EvToK b0 h hv)
    (x : Aff) : EvToK b0 (evalAff c h x) (evalAff cv hv x) := by
  unfold evalAff
  exact ((evToK_ratCast x.1).add ((evToK_ratCast x.2.1).mul hh)).add
    ((evToK_ratCast x.2.2).mul hc)

theorem EvToK.finsetSum {ι : Type*} (s : Finset ι) {x : ι → RatFunc K} {v : ι → ℂ}
    (h : ∀ i ∈ s, EvToK b0 (x i) (v i)) : EvToK b0 (∑ i ∈ s, x i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evToK_zero (K := K) (b := b0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem EvToK.uniq {x : RatFunc K} {v w : ℂ} (hv : EvToK b0 x v) (hw : EvToK b0 x w) : v = w :=
  hv.2.symm.trans hw.2

/-- Cramer's rule over the functions regular at `b₀`. -/
theorem regular_of_B {m : ℕ} (hD : LevelData m) {c h : RatFunc K} {cv hv : ℂ}
    (hc : EvToK b0 c cv) (hh : EvToK b0 h hv) (hdet : (Bmat m cv hv).det ≠ 0)
    (p : Nat.Partition m → RatFunc K) (h1 : p (onesPartition m) = 1)
    (hL1 : L 1 (pbwCoord (c := c) (h := h) m p) = 0)
    (hL2 : L 2 (pbwCoord (c := c) (h := h) m p) = 0) :
    ∃ pv : Nat.Partition m → ℂ, (∀ Y, EvToK b0 (p Y) (pv Y)) ∧
      (Bmat m cv hv).mulVec (fun j => pv (hD.em.equiv.symm j)) =
        Pi.single ⟨(lexWords m).length - 1, hD.lastIdx⟩ 1 := by
  classical
  set A := regSubK K b0 with hA
  set ev : A →+* ℂ := evRegK K b0
  set incl : A →+* RatFunc K := (regSubK K b0).val.toRingHom
  have hent : ∀ i j, EvToK b0 (Bmat m c h i j) (Bmat m cv hv i j) := by
    intro i j
    rw [Bmat_eq, Bmat_eq]
    exact evToK_evalAff hc hh _
  let BA : Matrix (Fin (lexWords m).length) (Fin (lexWords m).length) A :=
    Matrix.of fun i j => ⟨Bmat m c h i j, (hent i j).1⟩
  have hincl : BA.map incl = Bmat m c h := by ext i j; rfl
  have hev : BA.map ev = Bmat m cv hv := by
    ext i j
    exact (hent i j).2
  have hdetA : ev BA.det ≠ 0 := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hev]; exact hdet
  have hdetR : (incl BA.det) ≠ 0 := by
    intro h0
    apply hdetA
    have : (BA.det : RatFunc K) = 0 := h0
    have hm : EvToK b0 (BA.det : RatFunc K) (ev BA.det) := ⟨BA.det.2, rfl⟩
    rw [this] at hm
    exact hm.uniq (evToK_zero (K := K) (b := b0))
  have hinvmem : EvToK b0 ((BA.det : RatFunc K)⁻¹) (ev BA.det)⁻¹ :=
    EvToK.inv ⟨BA.det.2, rfl⟩ hdetA
  have hunit : IsUnit BA.det := by
    refine IsUnit.of_mul_eq_one ⟨_, hinvmem.1⟩ (Subtype.ext ?_)
    show (BA.det : RatFunc K) * (BA.det : RatFunc K)⁻¹ = 1
    exact mul_inv_cancel₀ hdetR
  have hunitR : IsUnit (Bmat m c h).det := by
    rw [← hincl, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hunit.map incl
  set e := Pi.single (M := fun _ : Fin (lexWords m).length => A)
    (⟨(lexWords m).length - 1, hD.lastIdx⟩ : Fin (lexWords m).length) 1 with he
  set q' := BA⁻¹.mulVec e
  have hq' : BA.mulVec q' = e := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  have hR1 : (Bmat m c h).mulVec (fun j => incl (q' j)) =
      Pi.single ⟨(lexWords m).length - 1, hD.lastIdx⟩ 1 := by
    funext j
    rw [← hincl]
    show (BA.map incl).mulVec (incl ∘ q') j = _
    rw [← RingHom.map_mulVec, hq']
    by_cases hj : j = ⟨(lexWords m).length - 1, hD.lastIdx⟩
    · subst hj; simp [e]
    · simp [e, Pi.single_eq_of_ne hj]
  have hR2 := Bmat_mulVec_singular hD p h1 hL1 hL2
  have hpq : (fun j => p (hD.em.equiv.symm j)) = fun j => incl (q' j) := by
    have := congrArg (fun v => (Bmat m c h)⁻¹.mulVec v) (hR2.trans hR1.symm)
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunitR] using this
  refine ⟨fun Y => ev (q' (hD.em.equiv Y)), fun Y => ?_, ?_⟩
  · have := congrFun hpq (hD.em.equiv Y)
    simp only [Equiv.symm_apply_apply] at this
    rw [this]
    exact ⟨(q' (hD.em.equiv Y)).2, rfl⟩
  · simp only [Equiv.apply_symm_apply]
    funext j
    rw [← hev]
    show (BA.map ev).mulVec (ev ∘ q') j = _
    rw [← RingHom.map_mulVec, hq']
    by_cases hj : j = ⟨(lexWords m).length - 1, hD.lastIdx⟩
    · subst hj; simp [e]
    · simp [e, Pi.single_eq_of_ne hj]

/-- The rows of `S_k` specialize. -/
theorem rows_specialize {m n : ℕ} (k : ℤ) {wsm wsk : List (List ℕ)} (hEm : IsEnum m wsm)
    (hEk : IsEnum n wsk) (hT : ∀ Y ∈ wsm, ∀ t ∈ posActAff 40 k Y, t.1 ∈ wsk)
    {c h : RatFunc K} {cv hv : ℂ} (hc : EvToK b0 c cv) (hh : EvToK b0 h hv)
    (p : Nat.Partition m → RatFunc K) (pv : Nat.Partition m → ℂ)
    (hp : ∀ Y, EvToK b0 (p Y) (pv Y)) (hL : L k (pbwCoord (c := c) (h := h) m p) = 0) :
    L k (pbwCoord (c := cv) (h := hv) m pv) = 0 := by
  refine L_of_rows k hEm hEk hT pv fun Z hZ => ?_
  have hR := rows_of_L k hEm hEk hT p hL Z hZ
  have hE : EvToK b0 (∑ Y : Nat.Partition m, Sfun k c h Z Y.word * p Y)
      (∑ Y : Nat.Partition m, Sfun k cv hv Z Y.word * pv Y) :=
    EvToK.finsetSum _ fun Y _ => (evToK_evalAff hc hh _).mul (hp Y)
  rw [hR] at hE
  exact hE.uniq (evToK_zero (K := K) (b := b0))

end Regular

/-- The normalized singular vector at a specialization is unique when `det B_m ≠ 0`. -/
theorem unique_of_B {m : ℕ} (hD : LevelData m) {cv hv : ℂ} (hdet : (Bmat m cv hv).det ≠ 0)
    (p p' : Nat.Partition m → ℂ) (h1 : p (onesPartition m) = 1)
    (h1' : p' (onesPartition m) = 1) (hs : IsSingular (pbwCoord (c := cv) (h := hv) m p) m)
    (hs' : IsSingular (pbwCoord (c := cv) (h := hv) m p') m) : p = p' := by
  have e1 := Bmat_mulVec_singular hD p h1 (hs.2.2 1 (by norm_num)) (hs.2.2 2 (by norm_num))
  have e2 := Bmat_mulVec_singular hD p' h1' (hs'.2.2 1 (by norm_num)) (hs'.2.2 2 (by norm_num))
  have hunit : IsUnit (Bmat m cv hv).det := isUnit_iff_ne_zero.2 hdet
  have := congrArg (fun v => (Bmat m cv hv)⁻¹.mulVec v) (e1.trans e2.symm)
  simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec] at this
  funext Y
  have := congrFun this (hD.em.equiv Y)
  simpa using this

end Virasoro
