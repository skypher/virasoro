import Virasoro.Proofs.Sec7Cut
import Virasoro.Proofs.Sec7Remainder

/-!
# Lemma 7.12 (chain expansion of the moments)

The proof follows the paper.  For a label `g` put `ν = w_g + ℓ_g`, so that `z_g = ν + δ_g`.  The
recursion of `S_{g,M}` splits into the labels `g'` with `w_{g'} = ν`, where
`z_g - h_{g'} = δ_g - δ_{g'}` (7.5), and the others, whose sum is
`Reg^{(M)}_ν(b, ν + δ_g) = ∑_j φ^{(M)}_{ν,j} δ_g^j/j!` (Taylor expansion; `SG_split`, `reg_trunc`).
Substituting repeatedly (`SG_expansion`) and collecting by the end point (`comb`, re-indexing by
the first label) gives (7.7).  The series over `j` is handled through its truncations: the error
of the truncation at `j < J` has `t`-adic order at least `J + c` with `c` independent of `J`.
-/

namespace Virasoro

open scoped LaurentSeries

section General

variable {K : Type} [Field K] [CharZero K] (bs d : K)

/-- `∑_{j<J} δ^j/j! · φ^{(M)}_{ν,j}`. -/
noncomputable def phiSum (M : ℕ) (ν : K) (y : K⸨X⸩) (J : ℕ) : K⸨X⸩ :=
  ∑ j ∈ Finset.range J, y ^ j / (j.factorial : K⸨X⸩) * phiRem bs d M ν j

/-- The chain expansion of `S_{g,M}`, cut at `j < J`: with `ν = w_g + ℓ_g`,
`∑_{j<J} φ^{(M)}_{ν,j} δ_g^j/j!` plus the chains from `ν` (entered from `g`) of level `M`, plus
the chains of level `n < M` followed by `φ^{(M-n)}_{ν+n,j}`. -/
noncomputable def sExp (M : ℕ) (g : Label) (J : ℕ) : K⸨X⸩ :=
  phiSum bs d M (kacHL g bs + (g.lvl : K)) (delG bs g) J +
    chainTail bs d 0 M (kacHL g bs + (g.lvl : K)) (delG bs g) +
    ∑ n ∈ Finset.Ioo 0 M, ∑ j ∈ Finset.range J,
      chainTail bs d j n (kacHL g bs + (g.lvl : K)) (delG bs g) *
        phiRem bs d (M - n) (kacHL g bs + (g.lvl : K) + (n : K)) j

/-- Re-indexing a sum over cut points by the first label of the chain. -/
theorem gen_reindex (p A : Label → K⸨X⸩) (T : Label → ℕ → K⸨X⸩) (W : ℕ → K⸨X⸩) (D : ℕ)
    (ν : K) :
    ∑ n ∈ Finset.Ioo 0 D,
        (∑ g ∈ labelsAt bs n ν, p g * (if g.lvl = n then A g else T g (n - g.lvl))) * W n =
      ∑ g ∈ labelsAt bs D ν,
        (if g.lvl < D then p g * (A g * W g.lvl +
          ∑ n' ∈ Finset.Ioo 0 (D - g.lvl), T g n' * W (g.lvl + n')) else 0) := by
  classical
  have hL : ∀ n ∈ Finset.Ioo 0 D,
      labelsAt bs n ν = (labelsAt bs D ν).filter (fun g => g.lvl ≤ n) := by
    intro n hn
    ext g
    simp only [mem_labelsAt, Finset.mem_filter]
    have hnD : n ≤ D := (Finset.mem_Ioo.1 hn).2.le
    constructor
    · rintro ⟨hg, hw⟩
      refine ⟨⟨?_, hw⟩, lvl_le_of_mem_labels hg⟩
      simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg ⊢
      exact ⟨⟨⟨hg.1.1.1, le_trans hg.1.1.2 hnD⟩, ⟨hg.1.2.1, le_trans hg.1.2.2 hnD⟩⟩,
        le_trans hg.2 hnD⟩
    · rintro ⟨⟨hg, hw⟩, hle⟩
      refine ⟨?_, hw⟩
      simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg ⊢
      have h1 := Nat.le_mul_of_pos_right g.1 hg.1.2.1
      have h2 := Nat.le_mul_of_pos_left g.2 hg.1.1.1
      exact ⟨⟨⟨hg.1.1.1, le_trans h1 hle⟩, ⟨hg.1.2.1, le_trans h2 hle⟩⟩, hle⟩
  rw [Finset.sum_congr rfl fun n hn => by rw [hL n hn]]
  simp_rw [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hpos := lvl_pos_of_mem_labels ((mem_labelsAt bs).1 hg).1
  by_cases hlt : g.lvl < D
  · rw [if_pos hlt]
    have hsplit : ∀ f : ℕ → K⸨X⸩, (∑ n ∈ Finset.Ioo 0 D, if g.lvl ≤ n then f n else 0) =
        f g.lvl + ∑ n' ∈ Finset.Ioo 0 (D - g.lvl), f (g.lvl + n') := by
      intro f
      have hset : (Finset.Ioo 0 D).filter (fun n => g.lvl ≤ n) =
          insert g.lvl ((Finset.Ioo 0 (D - g.lvl)).map (addLeftEmbedding g.lvl)) := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_insert, Finset.mem_map,
          addLeftEmbedding_apply]
        constructor
        · rintro ⟨⟨h0, hD⟩, hle⟩
          rcases Nat.eq_or_lt_of_le hle with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨n - g.lvl, ⟨by omega, by omega⟩, by omega⟩
        · rintro (h | ⟨n', ⟨h1, h2⟩, rfl⟩)
          · subst h; exact ⟨⟨hpos, hlt⟩, le_rfl⟩
          · exact ⟨⟨by omega, by omega⟩, by omega⟩
      rw [← Finset.sum_filter, hset, Finset.sum_insert, Finset.sum_map]
      · rfl
      · simp only [Finset.mem_map, Finset.mem_Ioo, addLeftEmbedding_apply, not_exists, not_and]
        intro n' h1 h3
        omega
    simp_rw [ite_mul, zero_mul]
    rw [hsplit (fun n => p g * (if g.lvl = n then A g else T g (n - g.lvl)) * W n)]
    rw [if_pos rfl, mul_add, Finset.mul_sum]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun n' hn' => ?_
      have hn'0 : 0 < n' := (Finset.mem_Ioo.1 hn').1
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
      ring
  · rw [if_neg hlt]
    refine Finset.sum_eq_zero fun n hn => ?_
    have := (Finset.mem_Ioo.1 hn).2
    rw [if_neg (by omega), zero_mul]

/-- Collecting the chain expansions of the `S_{g',D-ℓ_{g'}}` by end point. -/
theorem comb (p : Label → K⸨X⸩) (D : ℕ) (ν : K) (J : ℕ) :
    ∑ g ∈ labelsAt bs D ν, p g * (if g.lvl = D then 1 else sExp bs d (D - g.lvl) g J) =
      ∑ g ∈ labelsAt bs D ν, p g *
          (if g.lvl = D then delG bs g ^ 0 / ((0 : ℕ).factorial : K⸨X⸩)
            else chainTail bs d 0 (D - g.lvl) (ν + (g.lvl : K)) (delG bs g)) +
        ∑ n ∈ Finset.Ioo 0 D, ∑ j ∈ Finset.range J,
          (∑ g ∈ labelsAt bs n ν, p g *
            (if g.lvl = n then delG bs g ^ j / (j.factorial : K⸨X⸩)
              else chainTail bs d j (n - g.lvl) (ν + (g.lvl : K)) (delG bs g))) *
            phiRem bs d (D - n) (ν + (n : K)) j := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j _ => gen_reindex bs p (fun g => delG bs g ^ j / (j.factorial : K⸨X⸩))
    (fun g n' => chainTail bs d j n' (ν + (g.lvl : K)) (delG bs g))
    (fun n => phiRem bs d (D - n) (ν + (n : K)) j) D ν]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g hg => ?_
  obtain ⟨hgl, hgw⟩ := (mem_labelsAt bs).1 hg
  have hle := lvl_le_of_mem_labels hgl
  by_cases hD : g.lvl = D
  · rw [if_pos hD, if_pos hD]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    rw [Finset.sum_eq_zero fun j _ => by rw [if_neg (by omega)], add_zero]
  · have hlt : g.lvl < D := lt_of_le_of_ne hle hD
    rw [if_neg hD, if_neg hD]
    simp only [if_pos hlt]
    have hR : ∑ j ∈ Finset.range J, p g * (delG bs g ^ j / (j.factorial : K⸨X⸩) *
          phiRem bs d (D - g.lvl) (ν + (g.lvl : K)) j +
          ∑ n' ∈ Finset.Ioo 0 (D - g.lvl), chainTail bs d j n' (ν + (g.lvl : K)) (delG bs g) *
            phiRem bs d (D - (g.lvl + n')) (ν + ((g.lvl + n' : ℕ) : K)) j) =
        p g * (phiSum bs d (D - g.lvl) (ν + (g.lvl : K)) (delG bs g) J +
          ∑ n' ∈ Finset.Ioo 0 (D - g.lvl), ∑ j ∈ Finset.range J,
            chainTail bs d j n' (ν + (g.lvl : K)) (delG bs g) *
              phiRem bs d (D - g.lvl - n') (ν + (g.lvl : K) + (n' : K)) j) := by
      unfold phiSum
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm (s := Finset.range J)]
      refine congrArg (p g * ·) (congrArg (HAdd.hAdd _)
        (Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun j _ => ?_))
      rw [Nat.cast_add, add_assoc, Nat.sub_sub]
    rw [hR]
    unfold sExp
    rw [hgw]
    generalize phiSum bs d (D - g.lvl) (ν + (g.lvl : K)) (delG bs g) J = A
    generalize chainTail bs d 0 (D - g.lvl) (ν + (g.lvl : K)) (delG bs g) = B
    generalize (∑ n ∈ Finset.Ioo 0 (D - g.lvl), ∑ j ∈ Finset.range J,
      chainTail bs d j n (ν + (g.lvl : K)) (delG bs g) *
        phiRem bs d (D - g.lvl - n) (ν + (g.lvl : K) + (n : K)) j) = C
    generalize p g = P
    ring

open Classical in
/-- Step A: the recursion of `S_{g,M}` split at the weight `ν = w_g + ℓ_g`. -/
theorem SG_split (M : ℕ) (hM : 1 ≤ M) (g : Label) :
    SG bs d M g =
      ∑ g' ∈ labelsAt bs M (kacHL g bs + (g.lvl : K)),
          RG bs d g' / (delG bs g - delG bs g') * SG bs d (M - g'.lvl) g' +
        ∑ g' ∈ (labels M).filter (fun g' => ¬ kacHL g' bs = kacHL g bs + (g.lvl : K)),
          BG bs d M g' / (zG bs g - hG bs g') := by
  classical
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rw [SG_succ, Finset.sum_attach (labels (M' + 1))
    (fun g' => RG bs d g' / (zG bs g - hG bs g') * SG bs d (M' + 1 - g'.lvl) g'),
    ← Finset.sum_filter_add_sum_filter_not (labels (M' + 1))
      (fun g' => kacHL g' bs = kacHL g bs + (g.lvl : K))]
  have hfil : (labels (M' + 1)).filter (fun g' => kacHL g' bs = kacHL g bs + (g.lvl : K)) =
      labelsAt bs (M' + 1) (kacHL g bs + (g.lvl : K)) := by
    ext g'
    rw [Finset.mem_filter, mem_labelsAt]
  rw [hfil]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl fun g' hg' => ?_
    have hw := ((mem_labelsAt bs).1 hg').2
    have hz : zG bs g - hG bs g' = delG bs g - delG bs g' := by
      unfold zG delG deltaG
      rw [hw, map_add, map_natCast]
      ring
    rw [hz]
  · refine Finset.sum_congr rfl fun g' _ => ?_
    rw [BG]
    ring

/-- A geometric sum with remainder. -/
theorem geom_trunc {U y : K⸨X⸩} (hU : U ≠ 0) (hUy : U + y ≠ 0) (J : ℕ) :
    1 / (U + y) - ∑ j ∈ Finset.range J, (-y) ^ j / U ^ (j + 1) = (-y) ^ J / (U ^ J * (U + y)) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← sub_sub, ih]
    field_simp
    ring

open Classical in
/-- Step B: the Taylor expansion of `Reg^{(M)}_ν(b, ν + y)`, cut at `j < J`. -/
theorem reg_trunc (hbs : bs ≠ 0) (M : ℕ) (ν : K) {y : K⸨X⸩} (hy : OrdGE y 1) (J : ℕ) :
    OrdGE (∑ g' ∈ (labels M).filter (fun g' => ¬ kacHL g' bs = ν),
        BG bs d M g' / (HahnSeries.C ν + y - hG bs g') - phiSum bs d M ν y J)
      ((J : ℤ) - (((labels M).sup fun g => vhat bs d M g : ℕ) : ℤ)) := by
  classical
  have hfil : (labels M).filter (fun g' => ¬ kacHL g' bs = ν) =
      (labels M).filter (fun g' => kacHL g' bs ≠ ν) := by
    ext g'; simp
  unfold phiSum phiRem
  rw [hfil]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine OrdGE.sum fun g' hg' => ?_
  obtain ⟨hgl, hgw⟩ := Finset.mem_filter.1 hg'
  set U : K⸨X⸩ := HahnSeries.C ν - hG bs g' with hU
  have hregU : RegVal U (ν - kacHL g' bs) := (regVal_C ν).sub (regVal_hG hbs g')
  have hregy : RegVal y 0 := ⟨hy.mono (by norm_num), hy.coeff_eq_zero (by norm_num)⟩
  have hregUy : RegVal (U + y) (ν - kacHL g' bs) := by simpa using hregU.add hregy
  have hu0 : ν - kacHL g' bs ≠ 0 := sub_ne_zero.2 (Ne.symm hgw)
  have hne : ∀ {x : K⸨X⸩} {v : K}, RegVal x v → v ≠ 0 → x ≠ 0 := by
    intro x v hx hv h
    have := hx.2
    rw [h, HahnSeries.coeff_zero] at this
    exact hv this.symm
  have hU0 : U ≠ 0 := hne hregU hu0
  have hUy0 : U + y ≠ 0 := hne hregUy hu0
  have hden : HahnSeries.C ν + y - hG bs g' = U + y := by rw [hU]; ring
  have hterm : ∀ j ∈ Finset.range J,
      y ^ j / (j.factorial : K⸨X⸩) *
          (BG bs d M g' * ((-1 : K⸨X⸩) ^ j * (j.factorial : K⸨X⸩)) /
            (HahnSeries.C ν - hG bs g') ^ (j + 1)) =
        BG bs d M g' * ((-y) ^ j / U ^ (j + 1)) := by
    intro j _
    have hj : (j.factorial : K⸨X⸩) ≠ 0 := natCast_laurent_ne_zero (Nat.factorial_ne_zero j)
    rw [← hU, neg_pow y j]
    field_simp
    try ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hden, div_eq_mul_one_div (BG bs d M g'),
    ← mul_sub, geom_trunc hU0 hUy0 J]
  have hV : -(((labels M).sup fun g => vhat bs d M g : ℕ) : ℤ) ≤ -((vhat bs d M g' : ℕ) : ℤ) := by
    have := Finset.le_sup (f := fun g => vhat bs d M g) hgl
    omega
  have hUi : OrdGE (U ^ J * (U + y))⁻¹ 0 := ((hregU.pow J).mul hregUy).inv
    (mul_ne_zero (pow_ne_zero J hu0) hu0) |>.1
  have h1 := ((ordGE_BG bs d M g').mul (hy.neg.pow J)).mul hUi
  rw [div_eq_mul_inv, ← mul_assoc]
  refine h1.mono ?_
  push_cast
  linarith

/-- Error bounds for a finite sum of products. -/
theorem sum_err {s : Finset Label} (p : Label → K⸨X⸩) (E : Label → ℕ → K⸨X⸩)
    (h : ∀ g ∈ s, ∃ c : ℤ, ∀ J : ℕ, OrdGE (E g J) ((J : ℤ) + c)) :
    ∃ c : ℤ, ∀ J : ℕ, OrdGE (∑ g ∈ s, p g * E g J) ((J : ℤ) + c) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun J => by simpa using OrdGE.zero (K := K) _⟩
  | insert g s hgs ih =>
    obtain ⟨c₁, hc₁⟩ := h g (Finset.mem_insert_self g s)
    obtain ⟨c₂, hc₂⟩ := ih fun g' hg' => h g' (Finset.mem_insert_of_mem hg')
    refine ⟨min ((p g).order + c₁) c₂, fun J => ?_⟩
    rw [Finset.sum_insert hgs]
    refine OrdGE.add (((ordGE_order (p g)).mul (hc₁ J)).mono ?_) ((hc₂ J).mono ?_)
    · have := min_le_left ((p g).order + c₁) c₂
      linarith
    · have := min_le_right ((p g).order + c₁) c₂
      linarith

/-- The chain expansion of `S_{g,M}`: the truncation at `j < J` has error of order `≥ J + c`. -/
theorem SG_expansion (hbs : bs ≠ 0) : ∀ M : ℕ, 1 ≤ M → ∀ g : Label,
    ∃ c : ℤ, ∀ J : ℕ, OrdGE (SG bs d M g - sExp bs d M g J) ((J : ℤ) + c) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
  intro hM g
  classical
  set ν : K := kacHL g bs + (g.lvl : K) with hν
  set y : K⸨X⸩ := delG bs g with hy
  have hyo : OrdGE y 1 := ordGE_deltaG_one hbs g
  set p : Label → K⸨X⸩ := fun g' => RG bs d g' / (y - delG bs g') with hp
  set E : Label → ℕ → K⸨X⸩ := fun g' J =>
    SG bs d (M - g'.lvl) g' - (if g'.lvl = M then 1 else sExp bs d (M - g'.lvl) g' J) with hE
  have hErr : ∀ g' ∈ labelsAt bs M ν, ∃ c : ℤ, ∀ J : ℕ, OrdGE (E g' J) ((J : ℤ) + c) := by
    intro g' hg'
    have hle := lvl_le_of_mem_labels ((mem_labelsAt bs).1 hg').1
    have hpos := lvl_pos_of_mem_labels ((mem_labelsAt bs).1 hg').1
    by_cases hD : g'.lvl = M
    · refine ⟨0, fun J => ?_⟩
      have h0 : E g' J = 0 := by
        simp only [hE]
        rw [if_pos hD, hD, Nat.sub_self, SG_zero, sub_self]
      rw [h0]
      exact OrdGE.zero (K := K) _
    · obtain ⟨c, hc⟩ := ih (M - g'.lvl) (by omega) (by omega) g'
      exact ⟨c, fun J => by simpa only [hE, if_neg hD] using hc J⟩
  obtain ⟨c₁, hc₁⟩ := sum_err p E hErr
  set V : ℤ := (((labels M).sup fun g => vhat bs d M g : ℕ) : ℤ) with hV
  refine ⟨min c₁ (-V), fun J => ?_⟩
  -- the exact identity for the error
  have hz : ∀ g' : Label, zG bs g - hG bs g' = HahnSeries.C ν + y - hG bs g' := by
    intro g'
    rw [hν, hy]
    unfold zG delG deltaG
    rw [map_add, map_natCast]
    ring
  have hid : SG bs d M g - sExp bs d M g J =
      ∑ g' ∈ labelsAt bs M ν, p g' * E g' J +
        (∑ g' ∈ (labels M).filter (fun g' => ¬ kacHL g' bs = ν),
          BG bs d M g' / (HahnSeries.C ν + y - hG bs g') - phiSum bs d M ν y J) := by
    have hcomb := comb bs d p M ν J
    have htail : chainTail bs d 0 M ν y = ∑ g' ∈ labelsAt bs M ν, p g' *
        (if g'.lvl = M then delG bs g' ^ 0 / ((0 : ℕ).factorial : K⸨X⸩)
          else chainTail bs d 0 (M - g'.lvl) (ν + (g'.lvl : K)) (delG bs g')) :=
      chainTail_eq bs d 0 M ν y
    have htails : ∀ n j, chainTail bs d j n ν y = ∑ g' ∈ labelsAt bs n ν, p g' *
        (if g'.lvl = n then delG bs g' ^ j / (j.factorial : K⸨X⸩)
          else chainTail bs d j (n - g'.lvl) (ν + (g'.lvl : K)) (delG bs g')) :=
      fun n j => chainTail_eq bs d j n ν y
    have hsExp : sExp bs d M g J = phiSum bs d M ν y J +
        ∑ g' ∈ labelsAt bs M ν, p g' * (if g'.lvl = M then 1 else sExp bs d (M - g'.lvl) g' J) := by
      rw [hcomb, ← htail]
      simp_rw [← htails]
      unfold sExp
      rw [← hν, ← hy]
      ring
    rw [SG_split bs d M hM g, hsExp, ← hν, ← hy]
    simp_rw [hz]
    simp only [hE, hp, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hid]
  refine OrdGE.add ((hc₁ J).mono ?_) ((reg_trunc bs d hbs M ν hyo J).mono ?_)
  · have := min_le_left c₁ (-V)
    linarith
  · have := min_le_right c₁ (-V)
    rw [← hV]
    linarith

/-- Lemma 7.12 over an arbitrary coefficient field, with the truncation error of order
`≥ J + c`. -/
theorem moment_expansion (hbs : bs ≠ 0) {N : ℕ} (_hN : 1 ≤ N) (lam : K) (k : ℕ) :
    ∃ c : ℤ, ∀ J : ℕ, OrdGE (fullMoment bs d N lam k -
      (chainFn bs d lam N k 0 + ∑ n ∈ Finset.Ioo 0 N, ∑ j ∈ Finset.range J,
        chainFn bs d lam n k j * phiRem bs d (N - n) (lam + (n : K)) j)) ((J : ℤ) + c) := by
  classical
  set p : Label → K⸨X⸩ := fun a => RG bs d a * delG bs a ^ (k - 1) with hp
  set E : Label → ℕ → K⸨X⸩ := fun a J =>
    SG bs d (N - a.lvl) a - (if a.lvl = N then 1 else sExp bs d (N - a.lvl) a J) with hE
  have hErr : ∀ a ∈ labelsAt bs N lam, ∃ c : ℤ, ∀ J : ℕ, OrdGE (E a J) ((J : ℤ) + c) := by
    intro a ha
    have hle := lvl_le_of_mem_labels ((mem_labelsAt bs).1 ha).1
    have hpos := lvl_pos_of_mem_labels ((mem_labelsAt bs).1 ha).1
    by_cases hD : a.lvl = N
    · refine ⟨0, fun J => ?_⟩
      have h0 : E a J = 0 := by
        simp only [hE]
        rw [if_pos hD, hD, Nat.sub_self, SG_zero, sub_self]
      rw [h0]
      exact OrdGE.zero (K := K) _
    · obtain ⟨c, hc⟩ := SG_expansion bs d hbs (N - a.lvl) (by omega) a
      exact ⟨c, fun J => by simpa only [hE, if_neg hD] using hc J⟩
  obtain ⟨c, hc⟩ := sum_err p E hErr
  refine ⟨c, fun J => ?_⟩
  have hcl : collClass N bs lam = labelsAt bs N lam := by
    ext a
    rw [mem_collClass, mem_labelsAt]
  have hmom : fullMoment bs d N lam k = ∑ a ∈ labelsAt bs N lam, p a * SG bs d (N - a.lvl) a := by
    unfold fullMoment
    rw [hcl]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hw := ((mem_labelsAt bs).1 ha).2
    rw [hp]
    dsimp only
    rw [BG, delG, hw]
    ring
  have hfn : ∀ n j, chainFn bs d lam n k j = ∑ a ∈ labelsAt bs n lam, p a *
      (if a.lvl = n then delG bs a ^ j / (j.factorial : K⸨X⸩)
        else chainTail bs d j (n - a.lvl) (lam + (a.lvl : K)) (delG bs a)) := by
    intro n j
    rfl
  have hid : fullMoment bs d N lam k -
      (chainFn bs d lam N k 0 + ∑ n ∈ Finset.Ioo 0 N, ∑ j ∈ Finset.range J,
        chainFn bs d lam n k j * phiRem bs d (N - n) (lam + (n : K)) j) =
      ∑ a ∈ labelsAt bs N lam, p a * E a J := by
    rw [hmom, hfn N 0]
    simp_rw [hfn]
    rw [← comb bs d p N lam J]
    simp only [hE, mul_sub, Finset.sum_sub_distrib]
  rw [hid]
  exact hc J

end General

/-- Lemma 7.12.  The expansion is an identity of germs; it uses no cited input.

Paper label: lem:chain-expansion -/
theorem lem_chain_expansion : Stmt_lem_chain_expansion := by
  intro b hb N hN lam _ k _ m
  have hbs : bsC b ≠ 0 := by simpa [bsC] using hb
  obtain ⟨c, hc⟩ := moment_expansion (bsC b) dvar hbs hN (pt lam) k
  refine ⟨(m - c + 1).toNat, fun J' hJ' => ?_⟩
  have hlt : m < (J' : ℤ) + c := by omega
  have h0 := (hc J').coeff_eq_zero hlt
  rw [HahnSeries.coeff_sub, sub_eq_zero] at h0
  simp only [chainFnC, phiRemC, fullMomentC, pt_add_natCast]
  exact h0

end Virasoro
