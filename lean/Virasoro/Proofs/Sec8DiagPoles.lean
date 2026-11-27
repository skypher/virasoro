import Virasoro.Proofs.Sec8DiagBridge
import Virasoro.Proofs.Sec8Jets

/-!
# Lemma 8.4: pole orders of the residues between nodes

`R_g = 𝒜_g 𝒩_g`; `𝒜_g = ½ ∏_{(a,e)} (a b + e b⁻¹)⁻¹`.  At `b⋆² = -p'/p` a factor vanishes exactly
for `(a,e) = i(p,p')`, and then with slope `2ip`; so its germ has order `0` or `1`.  For the label
from `ν` to `ν'` (`Δ = L_{ν'} - L_ν` odd) the box `[1-u,u] × [1-v,v]` contains exactly the points
`i(p,p')` with `1 ≤ |i| ≤ (Δ-1)/2`, and `𝒩_g(b⋆,d) ≠ 0`; so `R_g` has order exactly `1 - Δ`.
-/

namespace Virasoro

open scoped LaurentSeries

variable {p p' r s : ℕ} {b : ℂ}

section Orders

variable {K : Type*} [Field K]

theorem dgOrderTop_inv {x : K⸨X⸩} (hx : x ≠ 0) : x⁻¹.orderTop = -x.orderTop := by
  have h := HahnSeries.orderTop_mul x x⁻¹
  rw [mul_inv_cancel₀ hx, HahnSeries.orderTop_one] at h
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (HahnSeries.orderTop_ne_top.2 hx)
  have hx' : x⁻¹ ≠ 0 := inv_ne_zero hx
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.1 (HahnSeries.orderTop_ne_top.2 hx')
  rw [← hn, ← hm] at h ⊢
  have : (0 : ℤ) = n + m := by exact_mod_cast h
  rw [show m = -n by omega]
  rfl

/-- A germ regular at `0` with nonzero value has order `0`. -/
theorem dgOrderTop_zero {x : K⸨X⸩} (hx : (0 : WithTop ℤ) ≤ x.orderTop) (h0 : x.coeff 0 ≠ 0) :
    x.orderTop = 0 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at h0
  apply le_antisymm _ hx
  exact HahnSeries.orderTop_le_of_coeff_ne_zero h0

/-- A germ regular at `0` with value `0` and nonzero slope has order `1`. -/
theorem dgOrderTop_one {x : K⸨X⸩} (hx : (0 : WithTop ℤ) ≤ x.orderTop) (h0 : x.coeff 0 = 0)
    (h1 : x.coeff 1 ≠ 0) : x.orderTop = 1 := by
  apply le_antisymm (HahnSeries.orderTop_le_of_coeff_ne_zero h1)
  rw [HahnSeries.le_orderTop_iff_forall] at hx ⊢
  intro m hm
  have hm' : m < 1 := by exact_mod_cast hm
  rcases lt_or_eq_of_le (show m ≤ 0 by omega) with h | h
  · exact hx m (by exact_mod_cast h)
  · rw [h]; exact h0

end Orders

section Products

variable {K : Type*} [Field K]

theorem dgOrderTop_prod {α : Type*} (t : Finset α) (f : α → K⸨X⸩) :
    (∏ i ∈ t, f i).orderTop = ∑ i ∈ t, (f i).orderTop := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [HahnSeries.orderTop_one]
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, HahnSeries.orderTop_mul, ih]

end Products

/-- The fusion polynomial `𝒩_{u,v}(b⋆, d)` is nonzero in `ℂ(d)`. -/
theorem genP_ratC_ne {b : ℂ} (hb : b ≠ 0) (u v : ℕ) : genP u v (RatFunc.C b : Kd) dvar ≠ 0 := by
  have key : ∀ w : ℂ, RatFunc.C w - (dvar : Kd) ≠ 0 := by
    intro w h
    have h1 := congrArg RatFunc.intDegree (sub_eq_zero.1 h)
    rw [RatFunc.intDegree_C, dvar, RatFunc.intDegree_X] at h1
    exact absurd h1 (by norm_num)
  have hfac : ∀ (k l : ℕ) (σ : ℂ),
      (lamSq (RatFunc.C b : Kd) dvar - ((k : Kd) * RatFunc.C b + RatFunc.C σ * (l : Kd) *
        (RatFunc.C b)⁻¹) ^ 2) / 4 ≠ 0 := by
    intro k l σ
    have e : (lamSq (RatFunc.C b : Kd) dvar - ((k : Kd) * RatFunc.C b + RatFunc.C σ * (l : Kd) *
        (RatFunc.C b)⁻¹) ^ 2) / 4 =
        RatFunc.C (((b + b⁻¹) ^ 2 - ((k : ℂ) * b + σ * l * b⁻¹) ^ 2) / 4) - dvar := by
      unfold lamSq
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_inv₀, map_natCast, map_ofNat]
      ring
    rw [e]
    exact key _
  unfold genP
  refine Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2 fun l _ => ?_
  refine mul_ne_zero ?_ ?_
  · have := hfac k l 1
    simpa using this
  · have := hfac k l (-1)
    have e2 : ((k : Kd) * RatFunc.C b + RatFunc.C (-1 : ℂ) * (l : Kd) * (RatFunc.C b)⁻¹) =
        (k : Kd) * RatFunc.C b - (l : Kd) * (RatFunc.C b)⁻¹ := by simp; ring
    rwa [e2] at this

/-- The value and slope of a factor `a b + e b⁻¹` of `𝒜` along `b = b⋆ + t`. -/
theorem j1_Afac {bs : Kd} (hbs : bs ≠ 0) (a e : ℤ) :
    J1 ((a : Kd⸨X⸩) * bGerm bs + (e : Kd⸨X⸩) * (bGerm bs)⁻¹) ((a : Kd) * bs + (e : Kd) * bs⁻¹)
      ((a : Kd) - (e : Kd) / bs ^ 2) := by
  have h := (((j2_intCast (K := Kd) a).mul (j2_bGerm bs)).add
    ((j2_intCast (K := Kd) e).mul (j2_bGerm_inv hbs))).toJ1
  refine h.congr (by ring) (by ring)

/-- At `b⋆² = -p'/p`: `a b⋆ + e b⋆⁻¹ = 0` iff `p e = p' a`. -/
theorem Afac_zero_iff {p p' : ℕ} {b : ℂ} (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p)
    (a e : ℤ) : (a : ℂ) * b + (e : ℂ) * b⁻¹ = 0 ↔ (p : ℤ) * e = p' * a := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
    have h0 : -(p' : ℂ) / p ≠ 0 := div_ne_zero (neg_ne_zero.2 hpc') hpc
    exact h0 (by simpa using hb.symm)
  have e1 : (a : ℂ) * b + (e : ℂ) * b⁻¹ = ((p : ℂ) * e - p' * a) / (p * b) := by
    calc (a : ℂ) * b + (e : ℂ) * b⁻¹ = ((a : ℂ) * b ^ 2 + e) / b := by field_simp
      _ = ((a : ℂ) * (-(p' : ℂ) / p) + e) / b := by rw [hb]
      _ = ((p : ℂ) * e - p' * a) / (p * b) := by field_simp; ring
  rw [e1, div_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h (mul_ne_zero hpc hb0)
  · intro h; left; exact_mod_cast h

/-- `|x_g| = |S_ν|` and `y_g = |S_{ν'}|` for the label from `ν` to `ν'`. -/
theorem nodeLabel_xy (hset : MinimalSetting p p' r s b) {ν ν' : Node} (hlt : ν.2 < ν'.2)
    (hodd : (ν'.2 - ν.2) % 2 = 1) :
    |(p' : ℤ) * (nodeLabel p p' r s ν ν').1 - p * (nodeLabel p p' r s ν ν').2| =
        |nodeS p p' r s ν| ∧
      (p' : ℤ) * (nodeLabel p p' r s ν ν').1 + p * (nodeLabel p p' r s ν ν').2 =
        |nodeS p p' r s ν'| := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb := hset.2.2.2.2.2.2.2.2
  obtain ⟨hiff, h1, h2, -⟩ := node_labels_ii hset ν ν' hlt hodd
  obtain ⟨hw, hw'⟩ := (hiff _ h1 h2).2 rfl
  rw [kacH_add_lvl hp hp' hb, nodeWt_eq, momWt_eq_iff hp hp'] at hw'
  rw [kacHL_eq_momWt hp hp' hb, nodeWt_eq, momWt_eq_iff hp hp'] at hw
  have hy0 : 0 < (p' : ℤ) * (nodeLabel p p' r s ν ν').1 + p * (nodeLabel p p' r s ν ν').2 := by
    have : 0 < p' * (nodeLabel p p' r s ν ν').1 := Nat.mul_pos hp' h1
    have : 0 < p * (nodeLabel p p' r s ν ν').2 := Nat.mul_pos hp h2
    positivity
  refine ⟨(sq_eq_sq_iff_abs_eq_abs _ _).1 hw, ?_⟩
  have := (sq_eq_sq_iff_abs_eq_abs _ _).1 hw'
  rwa [abs_of_pos hy0] at this

/-- Bounds for the lattice points of the box: with `U = 2p'u = y + x`, `V = 2pv = y - x` and
`y - |x| = (2m+1)P + e`, `|e| < P = pp'`. -/
theorem box_line_bounds {P U V x y e : ℤ} {m : ℕ} (hP : 0 < P) (hU : U = y + x) (hV : V = y - x)
    (hgap : y - |x| = (2 * m + 1) * P + e) (he : |e| < P) :
    (∀ i : ℤ, 0 < i → (2 * (i * P) ≤ U ∧ 2 * (i * P) ≤ V ↔ i ≤ m)) ∧
    (∀ i : ℤ, 0 < i → (2 * (i * P) < U ∧ 2 * (i * P) < V ↔ i ≤ m)) := by
  have he' := abs_lt.1 he
  have hUx : y - |x| ≤ U := by rw [hU]; linarith [neg_abs_le x]
  have hVx : y - |x| ≤ V := by rw [hV]; linarith [le_abs_self x]
  have hmin : U = y - |x| ∨ V = y - |x| := by
    rcases abs_cases x with ⟨h, -⟩ | ⟨h, -⟩
    · right; rw [hV, h]
    · left; rw [hU, h]; ring
  have upper : ∀ i : ℤ, i ≤ m → 2 * (i * P) < y - |x| := by
    intro i hi
    have : i * P ≤ (m : ℤ) * P := mul_le_mul_of_nonneg_right hi hP.le
    linarith
  have lower : ∀ i : ℤ, (m : ℤ) + 1 ≤ i → y - |x| < 2 * (i * P) := by
    intro i hi
    have : ((m : ℤ) + 1) * P ≤ i * P := mul_le_mul_of_nonneg_right hi hP.le
    linarith
  refine ⟨fun i _ => ⟨fun ⟨h1, h2⟩ => ?_, fun hi => ⟨by linarith [upper i hi], by linarith [upper i hi]⟩⟩,
    fun i _ => ⟨fun ⟨h1, h2⟩ => ?_, fun hi => ⟨by linarith [upper i hi], by linarith [upper i hi]⟩⟩⟩
  · by_contra hcon
    push_neg at hcon
    have := lower i (by omega)
    rcases hmin with h | h <;> linarith
  · by_contra hcon
    push_neg at hcon
    have := lower i (by omega)
    rcases hmin with h | h <;> linarith

/-- The lattice points `i(p,p')` in the box of the label from `ν` to `ν'` are those with
`1 ≤ |i| ≤ (Δ-1)/2`; there are `Δ - 1` of them. -/
theorem line_count (hset : MinimalSetting p p' r s b) {ν ν' : Node} (hlt : ν.2 < ν'.2)
    (hodd : (ν'.2 - ν.2) % 2 = 1) :
    ((genAIndex (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2).filter
      (fun pq => (p : ℤ) * pq.2 = p' * pq.1)).card = ν'.2 - ν.2 - 1 := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hint, -⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  obtain ⟨hx, hy⟩ := nodeLabel_xy hset hlt hodd
  obtain ⟨e, he, hgap⟩ := nodeS_gap hr0 hr hs0 hs hint ν ν' hlt hodd
  obtain ⟨-, h1, h2, -⟩ := node_labels_ii hset ν ν' hlt hodd
  set g := nodeLabel p p' r s ν ν' with hg
  have hcop' : IsCoprime (p : ℤ) p' := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast hcop
  have hS0 : 0 < |nodeS p p' r s ν| := by
    have h0 := nodeS_abs_ge hset ν
    have hn0 : (p' : ℤ) * r - p * s ≠ 0 := by
      intro h
      have hd : (p : ℤ) ∣ p' * r := ⟨s, by linarith⟩
      have := Int.le_of_dvd (by exact_mod_cast hr0) (hcop'.dvd_of_dvd_mul_left hd)
      have : (r : ℤ) < p := by exact_mod_cast hr
      omega
    have : 0 < |nodeS p p' r s (true, 0)| := by simpa [nodeS, nOrb] using hn0
    linarith
  set m : ℕ := (ν'.2 - ν.2 - 1) / 2 with hm
  have hΔ : ((ν'.2 : ℤ) - ν.2) = 2 * m + 1 := by omega
  set u : ℤ := (g.1 : ℤ) with hu
  set v : ℤ := (g.2 : ℤ) with hv
  set P : ℤ := (p : ℤ) * p' with hPdef
  have hP : 0 < P := by rw [hPdef]; exact_mod_cast Nat.mul_pos hp hp'
  have hgap' : ((p' : ℤ) * u + p * v) - |(p' : ℤ) * u - p * v| = (2 * m + 1) * P + e := by
    rw [hy, hx, hgap, hΔ]; ring
  obtain ⟨B1, B2⟩ := box_line_bounds (U := 2 * p' * u) (V := 2 * p * v) hP (by ring) (by ring)
    hgap' he
  -- scaling facts
  have sp : (0 : ℤ) < 2 * p := by positivity
  have sp' : (0 : ℤ) < 2 * p' := by positivity
  have hscale1 : ∀ i : ℤ, 2 * p' * (i * p) = 2 * (i * P) := fun i => by rw [hPdef]; ring
  have hscale2 : ∀ i : ℤ, 2 * p * (i * p') = 2 * (i * P) := fun i => by rw [hPdef]; ring
  have key : (genAIndex g.1 g.2).filter (fun pq => (p : ℤ) * pq.2 = p' * pq.1) =
      ((Finset.Icc (-(m : ℤ)) m).erase 0).image (fun i : ℤ => (i * p, i * p')) := by
    ext ⟨a, c⟩
    simp only [genAIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_image, Finset.mem_erase, ne_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨⟨ha1, ha2⟩, hc1, hc2⟩, h0, huv⟩, hline⟩
      obtain ⟨i, rfl⟩ := hcop'.dvd_of_dvd_mul_left (show (p : ℤ) ∣ p' * a from ⟨c, by linarith⟩)
      have hci : c = i * p' := by
        have : (p : ℤ) * c = p * (i * p') := by rw [hline]; ring
        exact mul_left_cancel₀ (by exact_mod_cast hp.ne') this
      subst hci
      have hi0 : i ≠ 0 := by rintro rfl; exact h0 (by simp)
      have ha2' : i * p ≤ u := by rw [mul_comm] at ha2; exact ha2
      have ha1' : 1 - u ≤ i * p := by rw [mul_comm] at ha1; exact ha1
      have hc2' : i * p' ≤ v := hc2
      have hc1' : 1 - v ≤ i * p' := hc1
      refine ⟨i, ⟨hi0, ?_, ?_⟩, by ring, rfl⟩
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have hj : 0 < -i := by omega
          have k1 : 2 * ((-i) * P) < 2 * p' * u := by
            have : (-i) * p < u := by linarith
            have := mul_lt_mul_of_pos_left this sp'
            rw [hscale1] at this; exact this
          have k2 : 2 * ((-i) * P) < 2 * p * v := by
            have : (-i) * p' < v := by linarith
            have := mul_lt_mul_of_pos_left this sp
            rw [hscale2] at this; exact this
          have := (B2 (-i) hj).1 ⟨k1, k2⟩
          omega
        · omega
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · omega
        · have k1 : 2 * (i * P) ≤ 2 * p' * u := by
            have := mul_le_mul_of_nonneg_left ha2' sp'.le
            rw [hscale1] at this; exact this
          have k2 : 2 * (i * P) ≤ 2 * p * v := by
            have := mul_le_mul_of_nonneg_left hc2' sp.le
            rw [hscale2] at this; exact this
          exact (B1 i hpos).1 ⟨k1, k2⟩
    · rintro ⟨i, ⟨hi0, hi1, hi2⟩, rfl, rfl⟩
      have hpu : (0 : ℤ) < u := by rw [hu]; exact_mod_cast h1
      have hpv : (0 : ℤ) < v := by rw [hv]; exact_mod_cast h2
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩, by ring⟩
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have hj : 0 < -i := by omega
          have k := ((B2 (-i) hj).2 (by omega)).1
          rw [← hscale1] at k
          have := lt_of_mul_lt_mul_left k sp'.le
          linarith [mul_comm i (p : ℤ)]
        · have : 0 < i * p := mul_pos hpos (by exact_mod_cast hp)
          linarith [mul_comm i (p : ℤ)]
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have : i * p < 0 := mul_neg_of_neg_of_pos hneg (by exact_mod_cast hp)
          linarith [mul_comm i (p : ℤ)]
        · have k := ((B1 i hpos).2 hi2).1
          rw [← hscale1] at k
          have := le_of_mul_le_mul_left k sp'
          linarith [mul_comm i (p : ℤ)]
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have hj : 0 < -i := by omega
          have k := ((B2 (-i) hj).2 (by omega)).2
          rw [← hscale2] at k
          have := lt_of_mul_lt_mul_left k sp.le
          linarith
        · have : 0 < i * p' := mul_pos hpos (by exact_mod_cast hp')
          linarith
      · rcases lt_or_gt_of_ne hi0 with hneg | hpos
        · have : i * p' < 0 := mul_neg_of_neg_of_pos hneg (by exact_mod_cast hp')
          linarith
        · have k := ((B1 i hpos).2 hi2).2
          rw [← hscale2] at k
          exact le_of_mul_le_mul_left k sp
      · rintro ⟨h1', h2'⟩
        have : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
        exact hi0 (by rcases mul_eq_zero.1 (show (p : ℤ) * i = 0 by linarith) with h | h <;> simp_all)
      · rintro ⟨h1', h2'⟩
        have hx0 : (p' : ℤ) * u - p * v = 0 := by rw [hu, hv, ← h1', ← h2']; ring
        rw [hx0, abs_zero] at hx
        linarith
  rw [key, Finset.card_image_of_injective]
  · rw [Finset.card_erase_of_mem (by simp), Int.card_Icc]
    omega
  · intro i i' h
    simp only [Prod.mk.injEq] at h
    exact mul_right_cancel₀ (by exact_mod_cast hp.ne') h.1

/-- The order of a factor of `𝒜` along `b = b⋆ + t`: `1` on the line `ℤ(p,p')`, `0` off it. -/
theorem factor_orderTop (hset : MinimalSetting p p' r s b) (pq : ℤ × ℤ) (hpq : pq ≠ (0, 0)) :
    ((pq.1 : Kd⸨X⸩) * bGerm (bsC b) + (pq.2 : Kd⸨X⸩) * (bGerm (bsC b))⁻¹).orderTop =
      if (p : ℤ) * pq.2 = p' * pq.1 then 1 else 0 := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb := hset.2.2.2.2.2.2.2.2
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p ≠ 0 := div_ne_zero (neg_ne_zero.2 hpc') hpc
    exact h0 (by simpa using hb.symm)
  have hbs : (bsC b : Kd) ≠ 0 := by simpa [bsC] using hb0
  have hJ := j1_Afac hbs pq.1 pq.2
  have hord : (0 : WithTop ℤ) ≤
      ((pq.1 : Kd⸨X⸩) * bGerm (bsC b) + (pq.2 : Kd⸨X⸩) * (bGerm (bsC b))⁻¹).orderTop := by
    simpa [OrdGE] using hJ.1
  have hval : (pq.1 : Kd) * bsC b + (pq.2 : Kd) * (bsC b)⁻¹ =
      RatFunc.C ((pq.1 : ℂ) * b + (pq.2 : ℂ) * b⁻¹) := by
    simp [bsC, map_add, map_mul, map_inv₀, map_intCast]
  split_ifs with hline
  · have hz : (pq.1 : ℂ) * b + (pq.2 : ℂ) * b⁻¹ = 0 := (Afac_zero_iff hp hp' hb _ _).2 hline
    have h1ne : pq.1 ≠ 0 := by
      intro h
      apply hpq
      have : (p : ℤ) * pq.2 = 0 := by rw [hline, h]; ring
      have h2 : pq.2 = 0 := by
        rcases mul_eq_zero.1 this with h' | h'
        · exact absurd h' (by exact_mod_cast hp.ne')
        · exact h'
      exact Prod.ext h h2
    refine dgOrderTop_one hord (by rw [hJ.2.1, hval, hz, map_zero]) ?_
    rw [hJ.2.2]
    have hsl : (pq.1 : Kd) - (pq.2 : Kd) / bsC b ^ 2 = RatFunc.C (2 * (pq.1 : ℂ)) := by
      have hb2 : (bsC b : Kd) ^ 2 = RatFunc.C (-(p' : ℂ) / p) := by
        rw [bsC, ← map_pow, hb]
      have hq : (pq.2 : ℂ) = (p' : ℂ) * pq.1 / p := by
        have : ((p : ℤ) * pq.2 : ℤ) = ((p' : ℤ) * pq.1 : ℤ) := hline
        have hc : (p : ℂ) * (pq.2 : ℂ) = (p' : ℂ) * (pq.1 : ℂ) := by exact_mod_cast this
        field_simp
        linear_combination hc
      rw [hb2]
      have e2 : (pq.2 : Kd) = RatFunc.C (pq.2 : ℂ) := (map_intCast _ _).symm
      have e1 : (pq.1 : Kd) = RatFunc.C (pq.1 : ℂ) := (map_intCast _ _).symm
      rw [e2, e1, ← map_div₀, ← map_sub, hq]
      congr 1
      field_simp
      ring
    rw [hsl]
    exact (map_ne_zero _).2 (mul_ne_zero two_ne_zero (by exact_mod_cast h1ne))
  · refine dgOrderTop_zero hord ?_
    rw [hJ.2.1, hval]
    exact (map_ne_zero _).2 (fun h => hline ((Afac_zero_iff hp hp' hb _ _).1 h))

/-- The order of the germ of `𝒜_{u,v}` is minus the number of lattice points in its box. -/
theorem genA_orderTop (hset : MinimalSetting p p' r s b) (u v : ℕ) :
    (genA u v (bGerm (bsC b))).orderTop =
      ((-(((genAIndex u v).filter (fun pq => (p : ℤ) * pq.2 = p' * pq.1)).card : ℤ) : ℤ) :
        WithTop ℤ) := by
  unfold genA
  rw [HahnSeries.orderTop_mul, dgOrderTop_prod]
  have h2 : ((2 : Kd⸨X⸩)⁻¹).orderTop = 0 := by
    have := ((regVal_ofNat (K := Kd) 2).inv (by norm_num))
    exact dgOrderTop_zero (by simpa [OrdGE] using this.1) (by rw [this.2]; norm_num)
  have hterm : ∀ pq ∈ genAIndex u v,
      (((pq.1 : Kd⸨X⸩) * bGerm (bsC b) + (pq.2 : Kd⸨X⸩) * (bGerm (bsC b))⁻¹)⁻¹).orderTop =
        (((if (p : ℤ) * pq.2 = p' * pq.1 then -1 else 0 : ℤ)) : WithTop ℤ) := by
    intro pq hpq
    have hpq0 : pq ≠ (0, 0) := (Finset.mem_filter.1 hpq).2.1
    have hF := factor_orderTop hset pq hpq0
    have hne : ((pq.1 : Kd⸨X⸩) * bGerm (bsC b) + (pq.2 : Kd⸨X⸩) * (bGerm (bsC b))⁻¹) ≠ 0 := by
      intro h
      rw [h, HahnSeries.orderTop_zero] at hF
      split_ifs at hF <;> exact absurd hF (by simp)
    rw [dgOrderTop_inv hne, hF]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl hterm, h2, zero_add, ← WithTop.coe_sum]
  congr 1
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_neg, nsmul_eq_mul,
    mul_one]

/-- Lemma 8.4 (`lem:node-poles`).
Paper label: lem:node-poles -/
theorem lem_node_poles : Stmt_lem_node_poles := by
  intro p p' r s b hset ν ν' hlt hodd
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb := hset.2.2.2.2.2.2.2.2
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p ≠ 0 := div_ne_zero (neg_ne_zero.2 hpc') hpc
    exact h0 (by simpa using hb.symm)
  have hbs : (bsC b : Kd) ≠ 0 := by simpa [bsC] using hb0
  have hP := regVal_genP hbs dvar (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2
  have hPord : (genP (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2 (bGerm (bsC b))
      (HahnSeries.C dvar)).orderTop = 0 :=
    dgOrderTop_zero (by simpa [OrdGE] using hP.1) (by rw [hP.2]; exact genP_ratC_ne hb0 _ _)
  have hord : (nodeR p p' r s b ν ν').orderTop = ((1 - ((ν'.2 : ℤ) - ν.2) : ℤ) : WithTop ℤ) := by
    unfold nodeR RG genR
    rw [HahnSeries.orderTop_mul, genA_orderTop hset, hPord, add_zero, line_count hset hlt hodd]
    congr 1
    omega
  refine ⟨hord.ge, ?_⟩
  unfold nodeRho
  exact HahnSeries.coeff_orderTop_ne hord

end Virasoro
