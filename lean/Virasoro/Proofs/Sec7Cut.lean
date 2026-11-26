import Virasoro.Statements.Sec7FixedCharge
import Virasoro.Proofs.Sec4Core1
import Virasoro.Proofs.Sec6Kac
import Virasoro.Proofs.Sec4Thm

/-!
# Lemma 7.10 (cutting a chain)

The proof follows the paper: writing `δ_L = y - (y - δ_{g₁}) - ∑_m (δ_{g_{m-1}} - δ_{g_m})`
cancels one link at a time.  With the recursive encoding of chains this becomes an identity for
the tails (`tail_cut`), proved by induction on the level, from which the identity for the
chain functions follows (`chainFn_cut`).  The only input is that no link denominator vanishes
(`link_ne`), which holds for the germ `b⋆ + t` because `b²` is not rational there.
-/

namespace Virasoro

open scoped LaurentSeries

section General

variable {K : Type*} [Field K] [CharZero K] (bs d : K)

theorem chainTail_eq (j D : ℕ) (ν : K) (y : K⸨X⸩) :
    chainTail bs d j D ν y =
      ∑ g ∈ labelsAt bs D ν, RG bs d g / (y - delG bs g) *
        (if g.lvl = D then delG bs g ^ j / (j.factorial : K⸨X⸩)
          else chainTail bs d j (D - g.lvl) (ν + (g.lvl : K)) (delG bs g)) := by
  rw [chainTail]
  exact Finset.sum_attach (labelsAt bs D ν) (fun g => RG bs d g / (y - delG bs g) *
        (if g.lvl = D then delG bs g ^ j / (j.factorial : K⸨X⸩)
          else chainTail bs d j (D - g.lvl) (ν + (g.lvl : K)) (delG bs g)))

theorem natCast_laurent_ne_zero {n : ℕ} (hn : n ≠ 0) : (n : K⸨X⸩) ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : K⸨X⸩ => x.coeff 0) h
  simp only [HahnSeries.coeff_zero] at h0
  rw [(regVal_natCast n).2] at h0
  exact hn (by exact_mod_cast h0)

theorem factorial_step (x : K⸨X⸩) {j : ℕ} (hj : 1 ≤ j) :
    (j : K⸨X⸩) * (x ^ j / (j.factorial : K⸨X⸩)) =
      x * (x ^ (j - 1) / ((j - 1).factorial : K⸨X⸩)) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hf : ((i + 1).factorial : K⸨X⸩) = ((i + 1 : ℕ) : K⸨X⸩) * (i.factorial : K⸨X⸩) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have h1 : ((i + 1 : ℕ) : K⸨X⸩) ≠ 0 := natCast_laurent_ne_zero (by omega)
  have h2 : (i.factorial : K⸨X⸩) ≠ 0 := natCast_laurent_ne_zero (Nat.factorial_ne_zero i)
  rw [hf, Nat.add_sub_cancel]
  field_simp
  ring

/-- The link condition: consecutive labels of a chain have different coordinates. -/
def LinkNe : Prop :=
  ∀ g g' : Label, 0 < g.1 → 0 < g.2 → 0 < g'.1 → 0 < g'.2 →
    kacHL g' bs = kacHL g bs + (g.lvl : K) → delG bs g ≠ delG bs g'

theorem mem_labelsAt {D : ℕ} {ν : K} {g : Label} :
    g ∈ labelsAt bs D ν ↔ g ∈ labels D ∧ kacHL g bs = ν := by
  classical
  unfold labelsAt
  exact Finset.mem_filter

theorem pos_of_mem_labels {D : ℕ} {g : Label} (hg : g ∈ labels D) : 0 < g.1 ∧ 0 < g.2 := by
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg
  exact ⟨hg.1.1.1, hg.1.2.1⟩

theorem mem_labels_self {D : ℕ} {g : Label} (hg : g ∈ labels D) : g ∈ labels g.lvl := by
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg ⊢
  have h1 := Nat.le_mul_of_pos_right g.1 hg.1.2.1
  have h2 := Nat.le_mul_of_pos_left g.2 hg.1.1.1
  exact ⟨⟨⟨hg.1.1.1, h1⟩, ⟨hg.1.2.1, h2⟩⟩, le_rfl⟩

/-- Re-indexing the sum over cut points: for a prefactor `p` and weights `W`,
`∑_{0<n<D} (∑_{g ∈ L_n(ν)} p g · [ℓ_g = n ? 1 : T₀(ν+ℓ_g, n-ℓ_g, δ_g)]) W n
= ∑_{g ∈ L_D(ν), ℓ_g < D} p g (W ℓ_g + ∑_{0<n'<D-ℓ_g} T₀(ν+ℓ_g, n', δ_g) W (ℓ_g + n'))`. -/
theorem cut_reindex (p : Label → K⸨X⸩) (W : ℕ → K⸨X⸩) (D : ℕ) (ν : K) :
    ∑ n ∈ Finset.Ioo 0 D,
        (∑ g ∈ labelsAt bs n ν, p g *
          (if g.lvl = n then 1 else chainTail bs d 0 (n - g.lvl) (ν + (g.lvl : K)) (delG bs g))) *
          W n =
      ∑ g ∈ labelsAt bs D ν,
        (if g.lvl < D then p g * (W g.lvl + ∑ n' ∈ Finset.Ioo 0 (D - g.lvl),
            chainTail bs d 0 n' (ν + (g.lvl : K)) (delG bs g) * W (g.lvl + n')) else 0) := by
  classical
  -- both sides as a double sum over pairs (n, g) with `ℓ_g ≤ n < D`
  have hL : ∀ n ∈ Finset.Ioo 0 D, labelsAt bs n ν = (labelsAt bs D ν).filter (fun g => g.lvl ≤ n) := by
    intro n hn
    ext g
    simp only [mem_labelsAt, Finset.mem_filter]
    have hnD : n ≤ D := (Finset.mem_Ioo.1 hn).2.le
    constructor
    · rintro ⟨hg, hw⟩
      refine ⟨⟨?_, hw⟩, lvl_le_of_mem_labels hg⟩
      simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg ⊢
      exact ⟨⟨⟨hg.1.1.1, le_trans hg.1.1.2 hnD⟩, ⟨hg.1.2.1, le_trans hg.1.2.2 hnD⟩⟩, le_trans hg.2 hnD⟩
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
    -- split the range `0 < n < D` with `ℓ_g ≤ n` into `n = ℓ_g` and `ℓ_g < n < D`
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
    rw [hsplit (fun n => p g *
      (if g.lvl = n then 1 else chainTail bs d 0 (n - g.lvl) (ν + (g.lvl : K)) (delG bs g)) * W n)]
    rw [if_pos rfl, mul_one, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n' hn' => ?_
    have hn'0 : 0 < n' := (Finset.mem_Ioo.1 hn').1
    rw [if_neg (by omega), Nat.add_sub_cancel_left]
    ring
  · rw [if_neg hlt]
    refine Finset.sum_eq_zero fun n hn => ?_
    have := (Finset.mem_Ioo.1 hn).2
    rw [if_neg (by omega), zero_mul]

theorem link_step (hlink : LinkNe bs) {D : ℕ} {ν : K} {g : Label} (hg : g ∈ labelsAt bs D ν) :
    ∀ g' ∈ labelsAt bs (D - g.lvl) (ν + (g.lvl : K)), delG bs g ≠ delG bs g' := by
  intro g' hg'
  obtain ⟨hgl, hgw⟩ := (mem_labelsAt bs).1 hg
  obtain ⟨hgl', hgw'⟩ := (mem_labelsAt bs).1 hg'
  have hp := pos_of_mem_labels hgl
  have hp' := pos_of_mem_labels hgl'
  exact hlink g g' hp.1 hp.2 hp'.1 hp'.2 (by rw [hgw', hgw])

/-- The cut identity for the tails: for an incoming coordinate `y` different from the
coordinates of the first labels,
`j T_j(ν,D,y) = y T_{j-1}(ν,D,y) - c^{(1)}_{ν→ν+D,j-1} - ∑_{0<n<D} T_0(ν,n,y) c^{(1)}_{ν+n→ν+D,j-1}`. -/
theorem tail_cut (hlink : LinkNe bs) : ∀ D : ℕ, 1 ≤ D → ∀ (ν : K) (y : K⸨X⸩),
    (∀ g ∈ labelsAt bs D ν, y ≠ delG bs g) → ∀ j : ℕ, 1 ≤ j →
    (j : K⸨X⸩) * chainTail bs d j D ν y =
      y * chainTail bs d (j - 1) D ν y - chainFn bs d ν D 1 (j - 1) -
        ∑ n ∈ Finset.Ioo 0 D, chainTail bs d 0 n ν y * chainFn bs d (ν + (n : K)) (D - n) 1 (j - 1) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro hD ν y hy j hj
  -- the cut sum, re-indexed by the first label
  have hT0 : ∀ n : ℕ, chainTail bs d 0 n ν y =
      ∑ g ∈ labelsAt bs n ν, RG bs d g / (y - delG bs g) *
        (if g.lvl = n then 1 else chainTail bs d 0 (n - g.lvl) (ν + (g.lvl : K)) (delG bs g)) := by
    intro n
    rw [chainTail_eq]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp
  have hcut := cut_reindex bs d (fun g => RG bs d g / (y - delG bs g))
    (fun n => chainFn bs d (ν + (n : K)) (D - n) 1 (j - 1)) D ν
  simp_rw [← hT0] at hcut
  rw [hcut, chainTail_eq bs d j D ν y, chainTail_eq bs d (j - 1) D ν y, chainFn,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hyg : y - delG bs g ≠ 0 := sub_ne_zero.2 (hy g hg)
  have hle := lvl_le_of_mem_labels ((mem_labelsAt bs).1 hg).1
  have hpos := lvl_pos_of_mem_labels ((mem_labelsAt bs).1 hg).1
  simp only [Nat.sub_self, pow_zero, mul_one]
  by_cases hD' : g.lvl = D
  · rw [if_pos hD', if_pos hD', if_neg (by omega), sub_zero]
    rw [← mul_assoc, mul_comm (j : K⸨X⸩), mul_assoc, factorial_step (delG bs g) hj]
    field_simp
    ring
  · have hlt : g.lvl < D := lt_of_le_of_ne hle hD'
    rw [if_neg hD', if_neg hD', if_pos hlt]
    have hIH := ih (D - g.lvl) (by omega) (by omega) (ν + (g.lvl : K)) (delG bs g)
      (link_step bs hlink hg) j hj
    have hW : ∀ n' ∈ Finset.Ioo 0 (D - g.lvl),
        chainFn bs d (ν + ((g.lvl + n' : ℕ) : K)) (D - (g.lvl + n')) 1 (j - 1) =
          chainFn bs d (ν + (g.lvl : K) + (n' : K)) (D - g.lvl - n') 1 (j - 1) := by
      intro n' _
      rw [Nat.cast_add, add_assoc, Nat.sub_sub]
    rw [Finset.sum_congr rfl fun n' hn' => by rw [hW n' hn']]
    rw [← mul_assoc, mul_comm (j : K⸨X⸩), mul_assoc, hIH]
    field_simp
    ring

/-- Lemma 7.10 over an arbitrary coefficient field, under the link condition. -/
theorem chainFn_cut (hlink : LinkNe bs) (lam : K) {D k j : ℕ} (_hD : 1 ≤ D) (hk : 1 ≤ k)
    (hj : 1 ≤ j) :
    (j : K⸨X⸩) * chainFn bs d lam D k j =
      chainFn bs d lam D (k + 1) (j - 1) -
        ∑ n ∈ Finset.Ioo 0 D, chainFn bs d lam n k 0 * chainFn bs d (lam + (n : K)) (D - n) 1 (j - 1) := by
  have hC0 : ∀ n : ℕ, chainFn bs d lam n k 0 =
      ∑ a ∈ labelsAt bs n lam, RG bs d a * delG bs a ^ (k - 1) *
        (if a.lvl = n then 1 else chainTail bs d 0 (n - a.lvl) (lam + (a.lvl : K)) (delG bs a)) := by
    intro n
    rw [chainFn]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  have hcut := cut_reindex bs d (fun a => RG bs d a * delG bs a ^ (k - 1))
    (fun n => chainFn bs d (lam + (n : K)) (D - n) 1 (j - 1)) D lam
  simp_rw [← hC0] at hcut
  rw [hcut, chainFn, chainFn, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hle := lvl_le_of_mem_labels ((mem_labelsAt bs).1 ha).1
  have hpos := lvl_pos_of_mem_labels ((mem_labelsAt bs).1 ha).1
  have hkk : k + 1 - 1 = (k - 1) + 1 := by omega
  rw [hkk, pow_succ]
  by_cases hD' : a.lvl = D
  · rw [if_pos hD', if_pos hD', if_neg (by omega), sub_zero]
    rw [← mul_assoc, mul_comm (j : K⸨X⸩), mul_assoc, factorial_step (delG bs a) hj]
    ring
  · have hlt : a.lvl < D := lt_of_le_of_ne hle hD'
    rw [if_neg hD', if_neg hD', if_pos hlt]
    have hT := tail_cut bs d hlink (D - a.lvl) (by omega) (lam + (a.lvl : K)) (delG bs a)
      (link_step bs hlink ha) j hj
    have hW : ∀ n' ∈ Finset.Ioo 0 (D - a.lvl),
        chainFn bs d (lam + ((a.lvl + n' : ℕ) : K)) (D - (a.lvl + n')) 1 (j - 1) =
          chainFn bs d (lam + (a.lvl : K) + (n' : K)) (D - a.lvl - n') 1 (j - 1) := by
      intro n' _
      rw [Nat.cast_add, add_assoc, Nat.sub_sub]
    rw [Finset.sum_congr rfl fun n' hn' => by rw [hW n' hn']]
    rw [← mul_assoc, mul_comm (j : K⸨X⸩), mul_assoc, hT]
    ring

end General

section Germ

variable {K : Type*} [Field K] [CharZero K]

/-- The link condition for the germ `b⋆ + t`: `δ_g - δ_{g'} = h_g + ℓ_g - h_{g'}` does not
vanish, since `(b⋆ + t)²` is not rational (Lemma 6.3). -/
theorem linkNe_germ (bs : K) : LinkNe bs := by
  intro g g' h1 h2 h3 h4 hw heq
  apply kacH_shift_ne (bGerm_ne_zero_all bs) (sqIrrational_bGerm bs) (g.1 : ℤ) (g.2 : ℤ)
    (g'.1 : ℤ) (g'.2 : ℤ)
    (by exact_mod_cast h1) (by exact_mod_cast h2) (by exact_mod_cast h3) (by exact_mod_cast h4)
  unfold delG deltaG hG at heq
  rw [hw] at heq
  have hC : (HahnSeries.C (kacHL g bs + (g.lvl : K)) : K⸨X⸩) =
      HahnSeries.C (kacHL g bs) + (g.lvl : K⸨X⸩) := by
    rw [map_add, map_natCast]
  rw [hC] at heq
  have hcast : (((g.1 : ℤ) * (g.2 : ℤ) : ℤ) : K⸨X⸩) = (g.lvl : K⸨X⸩) := by
    simp [Label.lvl]
  rw [hcast]
  unfold kacHL at heq
  linear_combination heq

end Germ

theorem pt_add_natCast (lam : ℂ) (n : ℕ) : pt (lam + (n : ℂ)) = pt lam + (n : Kd) := by
  rw [pt, pt, map_add, map_natCast]

/-- Lemma 7.10.

Paper label: lem:cutting -/
theorem lem_cutting : Stmt_lem_cutting := by
  intro b _hb lam D k j hD hk hj
  have h := chainFn_cut (bsC b) dvar (linkNe_germ (bsC b)) (pt lam) hD hk hj
  simp only [chainFnC]
  simp only [pt_add_natCast]
  exact h

end Virasoro
