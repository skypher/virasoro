import Virasoro.Proofs.Sec7Moments
import Virasoro.Proofs.Sec7Binom

/-!
# Lemma 7.11 (the remainder is regular)

The proof follows the paper.  The remainder `Reg^{(M)}_μ` is the sum of the collision groups at the
weights `λ' ≠ μ` (Proposition 6.4).  Its Taylor coefficients at `Δ = μ` are
`φ_j = ∑_{w_g ≠ μ} B_{g,M} (-1)^j j!/(μ - h_g)^{j+1}`; expanding
`(μ - h_g)^{-(j+1)} = ((μ - λ') - δ_g)^{-(j+1)}` in powers of `δ_g` writes every coefficient of
`t^m` as a finite combination of the coefficients of `t^m` of the full moments
`C_{λ',i+1,M}`, which vanish for `m < 0` (Lemma 7.8) and give `A⋆_{λ',i+1,M}` at `m = 0`.  The
same expansion gives the Taylor coefficients at `μ` of the principal parts of `H_M(c⋆,·)` at the
other weights, which proves (7.6).
-/

namespace Virasoro

open scoped LaurentSeries

section Local

variable {K : Type*} [Field K]

/-- The Taylor coefficients at `μ` of a simple fraction with its pole at `a ≠ μ`:
`[(Δ-μ)^j] c/(Δ-a)^k = c (-1)^j C(k-1+j, k-1)/(μ-a)^{j+k}`. -/
theorem lcoeff_pole_other {a μ : K} (h : μ ≠ a) (c : K) {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    lcoeff (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k) μ j =
      c * ((-1) ^ j * ((((k - 1) + j).choose (k - 1) : ℕ) : K) / (μ - a) ^ (j + (k - 1) + 1)) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hy : OrdGE (HahnSeries.single (1 : ℤ) (-1 : K)) 1 := by
    refine ordGE_iff.2 fun m hm => ?_
    rw [HahnSeries.coeff_single_of_ne (by omega)]
  have hexp : expandHom μ (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ (k' + 1)) =
      HahnSeries.C c * (HahnSeries.C (μ - a) - HahnSeries.single (1 : ℤ) (-1 : K))⁻¹ ^ (k' + 1) := by
    rw [map_div₀, map_pow, map_sub, expandHom_X, expandHom_C, expandHom_C, div_eq_mul_inv,
      ← inv_pow]
    congr 3
    rw [HahnSeries.single_neg, map_sub]
    ring
  unfold lcoeff
  rw [expandAt_eq, hexp, coeff_mul_inv_pow (sub_ne_zero.2 h) hy (ordGE_C c) k' (j + 1)
    (by push_cast; omega)]
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (((k' + i).choose k' : ℕ) : K) / (μ - a) ^ (i + k' + 1) *
        (HahnSeries.C c * HahnSeries.single (1 : ℤ) (-1 : K) ^ i).coeff (j : ℤ) =
      if i = j then c * ((-1) ^ j * (((k' + j).choose k' : ℕ) : K) / (μ - a) ^ (j + k' + 1))
        else 0 := by
    intro i _
    rw [HahnSeries.single_pow, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
      HahnSeries.coeff_single]
    by_cases hij : i = j
    · subst hij
      simp only [nsmul_eq_mul, mul_one, if_true]
      ring
    · rw [if_neg hij, if_neg]
      · ring
      · intro h'
        apply hij
        have : (j : ℤ) = (i : ℤ) := by simpa using h'
        exact_mod_cast this.symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (j + 1)) j,
    if_pos (Finset.self_mem_range_succ j)]

/-- The Taylor coefficients at `a` of a simple fraction with its pole at `a` vanish. -/
theorem lcoeff_pole_same (a c : K) {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    lcoeff (RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ k) a j = 0 := by
  unfold lcoeff
  rw [expandAt_eq, expandHom_pole_same, HahnSeries.coeff_single_of_ne (by omega)]

end Local

section General

variable {K : Type} [Field K] [CharZero K]

/-- One term of `φ_j`, expanded in powers of `δ_g`. -/
theorem phiTerm_coeff {bs : K} (hbs : bs ≠ 0) (d : K) (M : ℕ) {mu : K} {g : Label}
    (hw : kacHL g bs ≠ mu) (j n : ℕ) {m : ℤ} (hm : m < -((vhat bs d M g : ℕ) : ℤ) + n) :
    (BG bs d M g * ((-1 : K⸨X⸩) ^ j * (j.factorial : K⸨X⸩)) /
        (HahnSeries.C mu - hG bs g) ^ (j + 1)).coeff m =
      ∑ i ∈ Finset.range n, ((-1) ^ j * (j.factorial : K)) *
        ((((j + i).choose j : ℕ) : K) / (mu - kacHL g bs) ^ (i + j + 1)) *
          (BG bs d M g * deltaG bs (kacHL g bs) g ^ i).coeff m := by
  have hsplit : HahnSeries.C mu - hG bs g =
      HahnSeries.C (mu - kacHL g bs) - deltaG bs (kacHL g bs) g := by
    rw [deltaG, map_sub]; ring
  have hc : ((-1 : K⸨X⸩) ^ j * (j.factorial : K⸨X⸩)) =
      HahnSeries.C ((-1) ^ j * (j.factorial : K)) := by
    rw [map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [hsplit, hc, div_eq_mul_inv, ← inv_pow, mul_comm (BG bs d M g), mul_assoc,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul,
    coeff_mul_inv_pow (sub_ne_zero.2 hw.symm) (ordGE_deltaG_one hbs g) (ordGE_BG bs d M g) j n hm,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

open Classical in
/-- The coefficient of `t^m` of `φ_j`, grouped by the weights `λ' ≠ μ`: a finite combination of
the coefficients of `t^m` of the full moments `C_{λ',i+1,M}`. -/
theorem phiRem_coeff {bs : K} (hbs : bs ≠ 0) (d : K) (M : ℕ) (mu : K) (j n : ℕ) {m : ℤ}
    (hm : ∀ g ∈ labels M, m < -((vhat bs d M g : ℕ) : ℤ) + n) :
    (phiRem bs d M mu j).coeff m =
      ∑ w ∈ (Lam M bs).filter (fun w => w ≠ mu), ∑ i ∈ Finset.range n,
        ((-1) ^ j * (j.factorial : K)) * ((((j + i).choose j : ℕ) : K) / (mu - w) ^ (i + j + 1)) *
          (∑ g ∈ collClass M bs w, BG bs d M g * deltaG bs w g ^ i).coeff m := by
  unfold phiRem
  rw [HahnSeries.coeff_sum]
  rw [Finset.sum_congr rfl fun g hg => phiTerm_coeff hbs d M
    (Finset.mem_filter.1 hg).2 j n (hm g (Finset.mem_filter.1 hg).1)]
  have hmaps : ∀ g ∈ (labels M).filter (fun g => kacHL g bs ≠ mu),
      kacHL g bs ∈ (Lam M bs).filter (fun w => w ≠ mu) := by
    intro g hg
    obtain ⟨hgl, hgw⟩ := Finset.mem_filter.1 hg
    exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hgl, hgw⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w hw => ?_
  have hwmu : w ≠ mu := (Finset.mem_filter.1 hw).2
  have hfib : ((labels M).filter (fun g => kacHL g bs ≠ mu)).filter (fun g => kacHL g bs = w) =
      collClass M bs w := by
    ext g
    simp only [Finset.mem_filter, mem_collClass]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by rw [h3]; exact hwmu⟩, h3⟩
  rw [hfib]
  have hrw : ∀ g ∈ collClass M bs w, ∀ i,
      ((-1) ^ j * (j.factorial : K)) *
        ((((j + i).choose j : ℕ) : K) / (mu - kacHL g bs) ^ (i + j + 1)) *
          (BG bs d M g * deltaG bs (kacHL g bs) g ^ i).coeff m =
      ((-1) ^ j * (j.factorial : K)) * ((((j + i).choose j : ℕ) : K) / (mu - w) ^ (i + j + 1)) *
          (BG bs d M g * deltaG bs w g ^ i).coeff m := by
    intro g hg i
    rw [(mem_collClass.1 hg).2]
  rw [Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun i _ => hrw g hg i,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [HahnSeries.coeff_sum, Finset.mul_sum]

open Classical in
/-- Lemma 7.11 over an arbitrary coefficient field: the Taylor coefficients `φ_j` of the
remainder are regular at `t = 0`, with value `j!` times the coefficient of `(Δ - μ)^j` of
`H_M(c⋆,·)`. -/
theorem phiRem_regular {bs : K} (hbs : bs ≠ 0) (d : K) {M : ℕ} (hM : 1 ≤ M)
    (hrec : ∀ M', 1 ≤ M' → M' ≤ M →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M')
    (mu : K) (j : ℕ) :
    OrdGE (phiRem bs d M mu j) 0 ∧
      (phiRem bs d M mu j).coeff 0 = (j.factorial : K) * lcoeff (Hrat (kacC bs) d M) mu j := by
  set n : ℕ := (labels M).sup (fun g => vhat bs d M g) +
    (Lam M bs).sup (fun w => Mhat bs d M w) + 1 with hn
  have hvn : ∀ g ∈ labels M, vhat bs d M g < n := by
    intro g hg
    have := Finset.le_sup (f := fun g => vhat bs d M g) hg
    omega
  have hMn : ∀ w ∈ Lam M bs, Mhat bs d M w < n := by
    intro w hw
    have := Finset.le_sup (f := fun w => Mhat bs d M w) hw
    omega
  have hm : ∀ m : ℤ, m ≤ 0 → ∀ g ∈ labels M, m < -((vhat bs d M g : ℕ) : ℤ) + n := by
    intro m hm0 g hg
    have : ((vhat bs d M g : ℕ) : ℤ) < (n : ℤ) := by exact_mod_cast hvn g hg
    omega
  refine ⟨ordGE_iff.2 fun m hm0 => ?_, ?_⟩
  · rw [phiRem_coeff hbs d M mu j n (hm m hm0.le)]
    refine Finset.sum_eq_zero fun w hw => Finset.sum_eq_zero fun i _ => ?_
    have hwL : w ∈ Lam M bs := (Finset.mem_filter.1 hw).1
    have h0 := moment_coeff_neg hbs d hM hrec hwL (k := i + 1) (by omega) hm0
    rw [Nat.add_sub_cancel] at h0
    rw [h0, mul_zero]
  · rw [phiRem_coeff hbs d M mu j n (hm 0 le_rfl), confluence_identity hbs d hM hrec,
      lcoeff_sum, Finset.mul_sum]
    -- the weight `μ` itself contributes nothing
    have hsame : ∀ w ∈ Lam M bs, w = mu →
        (j.factorial : K) * lcoeff (∑ k ∈ Finset.Icc 1 (Mhat bs d M w),
          RatFunc.C (Atilde bs d M w k) / (RatFunc.X - RatFunc.C w) ^ k) mu j = 0 := by
      intro w _ hw
      rw [lcoeff_sum, Finset.sum_eq_zero, mul_zero]
      intro k hk
      rw [hw]
      exact lcoeff_pole_same mu _ (Finset.mem_Icc.1 hk).1 j
    rw [← Finset.sum_filter_add_sum_filter_not (Lam M bs) (fun w => w ≠ mu)]
    rw [Finset.sum_eq_zero (s := (Lam M bs).filter (fun w => ¬ w ≠ mu)) (fun w hw => by
      obtain ⟨hwL, hw'⟩ := Finset.mem_filter.1 hw
      exact hsame w hwL (not_not.1 hw')), add_zero]
    refine Finset.sum_congr rfl fun w hw => ?_
    obtain ⟨hwL, hwmu⟩ := Finset.mem_filter.1 hw
    -- both sides as a sum over `k = i + 1 ≤ n`
    rw [lcoeff_sum, Finset.mul_sum]
    set F : ℕ → K := fun k => (j.factorial : K) * (Atilde bs d M w k *
      ((-1) ^ j * ((((k - 1) + j).choose (k - 1) : ℕ) : K) / (mu - w) ^ (j + (k - 1) + 1)))
      with hF
    have hR : ∀ k ∈ Finset.Icc 1 (Mhat bs d M w),
        (j.factorial : K) *
          lcoeff (RatFunc.C (Atilde bs d M w k) / (RatFunc.X - RatFunc.C w) ^ k) mu j = F k := by
      intro k hk
      rw [hF, lcoeff_pole_other hwmu.symm _ (Finset.mem_Icc.1 hk).1 j]
    rw [Finset.sum_congr rfl hR, ← sum_range_succ_eq_Icc F]
    have hext : ∑ i ∈ Finset.range (Mhat bs d M w), F (i + 1) =
        ∑ i ∈ Finset.range n, F (i + 1) := by
      apply Finset.sum_subset
      · intro i hi
        simp only [Finset.mem_range] at hi ⊢
        have := hMn w hwL
        omega
      · intro i _ hi
        simp only [Finset.mem_range, not_lt] at hi
        rw [hF]
        dsimp only
        rw [Atilde_eq_zero hbs d M w (by omega), zero_mul, mul_zero]
    rw [hext]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hA : (∑ g ∈ collClass M bs w, BG bs d M g * deltaG bs w g ^ i).coeff 0 =
        Atilde bs d M w (i + 1) := by
      unfold Atilde
      rw [Nat.add_sub_cancel]
    have hc : (((j + i).choose j : ℕ) : K) = (((i + j).choose i : ℕ) : K) := by
      rw [Nat.choose_symm_add, Nat.add_comm]
    have he : (mu - w) ^ (i + j + 1) = (mu - w) ^ (j + i + 1) := by
      rw [Nat.add_comm i j]
    rw [hA, hF]
    dsimp only
    rw [Nat.add_sub_cancel, hc, he]
    ring

end General

/-- `H_M(c(b), Δ, d) = ∑_{ℓ_g ≤ M} B_{g,M}/(Δ - h_g)` over the field of germs (Proposition 6.4 with
Lemma 7.8). -/
theorem HgermC_eq (hrec : GenericRecursionUniform) {b : ℂ} (hb : b ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    HgermC b M = ∑ g ∈ labels M,
      RatFunc.C (BG (bsC b) dvar M g) / (RatFunc.X - RatFunc.C (hG (bsC b) g)) := by
  have hbs : bsC b ≠ 0 := by simpa [bsC] using hb
  have h := germ_recursion_self hrec (bsC b) dvar M hM
  unfold GenericRecursionAt at h
  unfold HgermC
  rw [h]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hg' := hg
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hg'
  have hS := SG_eq_evalAt hrec hbs dvar (M - g.lvl) g hg'.1.1.1 hg'.1.2.1
  rw [BG, RG, hS, zG, hG, map_mul]
  ring

open Classical in
/-- The first assertion in the proof of Lemma 7.11: `Reg^{(M)}_μ` is the sum of the collision
groups at the weights `λ' ≠ μ`. -/
theorem regC_eq (hrec : GenericRecursionUniform) {b : ℂ} (hb : b ≠ 0) {M : ℕ} (hM : 1 ≤ M)
    (mu : ℂ) :
    regC b M mu = ∑ g ∈ (labels M).filter (fun g => kacHL g b ≠ mu),
      RatFunc.C (BG (bsC b) dvar M g) / (RatFunc.X - RatFunc.C (hG (bsC b) g)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (labels M) (fun g => kacHL g b = mu)
    (fun g => RatFunc.C (BG (bsC b) dvar M g) / (RatFunc.X - RatFunc.C (hG (bsC b) g)))
  have hcc : collClass M b mu = (labels M).filter (fun g => kacHL g b = mu) := by
    ext g
    simp [mem_collClass]
  have hne : (labels M).filter (fun g => ¬ kacHL g b = mu) =
      (labels M).filter (fun g => kacHL g b ≠ mu) := by
    ext g
    simp
  unfold regC groupC
  rw [HgermC_eq hrec hb M hM, ← hsplit, hcc, hne]
  ring

open Classical in
/-- `φ^{(M)}_{μ,j} = j! [(Δ-μ)^j] Reg^{(M)}_μ`, the Laurent coefficient at the point `μ` of the
`Δ`-line over the field of germs. -/
theorem phiRemC_eq_lcoeff (hrec : GenericRecursionUniform) {b : ℂ} (hb : b ≠ 0) {M : ℕ}
    (hM : 1 ≤ M) (mu : ℂ) (j : ℕ) :
    phiRemC b M mu j = (j.factorial : Kd⸨X⸩) * lcoeff (regC b M mu) (HahnSeries.C (pt mu)) j := by
  have hbs : bsC b ≠ 0 := by simpa [bsC] using hb
  rw [regC_eq hrec hb hM mu, lcoeff_sum, Finset.mul_sum]
  unfold phiRemC phiRem
  have hfil : (labels M).filter (fun g => kacHL g (bsC b) ≠ pt mu) =
      (labels M).filter (fun g => kacHL g b ≠ mu) := by
    ext g
    simp only [Finset.mem_filter, bsC, kacHL_ratC, pt]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 (by rw [h])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h => h2 (RatFunc.C_injective h)⟩
  rw [hfil]
  refine Finset.sum_congr rfl fun g hg => ?_
  have hw : kacHL g b ≠ mu := (Finset.mem_filter.1 hg).2
  have hne : HahnSeries.C (pt mu) ≠ hG (bsC b) g := by
    intro h
    have h0 : (HahnSeries.C (pt mu) : Kd⸨X⸩).coeff 0 = (hG (bsC b) g).coeff 0 := by rw [h]
    rw [(regVal_C (pt mu)).2, (regVal_hG hbs g).2, bsC, kacHL_ratC] at h0
    exact hw (RatFunc.C_injective h0).symm
  rw [← pow_one (RatFunc.X - RatFunc.C (hG (bsC b) g)), lcoeff_pole_other hne _ (le_refl 1) j]
  simp only [Nat.sub_self, zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero]
  ring

end Virasoro
