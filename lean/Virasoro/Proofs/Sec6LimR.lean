import Virasoro.Proofs.Sec6LimRoot
import Virasoro.Proofs.Sec6ChainSlopes

/-!
# Proposition 6.7, the chain limit (a): `ℛ_g/t` at the germ (paper.tex l.1127–1135)

`ℛ_g(b,d) = E(b) · d · ∏_c (1 − d/c)` over the nonzero `d`-roots `c` of `𝒫_g`, with
`E(b) = 𝒜_g ∂_d𝒫_g|_{d=0} = −(ub² + v)/(2(b² + 1))` (`genA_mul_coeff_one`, the computation of
Lemma 6.5).  At `b = b⋆ + t`, `d = tY` this gives
`ℛ_g/t → E(b⋆) · Y · ∏_{j ∈ boxMults g} (1 − Y/(2b⋆ jκ₀))`, the limit of l.1134–1135 in the
coordinate `b` (the ν-derivative `jκ₀` times `dν/db = 2b⋆`).
-/

namespace Virasoro.ChainLim

open scoped LaurentSeries
open Finset

section Field

variable {F : Type} [Field F] [CharZero F]

/-- The two roots of the factor `(i,j)` of `𝒫`. -/
noncomputable def rt1 (b : F) (ij : ℕ × ℕ) : F :=
  phiL b (-(ij.1 : ℤ), -(ij.2 : ℤ)) * phiL b ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)

noncomputable def rt2 (b : F) (ij : ℕ × ℕ) : F :=
  phiL b (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * phiL b ((ij.1 : ℤ) + 1, -(ij.2 : ℤ))

/-- `ℛ_{u,v}(b,d) = E(b) · d · (1 − d/c₂(0,0)) ∏_{(i,j) ≠ (0,0)} (1 − d/c₁)(1 − d/c₂)`. -/
theorem genR_eq_roots (u v : ℕ) (hu : 0 < u) (hv : 0 < v) {b : F} (hb : b ≠ 0)
    (hb1 : b ^ 2 + 1 ≠ 0)
    (hA : (2 * ∏ pq ∈ genAIndex u v, ((pq.1 : F) * b + (pq.2 : F) * b⁻¹)) ≠ 0)
    (h00 : rt2 b (0, 0) ≠ 0)
    (hr : ∀ ij ∈ (range u ×ˢ range v).erase (0, 0), rt1 b ij ≠ 0 ∧ rt2 b ij ≠ 0) (d : F) :
    genR u v b d =
      -(((u : F) * b ^ 2 + (v : F)) / (2 * (b ^ 2 + 1))) * d *
        ((1 - d / rt2 b (0, 0)) *
          ∏ ij ∈ (range u ×ˢ range v).erase (0, 0), ((1 - d / rt1 b ij) * (1 - d / rt2 b ij))) := by
  have hmem : ((0 : ℕ), (0 : ℕ)) ∈ range u ×ˢ range v := by
    simp only [mem_product, mem_range]
    exact ⟨hu, hv⟩
  have hE := genA_mul_coeff_one u v hu hv hb hb1 hA
  obtain ⟨_, hc1⟩ := genPpoly_coeff u v hu hv b
  rw [← hE, hc1, genR, ← genPpoly_eval, genPpoly_eq, Polynomial.eval_prod,
    ← Finset.mul_prod_erase _ _ hmem]
  have e00 : phiL b (-((0 : ℕ) : ℤ), -((0 : ℕ) : ℤ)) = 0 := by simp [phiL]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, e00,
    zero_mul, zero_sub]
  have k : ∀ c : F, c ≠ 0 → c - d = c * (1 - d / c) := fun c hc => by field_simp
  have e1 : ∀ ij ∈ (range u ×ˢ range v).erase (0, 0),
      (phiL b (-(ij.1 : ℤ), -(ij.2 : ℤ)) * phiL b ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1) - d) *
          (phiL b (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * phiL b ((ij.1 : ℤ) + 1, -(ij.2 : ℤ)) - d) =
        tfun b ij * ((1 - d / rt1 b ij) * (1 - d / rt2 b ij)) := by
    intro ij hij
    obtain ⟨h1, h2⟩ := hr ij hij
    unfold rt1 at h1
    unfold rt2 at h2
    rw [k _ h1, k _ h2]
    unfold tfun rt1 rt2
    ring
  rw [prod_congr rfl e1, prod_mul_distrib]
  have h00' : phiL b (0, 1) * phiL b (1, 0) ≠ 0 := by
    have := h00
    unfold rt2 at this
    simpa using this
  have hrt : rt2 b (0, 0) = phiL b (0, 1) * phiL b (1, 0) := by
    unfold rt2
    simp
  simp only [Nat.cast_zero, neg_zero, zero_add]
  rw [hrt, k _ h00']
  ring

end Field

variable {K : Type} [Field K] [CharZero K]

theorem phiL_germ_ne {bs : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0)
    (hcop : Nat.Coprime p p') (hrel : (p : K) * bs ^ 2 + p' = 0) {x : ℤ × ℤ}
    (hx : x ≠ (0, 0)) : phiL (bGerm bs) x ≠ 0 := by
  have hp0 : p ≠ 0 := fun h0 => hp (by rw [h0]; simp)
  have hne0 : ∀ {u : K⸨X⸩} {v : K}, RegVal u v → v ≠ 0 → u ≠ 0 := by
    intro u v hu hv h0
    rw [h0] at hu
    exact hv (by simpa using hu.2.symm)
  by_cases hz : IsZ p p' x
  · obtain ⟨j, hj, rfl⟩ := hz.mult hp0 hcop
    have h1 := regVal_phiL_mult_div hbs hrel j
    have hv : 2 * (j : K) * (p : K) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast hj)) hp
    intro h0
    apply hne0 h1 hv
    rw [h0, zero_div]
  · exact hne0 (regVal_phiL hbs x) (phiL_star_ne hbs hp hrel (fun h => hz ⟨h, hx⟩))

/-- `ℛ_g/t` at the germ, with the product over the box `B_g`. -/
theorem regVal_genR_box {bs Y : K} (hbs : bs ≠ 0) {p p' : ℕ} (hp : (p : K) ≠ 0) (hne : p ≠ p')
    (hcop : Nat.Coprime p p') (hrel : (p : K) * bs ^ 2 + p' = 0) (hb1 : bs ^ 2 + 1 ≠ 0)
    (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    RegVal (genR u v (bGerm bs) (tX * HahnSeries.C Y) / tX)
      (-(((u : K) * bs ^ 2 + (v : K)) / (2 * (bs ^ 2 + 1))) * Y *
        ∏ x ∈ Icc (1 - (u : ℤ)) u ×ˢ Icc (1 - (v : ℤ)) v, wv p p' bs Y x) := by
  have hb := regVal_bGerm (K := K) bs
  have hbne := bGerm_ne_zero hbs
  have hb2 : RegVal (bGerm bs ^ 2 + 1) (bs ^ 2 + 1) := by
    have := (hb.pow 2).add (regVal_C (1 : K))
    simpa using this
  have hb2ne : bGerm bs ^ 2 + 1 ≠ 0 := by
    intro h0
    rw [h0] at hb2
    exact hb1 (by simpa using hb2.2.symm)
  have hA : (2 * ∏ pq ∈ genAIndex u v,
      ((pq.1 : K⸨X⸩) * bGerm bs + (pq.2 : K⸨X⸩) * (bGerm bs)⁻¹)) ≠ 0 := by
    refine mul_ne_zero two_ne_zero ?_
    rw [prod_ne_zero_iff]
    intro pq hpq
    have hpq0 : pq ≠ (0, 0) := (mem_filter.1 hpq).2.1
    exact phiL_germ_ne hbs hp hcop hrel hpq0
  have hroot := fun x hx0 hx1 => regVal_root (K := K) (Y := Y) hbs hp hne hcop hrel x hx0 hx1
  have h00 := hroot (0, 1) (by decide) (by decide)
  have e00 : rt2 (bGerm bs) (0, 0) = phiL (bGerm bs) (0, 1) * phiL (bGerm bs) (1 - 0, 1 - 1) := by
    unfold rt2
    norm_num
  have hrr : ∀ ij ∈ (range u ×ˢ range v).erase (0, 0),
      rt1 (bGerm bs) ij ≠ 0 ∧ rt2 (bGerm bs) ij ≠ 0 ∧
      RegVal (1 - tX * HahnSeries.C Y / rt1 (bGerm bs) ij)
        (wv p p' bs Y (-(ij.1 : ℤ), -(ij.2 : ℤ)) * wv p p' bs Y ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)) ∧
      RegVal (1 - tX * HahnSeries.C Y / rt2 (bGerm bs) ij)
        (wv p p' bs Y (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * wv p p' bs Y ((ij.1 : ℤ) + 1, -(ij.2 : ℤ))) := by
    intro ij hij
    have hij0 : ij ≠ (0, 0) := (mem_erase.1 hij).1
    have hx1 : ((-(ij.1 : ℤ), -(ij.2 : ℤ)) : ℤ × ℤ) ≠ (0, 0) := by
      intro h
      apply hij0
      rw [Prod.mk.injEq] at h
      exact Prod.ext (by omega) (by omega)
    have hx2 : ((-(ij.1 : ℤ), (ij.2 : ℤ) + 1) : ℤ × ℤ) ≠ (0, 0) := by
      intro h
      rw [Prod.mk.injEq] at h
      omega
    have r1 := hroot (-(ij.1 : ℤ), -(ij.2 : ℤ)) hx1 (by
      intro h
      rw [Prod.mk.injEq] at h
      omega)
    have r2 := hroot (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) hx2 (by
      intro h
      rw [Prod.mk.injEq] at h
      omega)
    have q1 : ((1 - -(ij.1 : ℤ), 1 - -(ij.2 : ℤ)) : ℤ × ℤ) = ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1) := by
      ext <;> simp <;> ring
    have q2 : ((1 - -(ij.1 : ℤ), 1 - ((ij.2 : ℤ) + 1)) : ℤ × ℤ) = ((ij.1 : ℤ) + 1, -(ij.2 : ℤ)) := by
      ext <;> simp <;> ring
    rw [q1] at r1
    rw [q2] at r2
    exact ⟨r1.1, r2.1, r1.2, r2.2⟩
  rw [genR_eq_roots u v hu hv hbne hb2ne hA (by rw [e00]; exact h00.1)
    (fun ij hij => ⟨(hrr ij hij).1, (hrr ij hij).2.1⟩)]
  have hY : RegVal (HahnSeries.C Y : K⸨X⸩) Y := regVal_C Y
  have hEv : RegVal (-(((u : K⸨X⸩) * bGerm bs ^ 2 + (v : K⸨X⸩)) / (2 * (bGerm bs ^ 2 + 1))))
      (-(((u : K) * bs ^ 2 + (v : K)) / (2 * (bs ^ 2 + 1)))) := by
    have := (((regVal_natCast u).mul (hb.pow 2)).add (regVal_natCast v)).div
      ((regVal_ofNat 2).mul hb2) (mul_ne_zero two_ne_zero hb1)
    have h' := (regVal_C (0 : K)).sub this
    simpa using h'
  have hP := RegVal.prod (s := (range u ×ˢ range v).erase (0, 0))
    (f := fun ij => (1 - tX * HahnSeries.C Y / rt1 (bGerm bs) ij) *
      (1 - tX * HahnSeries.C Y / rt2 (bGerm bs) ij))
    (v := fun ij => (wv p p' bs Y (-(ij.1 : ℤ), -(ij.2 : ℤ)) *
        wv p p' bs Y ((ij.1 : ℤ) + 1, (ij.2 : ℤ) + 1)) *
      (wv p p' bs Y (-(ij.1 : ℤ), (ij.2 : ℤ) + 1) * wv p p' bs Y ((ij.1 : ℤ) + 1, -(ij.2 : ℤ))))
    (fun ij hij => (hrr ij hij).2.2.1.mul (hrr ij hij).2.2.2)
  have h00v : RegVal (1 - tX * HahnSeries.C Y / rt2 (bGerm bs) (0, 0))
      (wv p p' bs Y (0, 1) * wv p p' bs Y (1, 0)) := by
    rw [e00]
    have := h00.2
    norm_num at this ⊢
    exact this
  have hall := ((hEv.mul hY).mul (h00v.mul hP))
  have e2 : -(((u : K⸨X⸩) * bGerm bs ^ 2 + (v : K⸨X⸩)) / (2 * (bGerm bs ^ 2 + 1))) *
        (tX * HahnSeries.C Y) *
        ((1 - tX * HahnSeries.C Y / rt2 (bGerm bs) (0, 0)) *
          ∏ ij ∈ (range u ×ˢ range v).erase (0, 0),
            ((1 - tX * HahnSeries.C Y / rt1 (bGerm bs) ij) *
              (1 - tX * HahnSeries.C Y / rt2 (bGerm bs) ij))) / tX =
      -(((u : K⸨X⸩) * bGerm bs ^ 2 + (v : K⸨X⸩)) / (2 * (bGerm bs ^ 2 + 1))) *
        HahnSeries.C Y *
        ((1 - tX * HahnSeries.C Y / rt2 (bGerm bs) (0, 0)) *
          ∏ ij ∈ (range u ×ˢ range v).erase (0, 0),
            ((1 - tX * HahnSeries.C Y / rt1 (bGerm bs) ij) *
              (1 - tX * HahnSeries.C Y / rt2 (bGerm bs) ij))) := by
    field_simp [tX_ne_zero]
  rw [e2]
  convert hall using 2
  -- the value: the product over the roots is the product over the box
  rw [prod_box (wv p p' bs Y) u v]
  have hmem : ((0 : ℕ), (0 : ℕ)) ∈ range u ×ˢ range v := by
    simp only [mem_product, mem_range]
    exact ⟨hu, hv⟩
  rw [← Finset.mul_prod_erase _ _ hmem]
  simp only [Nat.cast_zero, neg_zero, zero_add]
  rw [wv_zero, wv_one p p' hne]
  ring

end Virasoro.ChainLim
