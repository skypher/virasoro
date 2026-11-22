import Virasoro.Proofs.Sec6LimGr6

/-!
# Proposition 6.7, the chain limit (b): the transfer from `S = 1` (paper.tex l.1141–1146)

Along the germ `(b⋆ + t, λ + 2b⋆w t, 2b⋆y t)` the germ computation (`germ_chain`) gives
`H_N = P/D` regular with value the chain sum, and `D = t^e V` with `V(0) ≠ 0` (`kac_germ`).  So the
coefficients `P_i = [t^i] P` of the graded numerator satisfy `P_i(1, 2b⋆w, 2b⋆y) = 0` for `i < e`
and `P_e(1, 2b⋆w, 2b⋆y) = T · D_e(1, 2b⋆w)` with `T` the chain sum.
-/

namespace Virasoro.ChainLim

open Finset PowerSeries
open scoped LaurentSeries

variable {K : Type} [Field K] [CharZero K]

theorem coeff_tX_pow_mul (e : ℕ) (U : K⸨X⸩) (n : ℤ) : (tX ^ e * U).coeff n = U.coeff (n - e) := by
  rw [tX, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
  have := HahnSeries.coeff_single_mul_add (r := (1 : K)) (x := U) (a := n - e) (b := (e : ℤ))
  rw [one_mul, sub_add_cancel] at this
  exact this

variable [Algebra ℂ K]

/-- The transfer (paper.tex l.1141–1146), on the line `S = 1`. -/
theorem transfer (hrec : GenericRecursionUniform) (hK : Cited_KacDeterminant) {p p' r s : ℕ}
    (hp0 : 0 < p) (hp'0 : 0 < p') (hne : p ≠ p') (hcop : Nat.Coprime p p') {bs : ℂ}
    (hbs : bs ≠ 0) (hrel : (p : ℂ) * bs ^ 2 + p' = 0) (hb1 : bs ^ 2 + 1 ≠ 0) {w : K}
    (hw : ∀ z : ℂ, w ≠ algebraMap ℂ K z) (y : K) (N : ℕ) :
    (∀ i < eRes bs (kacH r s bs) N,
        ev1 bs w y (coeff i (NumG bs (kacH r s bs) N)) = 0) ∧
      ev1 bs w y (coeff (eRes bs (kacH r s bs) N) (DenG bs (kacH r s bs) N)) ≠ 0 ∧
      ev1 bs w y (coeff (eRes bs (kacH r s bs) N) (NumG bs (kacH r s bs) N)) =
        chainK p p' (algebraMap ℂ K bs) (2 * algebraMap ℂ K bs * y) N N
            (((p' : ℤ) * r - (p : ℤ) * s) ^ 2) (2 * algebraMap ℂ K bs * w) *
          ev1 bs w y (coeff (eRes bs (kacH r s bs) N) (DenG bs (kacH r s bs) N)) := by
  set lam := kacH r s bs with hlam
  set e := eRes bs lam N with he
  set bK := algebraMap ℂ K bs with hbK
  have hbK0 : bK ≠ 0 := (_root_.map_ne_zero _).2 hbs
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp' : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpK : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'K : (p' : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hne'K : (p' : K) - p ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => hne (Nat.cast_injective h).symm
  have hrelK : (p : K) * bK ^ 2 + p' = 0 := by
    have := congrArg (algebraMap ℂ K) hrel
    simpa [hbK] using this
  have hb1K : bK ^ 2 + 1 ≠ 0 := by
    have : algebraMap ℂ K (bs ^ 2 + 1) ≠ 0 := (_root_.map_ne_zero _).2 hb1
    simpa [hbK] using this
  -- the germ
  set Z : K⸨X⸩ := HahnSeries.C (algebraMap ℂ K lam) + tX * HahnSeries.C (2 * bK * w) with hZ
  set m2 : ℤ := ((p' : ℤ) * r - (p : ℤ) * s) ^ 2 with hm2
  have hlamK : algebraMap ℂ K lam = wtK p p' m2 := by
    rw [hlam, map_kacH]
    exact kacHL_star (K := K) hbK0 hpK hp'K hrelK (r, s)
  have hX0 : RegVal (tX : K⸨X⸩) 0 := ⟨ordGE_single_one, by simp [tX]⟩
  have hZr : RegVal Z (wtK p p' m2) := by
    have := (regVal_C (algebraMap ℂ K lam)).add (hX0.mul (regVal_C (2 * bK * w)))
    rw [zero_mul, add_zero] at this
    rw [← hlamK]
    exact this
  have hZs : RegVal ((Z - HahnSeries.C (wtK p p' m2)) / tX) (2 * bK * w) := by
    have e1 : (Z - HahnSeries.C (wtK p p' m2)) / tX = HahnSeries.C (2 * bK * w) := by
      rw [hZ, ← hlamK, add_sub_cancel_left, mul_div_cancel_left₀ _ tX_ne_zero]
    rw [e1]
    exact regVal_C _
  have hsl : ∀ g ∈ labels N, ((p' : ℤ) * g.1 - (p : ℤ) * g.2) ^ 2 = m2 →
      2 * bK * w ≠ 2 * bK * hdotK p p' g := by
    intro g _ _ h
    have h2 : (2 * bK) ≠ 0 := mul_ne_zero two_ne_zero hbK0
    have := mul_left_cancel₀ h2 h
    rw [hdotK_map] at this
    exact hw _ this
  have hG := germ_chain (Y := 2 * bK * y) hrec hbK0 hpK hp'K hp0 hp'0 hne hne'K hcop hrelK hb1K
    N N le_rfl m2 Z (2 * bK * w) hZr hZs hsl
  -- the denominator along the germ
  obtain ⟨V, v, hv0, hV, hDen0⟩ := kac_germ hK hp hp' hbs hrel hw lam N
  have hDen : denH (kacC (bGerm bK)) Z N = tX ^ e * V := hDen0
  have hVne : V ≠ 0 := regVal_ne_zero hV hv0
  have hDne : denH (kacC (bGerm bK)) Z N ≠ 0 := by
    rw [hDen]
    exact mul_ne_zero (pow_ne_zero _ tX_ne_zero) hVne
  have hdet : ∀ M ≤ N, (gram (kacC (bGerm bK)) Z M).det ≠ 0 := by
    intro M hM
    have := prod_ne_zero_iff.1 hDne M (mem_range.2 (Nat.lt_succ_of_le hM))
    exact this
  rw [evalAt_Hrat hdet, Hval_eq_numH hdet] at hG
  -- the images of the graded numerator and denominator
  have hNum : sig1 bs w y (NumG bs lam N) =
      numH (kacC (bGerm bK)) Z (tX * HahnSeries.C (2 * bK * y)) N := by
    rw [NumG, map_numH, sig1_cR w y hbs, sig1_DR, sig1_dR]
  have hDenS : sig1 bs w y (DenG bs lam N) = denH (kacC (bGerm bK)) Z N := by
    rw [DenG, map_denH, sig1_cR w y hbs, sig1_DR]
  set T := chainK p p' bK (2 * bK * y) N N m2 (2 * bK * w) with hT
  set R := numH (kacC (bGerm bK)) Z (tX * HahnSeries.C (2 * bK * y)) N /
    denH (kacC (bGerm bK)) Z N with hR
  have hNumR : sig1 bs w y (NumG bs lam N) = tX ^ e * (R * V) := by
    have h1 : numH (kacC (bGerm bK)) Z (tX * HahnSeries.C (2 * bK * y)) N =
        R * denH (kacC (bGerm bK)) Z N := by
      rw [hR, div_mul_cancel₀ _ hDne]
    rw [hNum, h1, hDen]
    ring
  have hRV : RegVal (R * V) (T * v) := hG.mul hV
  have cN : ∀ i : ℕ, ev1 bs w y (coeff i (NumG bs lam N)) = (R * V).coeff ((i : ℤ) - e) := by
    intro i
    rw [← coeff_sig1, hNumR, coeff_tX_pow_mul]
  have cD : ev1 bs w y (coeff e (DenG bs lam N)) = v := by
    rw [← coeff_sig1, hDenS, hDen, coeff_tX_pow_mul, sub_self]
    exact hV.2
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · rw [cN]
    exact hRV.1.coeff_eq_zero (by omega)
  · rw [cD]
    exact hv0
  · rw [cN, cD, sub_self]
    exact hRV.2

end Virasoro.ChainLim
