import Virasoro.Proofs.Sec8DiagLambda
import Virasoro.Proofs.Sec6TauFactor
import Virasoro.Proofs.Germs

/-!
# Corollary 8.9 (`cor:diagonal-lambda`)

The values on the diagonal at `λ` are Theorem 8.8 with `a = λ` and `Top(λ → μ^±_L) = 𝒩^±_L/γ^±_L`.
For `L = 2`, Lemma 8.3(ii) gives the labels `(r,s)` from `λ` to `μ^+_1` and `(p±r, p'∓s)` from
`μ^+_1` to `μ^±_2`, both with regular residues (Lemma 8.4 with `Δ = 1`), and Proposition 8.6 with
`θ = μ^+_1` (`κ̂ = ∓1`, `κ = ∓n₁/n₀`) gives `Top(λ → μ^±_2) = ∓(n₀/n₁) R_{r,s}(b⋆) R_{p±r,p'∓s}(b⋆)`.
With `R_g = 𝒜_g 𝒩_g` and `𝒩^±_2 = 𝒩_{r,s} 𝒩_{p±r,p'∓s}`, cancelling the nonzero polynomials in `d`
gives `γ^±_2`.
-/

namespace Virasoro

open scoped LaurentSeries Polynomial

variable {p p' r s : ℕ} {b : ℂ}

theorem regVal_genA_of {bs : Kd} (hbs : bs ≠ 0) {u v : ℕ}
    (hfac : ∀ pq ∈ genAIndex u v, (pq.1 : Kd) * bs + (pq.2 : Kd) * bs⁻¹ ≠ 0) :
    RegVal (genA u v (bGerm bs)) (genA u v bs) := by
  have hb := regVal_bGerm bs
  have hbi := hb.inv hbs
  unfold genA
  refine ((regVal_ofNat 2).inv (by norm_num)).mul (RegVal.prod fun pq hpq => ?_)
  exact (((regVal_intCast pq.1).mul hb).add ((regVal_intCast pq.2).mul hbi)).inv (hfac pq hpq)

theorem genA_ne_of {u v : ℕ} (hfac : ∀ pq ∈ genAIndex u v, (pq.1 : ℂ) * b + (pq.2 : ℂ) * b⁻¹ ≠ 0) :
    genA u v b ≠ 0 := by
  unfold genA
  exact mul_ne_zero (inv_ne_zero two_ne_zero)
    (Finset.prod_ne_zero_iff.2 fun pq h => inv_ne_zero (hfac pq h))

section OneLabel

variable (hset : MinimalSetting p p' r s b)
include hset

/-- For a label of `Δ = 1` no factor of `𝒜` vanishes at `b⋆`. -/
theorem fac_ne_one {ν ν' : Node} (hlt : ν.2 < ν'.2) (hΔ : ν'.2 - ν.2 = 1) :
    ∀ pq ∈ genAIndex (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2,
      (pq.1 : ℂ) * b + (pq.2 : ℂ) * b⁻¹ ≠ 0 := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb := hset.2.2.2.2.2.2.2.2
  have hcount := line_count hset hlt (by omega)
  rw [hΔ] at hcount
  intro pq hpq e
  have hline := (Afac_zero_iff hp hp' hb pq.1 pq.2).1 e
  have hmem : pq ∈ (genAIndex (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2).filter
      (fun pq => (p : ℤ) * pq.2 = p' * pq.1) := Finset.mem_filter.2 ⟨hpq, hline⟩
  have hz : ((genAIndex (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2).filter
      (fun pq => (p : ℤ) * pq.2 = p' * pq.1)).card = 0 := by omega
  rw [Finset.card_eq_zero.1 hz] at hmem
  simp at hmem

/-- The residue of a label with `Δ = 1` at `b⋆`: `R_g(b⋆) = 𝒜_g(b⋆) 𝒩_g(b⋆, d)`. -/
theorem rho_one_label {ν ν' : Node} (hlt : ν.2 < ν'.2) (hΔ : ν'.2 - ν.2 = 1) :
    nodeRho p p' r s b ν ν' =
      RatFunc.C (genA (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2 b) *
        algebraMap ℂ[X] Kd (genPpoly (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2 b) := by
  have hb0 := b_ne_zero_of hset
  have hbs : (bsC b : Kd) ≠ 0 := by simpa [bsC] using hb0
  have hfacC := fac_ne_one hset hlt hΔ
  have hfac : ∀ pq ∈ genAIndex (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2,
      (pq.1 : Kd) * bsC b + (pq.2 : Kd) * (bsC b)⁻¹ ≠ 0 := by
    intro pq hpq e
    apply hfacC pq hpq
    apply RatFunc.C_injective
    rw [map_zero, ← e]
    simp [bsC, map_add, map_mul, map_inv₀, map_intCast]
  have hR := (regVal_genA_of hbs hfac).mul (regVal_genP hbs dvar
    (nodeLabel p p' r s ν ν').1 (nodeLabel p p' r s ν ν').2)
  unfold nodeRho nodeR RG genR
  rw [show (1 : ℤ) - ((ν'.2 : ℤ) - ν.2) = 0 by omega, hR.2, genP_Kd_poly]
  congr 1
  exact (map_genA RatFunc.C _ _ b).symm

theorem nodeLabel_eq_of {ν ν' : Node} (hlt : ν.2 < ν'.2) (hodd : (ν'.2 - ν.2) % 2 = 1)
    (g : Label) (h1 : 0 < g.1) (h2 : 0 < g.2)
    (hw : ((p' : ℤ) * g.1 - p * g.2) ^ 2 = nodeS p p' r s ν ^ 2)
    (hw' : ((p' : ℤ) * g.1 + p * g.2) ^ 2 = nodeS p p' r s ν' ^ 2) :
    g = nodeLabel p p' r s ν ν' := by
  have hp : 0 < p := by have := hset.1; omega
  have hp' : 0 < p' := by have := hset.2.1; omega
  have hb := hset.2.2.2.2.2.2.2.2
  refine ((node_labels_ii hset ν ν' hlt hodd).1 g h1 h2).1 ⟨?_, ?_⟩
  · rw [kacHL_eq_momWt hp hp' hb, nodeWt_eq]
    exact (momWt_eq_iff hp hp' _ _).2 hw
  · rw [kacH_add_lvl hp hp' hb, nodeWt_eq]
    exact (momWt_eq_iff hp hp' _ _).2 hw'

theorem lab1 : nodeLabel p p' r s (true, 0) (true, 1) = (r, s) := by
  have hr := hset.2.2.2.1
  have hs := hset.2.2.2.2.2.1
  refine (nodeLabel_eq_of hset (show (true, 0).2 < (true, 1).2 by simp)
    (by show (1 - 0) % 2 = 1; omega) (r, s) hr hs ?_ ?_).symm
  · simp [nodeS, nOrb]
  · simp [nodeS, nOrb]

theorem lab2 (ε : Bool) : nodeLabel p p' r s (true, 1) (ε, 2) =
    (if ε then p + r else p - r, if ε then p' - s else p' + s) := by
  have hr := hset.2.2.2.1
  have hrp := hset.2.2.2.2.1
  have hs := hset.2.2.2.2.2.1
  have hsp := hset.2.2.2.2.2.2.1
  refine (nodeLabel_eq_of hset (show (true, 1).2 < (ε, 2).2 by simp)
    (by show (2 - 1) % 2 = 1; omega) _ (by cases ε <;> simp <;> omega)
    (by cases ε <;> simp <;> omega) ?_ ?_).symm
  · cases ε
    · simp only [Bool.false_eq_true, ↓reduceIte, nodeS, nOrb]
      push_cast [Nat.cast_sub hrp.le]
      norm_num
      ring
    · simp only [↓reduceIte, nodeS, nOrb]
      push_cast [Nat.cast_sub hsp.le]
      norm_num
      ring
  · cases ε
    · simp only [Bool.false_eq_true, ↓reduceIte, nodeS, nOrb]
      push_cast [Nat.cast_sub hrp.le]
      norm_num
      ring
    · simp only [↓reduceIte, nodeS, nOrb]
      push_cast [Nat.cast_sub hsp.le]
      norm_num
      ring

end OneLabel

theorem fs_01 : (firstSteps (true, 0) (true, 1)).erase (true, 1) = ∅ := by decide

theorem fs_12 (ε : Bool) : (firstSteps (true, 1) (ε, 2)).erase (ε, 2) = ∅ := by
  cases ε <;> decide

theorem topFac_val (ε : Bool) :
    topFac p p' r s (true, 0) (true, 1) (ε, 2) =
      ((((p' : ℤ) * r + p * s : ℤ) : ℚ) / (((p' : ℤ) * r - p * s : ℤ) : ℚ)) *
        (if ε then -1 else 1) := by
  unfold topFac kappaHat
  cases ε
  · rw [show firstSteps (true, 1) (false, 2) = {(false, 2)} by decide,
      show firstSteps (true, 0) (false, 2) \ firstSteps (true, 0) (true, 1) = {(false, 1)} by decide]
    simp [nodePos, nodeS, nOrb]
    norm_num
  · rw [show firstSteps (true, 1) (true, 2) = {(true, 2)} by decide,
      show firstSteps (true, 0) (true, 2) \ firstSteps (true, 0) (true, 1) = {(false, 1)} by decide]
    simp [nodePos, nodeS, nOrb]
    norm_num

theorem gamma_alg {A1 A2 q γ : ℂ} {P1 P2 : ℂ[X]} (hA : A1 * A2 ≠ 0)
    (hP : algebraMap ℂ[X] Kd P1 * algebraMap ℂ[X] Kd P2 ≠ 0)
    (hid : RatFunc.C A1 * algebraMap ℂ[X] Kd P1 * (RatFunc.C A2 * algebraMap ℂ[X] Kd P2) =
      RatFunc.C q * (algebraMap ℂ[X] Kd (P1 * P2) * RatFunc.C γ⁻¹)) : γ = q / (A1 * A2) := by
  rw [map_mul] at hid
  have e : (RatFunc.C (A1 * A2) - RatFunc.C (q * γ⁻¹)) *
      (algebraMap ℂ[X] Kd P1 * algebraMap ℂ[X] Kd P2) = 0 := by
    rw [map_mul, map_mul]
    linear_combination hid
  have e2 := RatFunc.C_injective (sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hP))
  have hγ : γ ≠ 0 := by
    intro h0; rw [h0, inv_zero, mul_zero] at e2; exact hA e2
  rw [eq_div_iff hA, e2]
  field_simp

/-- `Top(λ → μ^ε_L) = 𝒩^ε_L/γ^ε_L` with the coordinates of `w^ε_L` indexed by `ℓ^ε_L`. -/
theorem top_lambda_orb (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hI : Cited_VermaHomInjective) (hset : MinimalSetting p p' r s b)
    (wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)) (htl : TopLayerSetting p p' r s b wp wm)
    (ε : Bool) {L : ℕ} (hL : 1 ≤ L) (x : Nat.Partition (ellOrb p p' r s ε L) → ℂ)
    (hx : Verma.pbwCoord (ellOrb p p' r s ε L) x = if ε then wp L else wm L) :
    nodeTop p p' r s b (true, 0) (ε, L) =
      algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) x) *
        RatFunc.C (jform (kacC b) (kacH r s b) (ellOrb p p' r s ε L) L x x)⁻¹ := by
  cases ε
  · revert x hx
    rw [TT.ellOrb_false hL]
    intro x hx
    simp only [Bool.false_eq_true, ↓reduceIte] at hx
    obtain ⟨xp, hxp⟩ := Verma.mem_level_of_L_zero (htl.1 L hL).1.2.1
    exact (top_lambda hK hH hI hset wp wm htl hL xp x hxp hx).2
  · revert x hx
    rw [TT.ellOrb_true hL]
    intro x hx
    simp only [↓reduceIte] at hx
    obtain ⟨xm, hxm⟩ := Verma.mem_level_of_L_zero (htl.1 L hL).2.2.1
    exact (top_lambda hK hH hI hset wp wm htl hL x xm hx hxm).1

/-- Corollary 8.9, the values on the diagonal at `λ`. -/
theorem cor_diag_i (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hI : Cited_VermaHomInjective) (hset : MinimalSetting p p' r s b)
    (wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)) (htl : TopLayerSetting p p' r s b wp wm)
    (ε : Bool) (L j : ℕ) (hL : 1 ≤ L) (hj : j < L) (x : Nat.Partition (ellOrb p p' r s ε L) → ℂ)
    (hx : Verma.pbwCoord (ellOrb p p' r s ε L) x = if ε then wp L else wm L) :
    (nodeChain p p' r s b (true, 0) (ε, L) (L - j) j).coeff 0 =
      ((fDiag 0 L j / j.factorial *
          ((nodeS p p' r s (ε, L) : ℚ) / nodeS p p' r s (true, 0)) ^ j : ℚ) : Kd) *
        (algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) x) *
          RatFunc.C (jform (kacC b) (kacH r s b) (ellOrb p p' r s ε L) L x x)⁻¹) := by
  have h := (thm_diagonal_of_cited hK hH).1 p p' r s b hset (true, 0) (ε, L)
    (show (true, 0).2 < (ε, L).2 by show 0 < L; omega) j
    (show j < (ε, L).2 - (true, 0).2 by show j < L - 0; omega)
  simp only [Nat.sub_zero] at h
  rw [h, top_lambda_orb hK hH hI hset wp wm htl ε hL x hx]

/-- Corollary 8.9, `γ^±_2`. -/
theorem cor_diag_ii (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique) (hset : MinimalSetting p p' r s b)
    (wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b)) (htl : TopLayerSetting p p' r s b wp wm)
    (ε : Bool) (x : Nat.Partition (ellOrb p p' r s ε 2) → ℂ)
    (hx : Verma.pbwCoord (ellOrb p p' r s ε 2) x = if ε then wp 2 else wm 2)
    (hx1 : x (onesPartition (ellOrb p p' r s ε 2)) = 1) :
    jform (kacC b) (kacH r s b) (ellOrb p p' r s ε 2) 2 x x =
      (if ε then -1 else 1) * ((((p' : ℤ) * r + p * s : ℤ) : ℂ) / (((p' : ℤ) * r - p * s : ℤ) : ℂ)) /
        (genA r s b * genA (if ε then p + r else p - r) (if ε then p' - s else p' + s) b) := by
  have hT := top_lambda_orb hK hH hI hset wp wm htl ε (L := 2) (by norm_num) x hx
  have hsing : Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b)
      (ellOrb p p' r s ε 2) x) (ellOrb p p' r s ε 2) := by
    rw [hx]
    cases ε
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [TT.ellOrb_false (by norm_num)]
      exact (htl.1 2 (by norm_num)).2
    · simp only [↓reduceIte]
      rw [TT.ellOrb_true (by norm_num)]
      exact (htl.1 2 (by norm_num)).1
  have hτ := ((sub_tau_factorization hH hU) p p' r s b hset 2 ε (by norm_num) x hx1 hsing).2
    (by norm_num)
  have hθ : ((true, 1) : Node) ∈ firstSteps (true, 0) (ε, 2) :=
    mem_firstSteps.2 (Or.inl ⟨by simp, by simp, by simp⟩)
  have hθμ : ((true, 1) : Node) ≠ (ε, 2) := by simp
  have hid := top_identity hK hH hset hθ hθμ
  have hr1 : nodeTop p p' r s b (true, 0) (true, 1) = nodeRho p p' r s b (true, 0) (true, 1) := by
    rw [rho_eq hK hH hset (show (true, 0).2 < (true, 1).2 by simp) (by show (1 - 0) % 2 = 1; omega),
      fs_01, Finset.prod_empty, div_one]
  have hr2 : nodeTop p p' r s b (true, 1) (ε, 2) = nodeRho p p' r s b (true, 1) (ε, 2) := by
    rw [rho_eq hK hH hset (show (true, 1).2 < (ε, 2).2 by simp) (by show (2 - 1) % 2 = 1; omega),
      fs_12, Finset.prod_empty, div_one]
  have hA1 := genA_ne_of (fac_ne_one hset (show (true, 0).2 < (true, 1).2 by simp) (by simp))
  have hA2 := genA_ne_of (fac_ne_one hset (show (true, 1).2 < (ε, 2).2 by simp) (by simp))
  rw [lab1 hset] at hA1
  rw [lab2 hset] at hA2
  have hTne := top_ne hK hH hset (x := (true, 0)) (y := (ε, 2)) (by simp)
  rw [hr1, hr2, rho_one_label hset (show (true, 0).2 < (true, 1).2 by simp) (by simp),
    rho_one_label hset (show (true, 1).2 < (ε, 2).2 by simp) (by simp), lab1 hset, lab2 hset, hT,
    topFac_val, ← map_ratCast (RatFunc.C : ℂ →+* Kd)] at hid
  rw [hT] at hTne
  cases ε
  · simp only [Bool.false_eq_true, ↓reduceIte] at hτ hid hA2 ⊢
    norm_num at hτ
    rw [hτ] at hid hTne
    have hP : algebraMap ℂ[X] Kd (genPpoly r s b) * algebraMap ℂ[X] Kd (genPpoly (p - r) (p' + s) b)
        ≠ 0 := by
      rw [← map_mul]; intro h0; apply hTne; rw [h0, zero_mul]
    rw [gamma_alg (mul_ne_zero hA1 hA2) hP hid]
    push_cast
    ring
  · simp only [↓reduceIte] at hτ hid hA2 ⊢
    norm_num at hτ
    rw [hτ] at hid hTne
    have hP : algebraMap ℂ[X] Kd (genPpoly r s b) * algebraMap ℂ[X] Kd (genPpoly (p + r) (p' - s) b)
        ≠ 0 := by
      rw [← map_mul]; intro h0; apply hTne; rw [h0, zero_mul]
    rw [gamma_alg (mul_ne_zero hA1 hA2) hP hid]
    push_cast
    ring

/-- Corollary 8.9 (`cor:diagonal-lambda`), from the cited results (through Theorems 8.8, 8.2 and
the factorization of the layer norms).

Paper label: cor:diagonal-lambda -/
theorem cor_diagonal_lambda_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hI : Cited_VermaHomInjective) (hU : Cited_SingularUnique) : Stmt_cor_diagonal_lambda := by
  intro p p' r s b hset wp wm htl
  exact ⟨fun ε L j hL hj x hx => cor_diag_i hK hH hI hset wp wm htl ε L j hL hj x hx,
    fun ε x hx hx1 => cor_diag_ii hK hH hI hU hset wp wm htl ε x hx hx1⟩

end Virasoro
