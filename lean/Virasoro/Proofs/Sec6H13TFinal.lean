import Virasoro.Proofs.Sec6H13TRhoEnd

/-!
# Proposition 6.8(ii): `[t^i Y^j]` of each term of the expansion of `R_M` (paper.tex l.1304–1378)

`jL(Tfam ν r M) = ∑_{(μ₀, μ)} M^{\underline{w₀}} · K̂_r(μ₀; μ)(M) · G₂(μ₀, μ)(M)` over admissible
`μ₀, μ` with `|μ₀|, |μ| ≤ M` (l.1306–1309), where `M^{\underline{w₀}} G₂ = (M!/2^M) Y^M D₀⁻¹(λ₀)
ρ̃_{λ₀,λ}` (l.1333–1352).  Each term is good from the level `0` on with valuation `max(w₀, w)`
(root sets, l.1374–1378), so each coefficient sees finitely many terms, and `[t^i Y^j] Tfam` is a
polynomial in `M` of degree at most `2i + 2j` (`Stmt_sub_h13_degree_chain`).
-/

namespace Virasoro.H13T

open Virasoro.H13D Virasoro.H13C Verma Finset

/-- The `ρ̃` end `(M!/2^M) Y^M D₀⁻¹(λ₀) ρ̃_{λ₀,λ}` along the levels. -/
noncomputable def rhoHat (ν : Fin 2) (μ₀ μ : List ℕ) (M : ℕ) : LL :=
  jL (cQ ((M.factorial : ℚ) / 2 ^ M) * Yp M * D0i M (lamOf μ₀ M) (lamOf μ₀ M) *
    RL ν M (lamOf μ₀ M) (lamOf μ M))

/-- `G₂ = ∑_{box} rhoN2`. -/
noncomputable def G2 (ν : Fin 2) (μb μk : List ℕ) (M : ℕ) : LL :=
  ∑ τ ∈ box M, rhoN2 ν μb μk M τ.1 τ.2.1 τ.2.2.1 τ.2.2.2.1 τ.2.2.2.2

theorem rhoHat_pairing (ν : Fin 2) {μ₀ μ : List ℕ} (h₀ : Adm μ₀) (h : Adm μ) {M : ℕ}
    (hM0 : μ₀.sum ≤ M) (hM : μ.sum ≤ M) :
    rhoHat ν μ₀ μ M = cL ((M.factorial : ℚ) / 2 ^ M) * mono 0 M 1 *
        (cL (1 / (topNat (μ₀ ++ List.replicate (M - μ₀.sum) 1)
          (μ₀ ++ List.replicate (M - μ₀.sum) 1) : ℚ)) *
          mono 0 (-((μ₀.length + (M - μ₀.sum) : ℕ) : ℤ)) 1) *
        tL ^ ((μ₀.length + (M - μ₀.sum)) + (μ.length + (M - μ.sum))) *
        pairing cLc DL (dL ν) (neg (μ₀ ++ List.replicate (M - μ₀.sum) 1))
          (neg (μ ++ List.replicate (M - μ.sum) 1)) := by
  have hR : jL (RL ν M (lamOf μ₀ M) (lamOf μ M)) =
      fL (torusWordT tS cS Polynomial.X (dS ν) (lamOf μ₀ M).word (lamOf μ M).word) := rfl
  rw [rhoHat]
  simp only [D0i, Matrix.diagonal_apply_eq, map_mul, jL_cQ, jL_Yp]
  rw [hR, fL_torusWordT ν _ _ (word_pos _), torusWord_eq_pairing ν _ _ (word_pos _) (word_pos _),
    lamOf_word h₀ hM0, lamOf_word h hM, List.length_append, List.length_replicate,
    List.length_append, List.length_replicate]
  ring

theorem rhoHat_eq (ν : Fin 2) {μ₀ μ : List ℕ} (h₀ : Adm μ₀) (h : Adm μ) {M : ℕ}
    (hM0 : μ₀.sum ≤ M) (hM : μ.sum ≤ M) :
    rhoHat ν μ₀ μ M = cL ((M.descFactorial μ₀.sum : ℕ) : ℚ) * G2 ν μ₀ μ M := by
  rw [rhoHat_pairing ν h₀ h hM0 hM]
  set ar := M - μ₀.sum with har
  set a0 := M - μ.sum with ha0
  have hM1 : M = μ₀.sum + ar := by omega
  have hM2 : M = μ.sum + a0 := by omega
  have step : cL ((M.factorial : ℚ) / 2 ^ M) * mono 0 M 1 *
        (cL (1 / (topNat (μ₀ ++ List.replicate ar 1) (μ₀ ++ List.replicate ar 1) : ℚ)) *
          mono 0 (-((μ₀.length + ar : ℕ) : ℤ)) 1) *
        tL ^ ((μ₀.length + ar) + (μ.length + a0)) *
        pairing cLc DL (dL ν) (neg (μ₀ ++ List.replicate ar 1)) (neg (μ ++ List.replicate a0 1)) =
      ∑ p1 ∈ range (ar + 1), ∑ mL ∈ range (ar - p1 + 1), ∑ p2 ∈ range (ar - p1 - mL + 1),
        ∑ q ∈ range (a0 - (ar - p1 - mL - p2) + 1),
          ∑ m' ∈ range (a0 - (ar - p1 - mL - p2) - q + 1),
            rhoN ν μ₀ μ M p1 (p2 + (ar - p1 - mL - p2)) p2 q (a0 - (ar - p1 - mL - p2) - q - m') := by
    rw [torus_ones_raw]
    simp only [mul_sum]
    refine sum_congr rfl fun p1 hp1 => sum_congr rfl fun mL hmL => sum_congr rfl fun p2 hp2 =>
      sum_congr rfl fun q hq => sum_congr rfl fun m' hm' => ?_
    simp only [mem_range] at hp1 hmL hp2 hq hm'
    by_cases hk : ar - p1 - mL - p2 ≤ a0
    · exact rho_term_eq ν μ₀ μ h₀.2 hM1 hM2 (by omega) (by omega)
    · rw [rawT, (Nat.descFactorial_eq_zero_iff_lt (n := a0)).2 (by omega), rhoN,
        (Nat.descFactorial_eq_zero_iff_lt (n := M - μ.sum)).2 (by omega)]
      simp only [Nat.cast_zero, map_zero, mul_zero, zero_mul]
  have hz1 : ∀ p1 r p2 q s, ar < p1 + r → rhoN ν μ₀ μ M p1 r p2 q s = 0 := by
    intro p1 r p2 q s hlt
    rw [rhoN, (Nat.descFactorial_eq_zero_iff_lt (n := M)).2 (by omega)]
    simp only [Nat.cast_zero, map_zero, mul_zero, zero_mul]
  have hz2 : ∀ p1 r p2 q s, p2 ≤ r → a0 < r - p2 + q + s → rhoN ν μ₀ μ M p1 r p2 q s = 0 := by
    intro p1 r p2 q s _ hlt
    rw [rhoN, (Nat.descFactorial_eq_zero_iff_lt (n := M - μ.sum)).2 (by omega)]
    simp only [Nat.cast_zero, map_zero, mul_zero, zero_mul]
  rw [step]
  refine (raw5_eq_box (rhoN ν μ₀ μ M) (N := M) (by omega) (by omega) hz1 hz2).trans ?_
  rw [← sum_box M (rhoN ν μ₀ μ M), G2, mul_sum]
  exact sum_congr rfl fun τ _ => rhoN_eq ν μ₀ μ M _ _ _ _ _

theorem coeff_cL_mul_zero (q : ℚ) (F : LL) (n : ℤ) (h : F.coeff n = 0) : (cL q * F).coeff n = 0 := by
  rw [cL, RingHom.comp_apply, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, h, smul_zero]

/-- `G₂` is good from the level `max(w₀, w)` on, with degree drop and valuation `w₀`. -/
theorem good_G2 (ν : Fin 2) {μ₀ μ : List ℕ} (h₀ : Adm μ₀) (h : Adm μ) :
    GF (G2 ν μ₀ μ) (max μ₀.sum μ.sum) μ₀.sum μ₀.sum := by
  refine GF.of_sum_sz box (fun τ => τ.2.2.1 ≤ τ.2.1) szB 0 (fun M τ => mem_box) (fun M _ => rfl)
    ⟨0, fun M hM n hn => ?_⟩ (fun τ hτ => ?_) (fun τ M hτ hW hlt => ?_)
  · have hd : ((M.descFactorial μ₀.sum : ℕ) : ℚ) ≠ 0 := by
      have : M.descFactorial μ₀.sum ≠ 0 := fun h0 =>
        absurd ((Nat.descFactorial_eq_zero_iff_lt).1 h0) (by omega)
      exact_mod_cast this
    have e : G2 ν μ₀ μ M = cL (1 / ((M.descFactorial μ₀.sum : ℕ) : ℚ)) * rhoHat ν μ₀ μ M := by
      rw [rhoHat_eq ν h₀ h (by omega) (by omega), ← mul_assoc, ← map_mul, one_div_mul_cancel hd,
        map_one, one_mul]
    rw [e]
    exact coeff_cL_mul_zero _ _ n (by rw [rhoHat]; exact jL_coeff_neg _ n hn)
  · exact (good_rhoN2 ν μ₀ μ h₀.2 hτ).mono le_rfl (by omega)
  · obtain ⟨p1, r, p2, q, s⟩ := τ
    dsimp only [szB] at hτ hlt ⊢
    rw [rhoN2]
    by_cases hb : M - μ₀.sum < p1 + r
    · rw [(Nat.descFactorial_eq_zero_iff_lt).2 hb]
      simp only [Nat.cast_zero, zero_mul, map_zero]
    · rw [(Nat.descFactorial_eq_zero_iff_lt (n := M - μ.sum)).2 (by omega)]
      simp only [Nat.cast_zero, mul_zero, zero_mul, map_zero]

/-! ### The terms of the expansion and the degree count -/

/-- The `(μ₀, μ)`-term `M^{\underline{w₀}} K̂_r(μ₀; μ) G₂(μ₀, μ)`. -/
noncomputable def termF (ν : Fin 2) (r : ℕ) (x : List ℕ × List ℕ) (M : ℕ) : LL :=
  cL ((M.descFactorial x.1.sum : ℕ) : ℚ) * (Khat r x.1 x.2 M * G2 ν x.1 x.2 M)

theorem jL_Tfam (ν : Fin 2) (r M : ℕ) :
    jL (Tfam ν r M) = ∑ x ∈ admSet M ×ˢ admSet M, termF ν r x M := by
  have e1 : Tfam ν r M = ∑ Y, ∑ Y', (cQ ((M.factorial : ℚ) / 2 ^ M) * Yp M * D0i M Y Y *
      RL ν M Y Y') * (Em M ^ r) Y Y' := by
    rw [Tfam, trR, mul_sum]
    refine sum_congr rfl fun Y _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun Y' _ => ?_
    rw [D0i, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]
    ring
  rw [e1]
  simp only [map_sum, sum_partition_eq M]
  rw [sum_product]
  refine sum_congr rfl fun μ₀ hμ₀ => sum_congr rfl fun μ hμ => ?_
  obtain ⟨h₀, hM0⟩ := mem_admSet.1 hμ₀
  obtain ⟨h, hM⟩ := mem_admSet.1 hμ
  have eK : jL ((Em M ^ r) (lamOf μ₀ M) (lamOf μ M)) = Khat r μ₀ μ M := by
    rw [Khat, if_pos ⟨hM0, hM⟩]
  have eR : jL (cQ ((M.factorial : ℚ) / 2 ^ M) * Yp M * D0i M (lamOf μ₀ M) (lamOf μ₀ M) *
      RL ν M (lamOf μ₀ M) (lamOf μ M)) = rhoHat ν μ₀ μ M := rfl
  rw [map_mul, eR, eK, rhoHat_eq ν h₀ h hM0 hM, termF]
  ring

theorem good_termF (ν : Fin 2) (r : ℕ) {x : List ℕ × List ℕ} (hx : Adm x.1 ∧ Adm x.2) :
    GF (termF ν r x) 0 0 (max 0 (((max x.1.sum x.2.sum : ℕ) : ℤ) - 0)) := by
  obtain ⟨μ₀, μ⟩ := x
  obtain ⟨h₀, h⟩ : Adm μ₀ ∧ Adm μ := hx
  show GF (fun M => cL ((M.descFactorial μ₀.sum : ℕ) : ℚ) * (Khat r μ₀ μ M * G2 ν μ₀ μ M)) 0 0
    (max 0 (((max μ₀.sum μ.sum : ℕ) : ℤ) - 0))
  have hKG := GF.mul_vanish (good_Khat h₀ r μ h) (good_G2 ν h₀ h) (le_max_left _ _)
    (fun M h1 h2 => Khat_low (Or.inr (by omega)))
  have hT := GF.pi_mul (descPochhammer ℚ μ₀.sum) (e := μ₀.sum)
    (descPochhammer_natDegree ℚ μ₀.sum).le (W₀ := 0) (W := μ₀.sum) (Nat.zero_le _)
    (fun M _ hM => by
      rw [descPochhammer_eval_eq_descFactorial, (Nat.descFactorial_eq_zero_iff_lt).2 hM,
        Nat.cast_zero]) hKG
  refine (hT.congr fun M _ => ?_).mono (by omega) (by omega)
  rw [descPochhammer_eval_eq_descFactorial]

/-- Every `[t^i Y^j]` of `jL(Tfam ν r M)` is a polynomial in `M` of degree at most `2i + 2j`. -/
theorem good_jTfam (ν : Fin 2) (r : ℕ) : Good (fun M => jL (Tfam ν r M)) 0 0 := by
  have := GF.of_sum_sz (G := fun M => jL (Tfam ν r M)) (F := termF ν r) (W := 0) (D := 0) (V := 0)
    (fun M => admSet M ×ˢ admSet M) (fun x => Adm x.1 ∧ Adm x.2)
    (fun x => max x.1.sum x.2.sum) 0
    (fun M x => by
      rw [mem_product, mem_admSet, mem_admSet, max_le_iff]
      tauto)
    (fun M _ => jL_Tfam ν r M) ⟨0, fun M _ n hn => jL_coeff_neg _ n hn⟩
    (fun x hx => good_termF ν r hx)
    (fun x M _ _ hM => by
      rw [termF, Khat_low (by omega : M < x.1.sum ∨ M < x.2.sum), zero_mul, mul_zero])
  exact GF.good this

/-- Proposition 6.8(ii), the reduced statement (paper.tex l.1304–1378). -/
theorem sub_h13_degree_chain : Stmt_sub_h13_degree_chain := by
  intro ν r i j
  have h := (good_jTfam ν r).poly (i : ℤ) j
  simp only [cfL_jL, sub_zero] at h
  exact h

end Virasoro.H13T
