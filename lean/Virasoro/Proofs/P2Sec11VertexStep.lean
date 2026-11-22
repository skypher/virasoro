import Virasoro.Proofs.P2Sec11VertexRad

/-!
# Proposition 11.2(i): the induction step and part (i) (paper.tex l.2423–2459)

Assembly of `Stmt_sub_vertex_step`.  The arithmetic input is equation (10.6) for the levels of
the orbit and the Kac label `(R,S)` of each primitive arrow `μ^{ε'}_{k₀+i} → μ^η_{k₀+i+1}`, with
`R > k`, `S > m` (equation (10.7)), so that `P_{R,S}(b⋆;μ^{ε'}_{k₀+i},h_{2k+1,2m+1}(b⋆)) = 0`
(Proposition 10.2(ii)).
-/

namespace Virasoro

open Polynomial Verma

variable {p p' r s : ℕ}

/-- The levels increase along every primitive arrow. -/
theorem ellOrb_lt_succ (hp : 0 < p) (hp' : 0 < p') (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s)
    (hs : s < p') (ε : Bool) (k : ℕ) (ε' : Bool) :
    ellOrb p p' r s ε k < ellOrb p p' r s ε' (k + 1) := by
  obtain ⟨R, S, hR, hS, hsum, hdiff, -⟩ := arrow_data hr0 hr hs0 hs ε k ε'
  have h1 := arrow_level hp hp' hr hs ε k ε' hsum hdiff
  have h2 : 0 < R * S := Nat.mul_pos hR hS
  omega

theorem ellOrb_lt_add (hp : 0 < p) (hp' : 0 < p') (hr0 : 0 < r) (hr : r < p) (hs0 : 0 < s)
    (hs : s < p') (ε : Bool) (k₀ : ℕ) :
    ∀ j : ℕ, 1 ≤ j → ∀ ε' : Bool, ellOrb p p' r s ε k₀ < ellOrb p p' r s ε' (k₀ + j) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => exact fun ε' => ellOrb_lt_succ hp hp' hr0 hr hs0 hs ε k₀ ε'
  | succ j _ ih =>
    intro ε'
    exact (ih true).trans (ellOrb_lt_succ hp hp' hr0 hr hs0 hs true (k₀ + j) ε')

/-- Equation (10.6): `μ^{ε'}_k = μ^ε_{k₀} + (ℓ^{ε'}_k - ℓ^ε_{k₀})`. -/
theorem muOrb_add_lev (hp : 0 < p) (hp' : 0 < p') (hr : r < p) (hs : s < p') (ε : Bool)
    (k₀ : ℕ) (ε' : Bool) (k : ℕ) (hle : ellOrb p p' r s ε k₀ ≤ ellOrb p p' r s ε' k) :
    muOrb p p' r s ε k₀ + ((ellOrb p p' r s ε' k - ellOrb p p' r s ε k₀ : ℕ) : ℂ) =
      muOrb p p' r s ε' k := by
  have h1 := four_ellOrb hr hs ε' k
  have h2 := four_ellOrb hr hs ε k₀
  have h1c : (4 : ℂ) * p * p' * (ellOrb p p' r s ε' k : ℂ) =
      (nOrb p p' r s ε' k : ℂ) ^ 2 - ((p' : ℂ) * r - p * s) ^ 2 := by exact_mod_cast h1
  have h2c : (4 : ℂ) * p * p' * (ellOrb p p' r s ε k₀ : ℂ) =
      (nOrb p p' r s ε k₀ : ℂ) ^ 2 - ((p' : ℂ) * r - p * s) ^ 2 := by exact_mod_cast h2
  have hne : (4 : ℂ) * p * p' ≠ 0 := by
    have h1 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have h2 : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
    exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2
  rw [Nat.cast_sub hle, muOrb, muOrb, momWt, momWt, eq_div_iff hne, add_mul,
    div_mul_cancel₀ _ hne]
  linear_combination h1c - h2c

/-- For the arrow `μ^{ε'}_{k₀+j} → μ^η_{k₀+j+1}` inside `M(c⋆,μ^ε_{k₀})`: a singular vector of
`M(c⋆,μ^{ε'}_{k₀+j})` at the level of the arrow pairs to zero with the highest-weight vector
under `ρ_{c⋆,μ^{ε'}_{k₀+j},d}`, `d = h_{2k+1,2m+1}(b⋆)` (l.2447–2451). -/
theorem orbit_pair_zero (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique)
    (hF : Cited_FusionPolynomial) {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool)
    (k₀ k m : ℕ) (hk : k < min r (p - r)) (hm : m < min s (p' - s)) (ε' : Bool) (j : ℕ)
    (hj : 1 ≤ j) (η : Bool)
    (u : Verma ℂ (kacC b) (muOrb p p' r s ε k₀ +
      ((ellOrb p p' r s ε' (k₀ + j) - ellOrb p p' r s ε k₀ : ℕ) : ℂ)))
    (hu : IsSingular u ((ellOrb p p' r s η (k₀ + (j + 1)) - ellOrb p p' r s ε k₀) -
      (ellOrb p p' r s ε' (k₀ + j) - ellOrb p p' r s ε k₀))) :
    pairing (kacC b) (muOrb p p' r s ε k₀ +
      ((ellOrb p p' r s ε' (k₀ + j) - ellOrb p p' r s ε k₀ : ℕ) : ℂ))
      (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) u hw = 0 := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hb0 : b ≠ 0 := by
    rintro rfl
    have h0 : -(p' : ℂ) / p = 0 := by rw [← hb]; simp
    rw [div_eq_zero_iff, neg_eq_zero] at h0
    rcases h0 with h | h <;> · norm_cast at h; omega
  obtain ⟨R, S, hR, hS, hsum, hdiff, hcR, hcS, -⟩ := arrow_data hr0 hr hs0 hs ε' (k₀ + j) η
  have hlt := ellOrb_lt_add hp hp' hr0 hr hs0 hs ε k₀ j hj ε'
  have hμ : muOrb p p' r s ε k₀ +
      ((ellOrb p p' r s ε' (k₀ + j) - ellOrb p p' r s ε k₀ : ℕ) : ℂ) = kacH R S b := by
    rw [muOrb_add_lev hp hp' hr hs ε k₀ ε' (k₀ + j) hlt.le, kacH_momWt hp hp' hb, muOrb]
    rcases hdiff with h | h
    · rw [h]
    · rw [h, momWt_neg]
  have hlev := arrow_level hp hp' hr hs ε' (k₀ + j) η hsum hdiff
  have hRS : 0 < R * S := Nat.mul_pos hR hS
  have hl : (ellOrb p p' r s η (k₀ + (j + 1)) - ellOrb p p' r s ε k₀) -
      (ellOrb p p' r s ε' (k₀ + j) - ellOrb p p' r s ε k₀) = R * S := by
    rw [← Nat.add_assoc]
    omega
  rw [hl] at hu
  have hRk := min_le_of_congr hcR
  have hSm := min_le_of_congr hcS
  rw [pairing_singular_fus hH hU hF hb0 hR hS _ hμ _ _ (isPrimaryPairing_pairing _) u hu, hμ,
    fusP_roots]
  exact ⟨2 * k + 1, mem_oddsBelow.2 ⟨by omega, by omega⟩, 2 * m + 1,
    mem_oddsBelow.2 ⟨by omega, by omega⟩, by push_cast; rfl⟩

/-- `Stmt_sub_vertex_step` (paper.tex l.2423–2459): the induction step of
Proposition 11.2(i). -/
theorem sub_vertex_step (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_vertex_step := by
  intro p p' r s b hset ε k₀ k m hk hm T hT i H N₁ N₂ a a₂ wa wb ha hb
  have G := vertexGen_of_clauses H
  have hR : IsJWard (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)
      (jantzen (kacC b) (muOrb p p' r s ε k₀) (i + 1)) (rhoJ T (i + 1)) :=
    ⟨fun hx hx' hy => rhoJ_add_left hT G hx hx' hy, fun a _ _ hx hy => rhoJ_smul_left hT G a hx hy,
      rhoJ_symm hT _, fun n _ _ hx hy => rhoJ_ward hT G n hx hy,
      fun n _ hx => L_mem_jantzen _ _ (i + 1) n hx⟩
  -- `J^{i+2} ⊂ rad ρ^{(i+1)}` (l.2439–2459)
  have hrad : ∀ x ∈ jantzen (kacC b) (muOrb p p' r s ε k₀) (i + 1 + 1),
      ∀ y ∈ jantzen (kacC b) (muOrb p p' r s ε k₀) (i + 1), rhoJ T (i + 1) x y = 0 := by
    obtain ⟨wp, wm, ⟨hsing, hlayer⟩, hint⟩ := hJ p p' r s b hset ε k₀
    have hi1 : 1 ≤ i + 1 := Nat.le_add_left 1 i
    have hi2 : 1 ≤ i + 1 + 1 := Nat.le_add_left 1 (i + 1)
    obtain ⟨hχp, hχm⟩ := hsing (i + 1) hi1
    obtain ⟨hap, ham⟩ := hsing (i + 1 + 1) hi2
    have hJ1 := hlayer (i + 1) hi1
    have hJ2 := hlayer (i + 1 + 1) hi2
    have hinf := (hint (i + 1) hi1).1
    have hsubp : negSpan (wp (i + 1)) ≤ jantzen (kacC b) (muOrb p p' r s ε k₀) (i + 1) := by
      rw [hJ1]; exact le_sup_left
    have hsubm : negSpan (wm (i + 1)) ≤ jantzen (kacC b) (muOrb p p' r s ε k₀) (i + 1) := by
      rw [hJ1]; exact le_sup_right
    have hle2 : jantzen (kacC b) (muOrb p p' r s ε k₀) (i + 1 + 1) ≤
        negSpan (wp (i + 1)) ⊓ negSpan (wm (i + 1)) := hinf.ge
    have hsp : negSpan (wp (i + 1 + 1)) ≤ jantzen (kacC b) (muOrb p p' r s ε k₀) (i + 1 + 1) := by
      rw [hJ2]; exact le_sup_left
    have hsm : negSpan (wm (i + 1 + 1)) ≤ jantzen (kacC b) (muOrb p p' r s ε k₀) (i + 1 + 1) := by
      rw [hJ2]; exact le_sup_right
    have hapm := hle2 (hsp (mem_negSpan_self _))
    have hamm := hle2 (hsm (mem_negSpan_self _))
    have hpp := hR.sing_zero hI hχp hsubp hap hapm.1
      (orbit_pair_zero hH hU hF hset ε k₀ k m hk hm true (i + 1) hi1 true)
    have hpm := hR.sing_zero hI hχm hsubm hap hapm.2
      (orbit_pair_zero hH hU hF hset ε k₀ k m hk hm false (i + 1) hi1 true)
    have hmp := hR.sing_zero hI hχp hsubp ham hamm.1
      (orbit_pair_zero hH hU hF hset ε k₀ k m hk hm true (i + 1) hi1 false)
    have hmm := hR.sing_zero hI hχm hsubm ham hamm.2
      (orbit_pair_zero hH hU hF hset ε k₀ k m hk hm false (i + 1) hi1 false)
    have := hR.radical hχp hχm hJ1 hap ham (hsp.trans (hle2.trans (inf_le_left.trans hsubp)))
      (hsm.trans (hle2.trans (inf_le_left.trans hsubp))) hpp hpm hmp hmm
    rw [← hJ2] at this
    exact this
  have hUl := ha.inLat
  have hWl := hb.inLat
  refine ⟨vg_dvd G hUl hWl, fun wa' wb' ha' hb' => ?_,
    fun n N₁' N₂' a' b' wa' wb' ha' hb' e1 e2 => ?_, fun hex => ?_⟩
  · rw [vg_congr_left G ha'.inLat hUl hb'.inLat (ha'.ev0.trans ha.ev0.symm),
      vg_congr_right hT G hUl hb'.inLat hWl (hb'.ev0.trans hb.ev0.symm)]
  · have e := congrArg (fun q : ℂ[X] => q.coeff (i + 1))
      (hT.2 n (pbwCoord N₁ wa) (pbwCoord N₂ wb))
    beta_reduce at e
    have l1 : (T (pbwCoord N₁' wa') (pbwCoord N₂ wb)).coeff (i + 1) =
        (T (Verma.L (-n) (pbwCoord N₁ wa)) (pbwCoord N₂ wb)).coeff (i + 1) :=
      vg_congr_left G ha'.inLat (hUl.L (-n)) hWl (by rw [ha'.ev0, latEv0_L, ha.ev0, e1])
    have l2 : (T (pbwCoord N₁ wa) (pbwCoord N₂' wb')).coeff (i + 1) =
        (T (pbwCoord N₁ wa) (Verma.L n (pbwCoord N₂ wb))).coeff (i + 1) :=
      vg_congr_right hT G hUl hb'.inLat (hWl.L n) (by rw [hb'.ev0, latEv0_L, hb.ev0, e2])
    have hc : ∀ q : ℂ[X], (C (muOrb p p' r s ε k₀) + X + (N₁ : ℂ[X])) * q -
        (C (muOrb p p' r s ε k₀) + X + (N₂ : ℂ[X])) * q +
          (n : ℂ[X]) * C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) * q =
        C (((N₁ : ℂ) - (N₂ : ℂ)) + (n : ℂ) * kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) * q := by
      intro q
      simp only [map_sub, map_add, map_mul, map_natCast, map_intCast]
      ring
    rw [L_zero_of_mem_level ⟨wa, rfl⟩, L_zero_of_mem_level ⟨wb, rfl⟩, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, hc, coeff_sub, coeff_C_mul] at e
    rw [l1, l2]
    exact e
  · rw [rhoJ_eq hT G hUl hWl, ha.ev0, hb.ev0]
    rcases hex with ⟨w, hw⟩ | ⟨w, hw⟩
    · exact hrad _ (pbwCoord_mem_jantzen ⟨w, hw.1, hw.2⟩) _
        (pbwCoord_mem_jantzen ⟨wb, hb.1, hb.2⟩)
    · rw [rhoJ_symm hT]
      exact hrad _ (pbwCoord_mem_jantzen ⟨w, hw.1, hw.2⟩) _
        (pbwCoord_mem_jantzen ⟨wa, ha.1, ha.2⟩)

example (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective) :
    Stmt_sub_vertex_step := sub_vertex_step hJ hH hU hF hI

/-- Proposition 11.2(i) (paper.tex l.2378–2384, proof l.2412–2459). -/
theorem vertex_part_i (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial) (hI : Cited_VermaHomInjective)
    (p p' r s : ℕ) (b : ℂ) (hset : MinimalSetting p p' r s b) (ε : Bool) (k₀ k m : ℕ)
    (hk : k < min r (p - r)) (hm : m < min s (p' - s))
    (T : Verma ℂ[X] (C (kacC b)) (C (muOrb p p' r s ε k₀) + X) →ₗ[ℂ[X]]
      Verma ℂ[X] (C (kacC b)) (C (muOrb p p' r s ε k₀) + X) →ₗ[ℂ[X]] ℂ[X])
    (hT : Verma.IsPrimaryPairing (C (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b)) T) (i : ℕ) :
    ∀ (N₁ N₂ : ℕ) (a : Nat.Partition N₁ → ℂ) (a₂ : Nat.Partition N₂ → ℂ)
      (wa : Nat.Partition N₁ → ℂ[X]) (wb : Nat.Partition N₂ → ℂ[X]),
      IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₁ i a wa →
      IsJFamily (kacC b) (muOrb p p' r s ε k₀) N₂ i a₂ wb →
        VertexClausesAt (kacC b) (muOrb p p' r s ε k₀)
          (kacH (2 * (k : ℤ) + 1) (2 * (m : ℤ) + 1) b) i T N₁ N₂ a a₂ wa wb :=
  vertex_part_i_of_step hJ hH hU hF (sub_vertex_step hJ hH hU hF hI) p p' r s b hset ε k₀ k m hk
    hm T hT i

end Virasoro
