import Virasoro.Sphere.Proofs.Sec5SharpPoint
import Virasoro.Sphere.Proofs.Sec6Examples
import Virasoro.Proofs.Sec5SharpArith
import Virasoro.Proofs.Sec6TwoTerm
import Virasoro.Proofs.Sec6TTFrame
import Virasoro.Proofs.Sec6Regular

/-!
# Theorem 5.4 (`thm:sharp-B`): the pole of `ℬ_N` at `Δ = λ` has order exactly `j_N(λ)`

sphere/paper.tex l.1607–1691.  By Theorem 5.3 the coefficient of `(Δ-λ)^{-k}` is the sum of the
two summands `π^±(Δ₄,Δ₃) π^±(Δ₁,Δ₂)/γ^± · ℬ_{N-ℓ^±}(c⋆,μ^±,Δ_i)`.  Each summand is the image in
`K4 = ℂ(Δ₁,…,Δ₄)` of a polynomial in `Δ₁,…,Δ₄`; the sum of the two polynomials is nonzero at the
rational point of l.1621–1628: the higher branch vanishes there (Lemma 5.2(iii)), the
lower-branch factors `π` do not (Lemma 5.2(iii)), and `ℬ_M = (-1)^M binom(κ,M) ≠ 0` there
(the BPZ equation, `block_point`).
-/

namespace Virasoro.Sphere

open Virasoro Polynomial Verma Finset

/-! ### The summand as a polynomial in the external weights -/

/-- `∑_{Y,Z} γ_Y(μ;Δ₄,Δ₃) (G_M(c,μ)⁻¹)_{Y,Z} γ_Z(μ;Δ₁,Δ₂)` as a polynomial in `Δ₁,…,Δ₄`. -/
noncomputable def BR (c μ : ℂ) (M : ℕ) : MvPolynomial (Fin 4) ℂ :=
  ∑ Y : Nat.Partition M, ∑ Z : Nat.Partition M,
    gammaY (MvPolynomial.C μ) (MvPolynomial.X 3) (MvPolynomial.X 2) Y.word *
      MvPolynomial.C ((gram c μ M)⁻¹ Y Z) *
      gammaY (MvPolynomial.C μ) (MvPolynomial.X 0) (MvPolynomial.X 1) Z.word

theorem algebraMap_C_K4 (x : ℂ) :
    algebraMap (MvPolynomial (Fin 4) ℂ) K4 (MvPolynomial.C x) = cK x := by
  rw [cK, IsScalarTower.algebraMap_apply ℂ (MvPolynomial (Fin 4) ℂ) K4,
    MvPolynomial.algebraMap_eq]

/-- Over `K4`, `ℬ_M(c,μ,Δ_i)` at a point `μ` with `det G_M(c,μ) ≠ 0` is the image of `BR`. -/
theorem evalBsph_K4 {c μ : ℂ} {M : ℕ} (h : (gram c μ M).det ≠ 0) :
    RatFunc.eval (RingHom.id K4) (cK μ) (Bsph (cK c) ΔK M) =
      algebraMap (MvPolynomial (Fin 4) ℂ) K4 (BR c μ M) := by
  have hG : gram (cK c) (cK μ) M = (gram c μ M).map cK := gram_map (algebraMap ℂ K4) c μ M
  have hdet : (gram (cK c) (cK μ) M).det ≠ 0 := by
    rw [hG, show ((gram c μ M).map cK).det = cK (gram c μ M).det from
      (RingHom.map_det (algebraMap ℂ K4) _).symm]
    exact (_root_.map_ne_zero _).2 h
  have hinv : (gram (cK c) (cK μ) M)⁻¹ = ((gram c μ M)⁻¹).map cK :=
    gram_inv_map (algebraMap ℂ K4) c μ M
  have := evalAt_Bsph (c := cK c) (z := cK μ) ΔK hdet
  unfold evalAt at this
  rw [this, BR, map_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun Z _ => ?_
  rw [map_mul, map_mul, map_gammaY, map_gammaY, algebraMap_C_K4, algebraMap_C_K4, hinv,
    Matrix.map_apply]
  simp only [ΔK, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_eq]

/-- The value of `BR` at a point `v` is the block coefficient `ℬ_M(c,μ,v)`. -/
theorem eval_BR {c μ : ℂ} {M : ℕ} (h : (gram c μ M).det ≠ 0) (v : Fin 4 → ℂ) :
    MvPolynomial.eval v (BR c μ M) = blockAt c μ v M := by
  rw [blockAt, ← evalAt, evalAt_Bsph v h, BR, map_sum]
  refine sum_congr rfl fun Y _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun Z _ => ?_
  rw [map_mul, map_mul, map_gammaY, map_gammaY]
  simp only [MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The polynomial representative of the summand `topTermSph`. -/
noncomputable def topR (c lam : ℂ) (N ℓ k : ℕ) (x : Nat.Partition ℓ → ℂ) :
    MvPolynomial (Fin 4) ℂ :=
  if ℓ ≤ N then
    piR lam x 3 2 * piR lam x 0 1 * MvPolynomial.C (jform c lam ℓ k x x)⁻¹ *
      BR c (lam + (ℓ : ℂ)) (N - ℓ)
  else 0

theorem topTermSph_eq_topR {c lam : ℂ} {N ℓ : ℕ} (k : ℕ) (x : Nat.Partition ℓ → ℂ)
    (hdet : ℓ ≤ N → (gram c (lam + (ℓ : ℂ)) (N - ℓ)).det ≠ 0) :
    topTermSph (Bsph (cK c) ΔK) c lam N ℓ k x =
      algebraMap (MvPolynomial (Fin 4) ℂ) K4 (topR c lam N ℓ k x) := by
  unfold topTermSph topR
  split_ifs with hN
  · have hμ : cK (lam + (ℓ : ℂ)) = cK (lam + (ℓ : ℂ)) := rfl
    rw [evalBsph_K4 (hdet hN), map_mul, map_mul, map_mul, ← piScalar_K4, ← piScalar_K4,
      algebraMap_C_K4]
  · rw [map_zero]

theorem eval_topR {c lam : ℂ} {N ℓ : ℕ} (k : ℕ) (x : Nat.Partition ℓ → ℂ) (hN : ℓ ≤ N)
    (hdet : (gram c (lam + (ℓ : ℂ)) (N - ℓ)).det ≠ 0) (v : Fin 4 → ℂ) :
    MvPolynomial.eval v (topR c lam N ℓ k x) =
      piScalar lam x (v 3) (v 2) * piScalar lam x (v 0) (v 1) * (jform c lam ℓ k x x)⁻¹ *
        blockAt c (lam + (ℓ : ℂ)) v (N - ℓ) := by
  rw [topR, if_pos hN, map_mul, map_mul, map_mul, eval_piR, eval_piR, MvPolynomial.eval_C,
    eval_BR hdet]

/-- A nonzero value at one point makes the image in `K4` nonzero. -/
theorem algebraMap_K4_ne {P : MvPolynomial (Fin 4) ℂ} (v : Fin 4 → ℂ)
    (h : MvPolynomial.eval v P ≠ 0) : algebraMap (MvPolynomial (Fin 4) ℂ) K4 P ≠ 0 := by
  intro h0
  apply h
  rw [(IsFractionRing.injective (MvPolynomial (Fin 4) ℂ) K4) (h0.trans (map_zero _).symm),
    map_zero]

/-! ### The rational specialization of l.1621–1628 -/

section Point

variable {p p' r s : ℕ} {b : ℂ}

/-- The weight `(a² - (p'-p)²)/(4pp')` of the momentum `a` (paper l.1622). -/
noncomputable def momC (p p' : ℕ) (a : ℂ) : ℂ := (a ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p')

/-- The external weights of the BPZ setting at `b⋆` with `β_μ = -m/p`, `β₃ = a₃/p` and `B = 0`:
`Δ₁ = wt(m + p')`, `Δ₂ = h_{2,1} = wt(2p' - p)`, `Δ₃ = wt(a₃)`, `Δ₄ = wt(m + p' - a₃ - p)`. -/
theorem bpzWeights_min (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (m a₃ : ℂ) :
    bpzWeights b (-m / p) (a₃ / p) (β4of b (-m / p) (a₃ / p)) 0 = momC p p' (m + p') ∧
    bpzWeights b (-m / p) (a₃ / p) (β4of b (-m / p) (a₃ / p)) 1 = momC p p' (2 * p' - p) ∧
    bpzWeights b (-m / p) (a₃ / p) (β4of b (-m / p) (a₃ / p)) 2 = momC p p' a₃ ∧
    bpzWeights b (-m / p) (a₃ / p) (β4of b (-m / p) (a₃ / p)) 3 =
      momC p p' (m + p' - a₃ - p) := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  obtain ⟨hb0, -⟩ := inv_sq_min hp hp' hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · show wtB b (-m / p + b ^ 2) = _
    unfold wtB momC
    rw [hb]
    field_simp
    ring
  · show kacH 2 1 b = _
    have h1 : kacH 2 1 b = (-3 * b ^ 2 - 2) / 4 := by
      unfold kacH
      push_cast
      field_simp
      ring
    rw [h1, hb]
    unfold momC
    field_simp
    ring
  · show wtB b (a₃ / p) = _
    unfold wtB momC
    rw [hb]
    field_simp
    ring
  · show wtB b (β4of b (-m / p) (a₃ / p)) = _
    unfold wtB momC β4of
    rw [hb]
    field_simp
    ring

/-- `wt_b(-m/p) = (m² - (p'-p)²)/(4pp')`. -/
theorem wtB_neg_min (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p) (m : ℂ) :
    wtB b (-m / p) = momC p p' m := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  unfold wtB momC
  rw [hb]
  field_simp
  ring

/-- Lemma 5.2(iii) for a singular vector of level `ℓ^ε_k` with any nonzero scale. -/
theorem pi_iii_any (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) (hset : MinimalSetting p p' r s b) (ε : Bool) {k n : ℕ}
    (hk : 1 ≤ k) (hn : ellOrb p p' r s ε k = n) (x : Nat.Partition n → ℂ)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) n x) n) (aa ab : ℂ) :
    (piScalar (kacH r s b) x (momC p p' aa) (momC p p' ab) = 0 →
      ∃ c₀ : ℤ, |c₀| ≤ nOrb p p' r s ε k - p' - p ∧ (aa + ab = (c₀ : ℂ) ∨ aa - ab = (c₀ : ℂ))) ∧
    ((aa - ab = ((nOrb p p' r s ε k - p' - p : ℤ) : ℂ) ∨
        aa - ab = -((nOrb p p' r s ε k - p' - p : ℤ) : ℂ)) →
      piScalar (kacH r s b) x (momC p p' aa) (momC p p' ab) = 0) := by
  subst hn
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  have hlev := TT.ellOrb_pos hp hp' hr hrp hs hsp ε hk
  have ha := sub_singular_ones_coeff _ _ _ hlev x hx
  set a := x (onesPartition _) with ha_def
  set xt := a⁻¹ • x with hxt_def
  clear_value xt
  have hxe : x = a • xt := by rw [hxt_def, smul_smul, mul_inv_cancel₀ ha, one_smul]
  have hxt1 : xt (onesPartition _) = 1 := by
    rw [hxt_def, Pi.smul_apply, smul_eq_mul, ← ha_def, inv_mul_cancel₀ ha]
  have hxts : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b)
      (ellOrb p p' r s ε k) xt) (ellOrb p p' r s ε k) := by
    rw [hxt_def, map_smul]
    exact isSingular_smul hx (inv_ne_zero ha)
  have L := (lem_pi_factorization_of_cited hH hF hU p p' r s b hset k ε hk xt hxt1 hxts).2.2 aa ab
  have hpi : piScalar (kacH r s b) x (momC p p' aa) (momC p p' ab) =
      a * piScalar (kacH r s b) xt (momC p p' aa) (momC p p' ab) := by
    rw [hxe, piScalar_smul]
    rfl
  rw [hpi]
  refine ⟨fun h0 => L.1 ((mul_eq_zero.1 h0).resolve_left ha), fun h => ?_⟩
  have h2 : piScalar (kacH r s b) xt (momC p p' aa) (momC p p' ab) = 0 := L.2 h
  rw [h2, mul_zero]

theorem nOrb_add_not (ε : Bool) (k : ℕ) :
    nOrb p p' r s ε k + nOrb p p' r s (!ε) k = 2 * k * p * p' := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> cases ε <;> simp [nOrb, h] <;> ring

/-- `κ = (kp-1)p'/(2p)` is not a natural number (l.1684–1686). -/
theorem kappa_ne_nat (hp : 2 ≤ p) (hp' : 0 < p') (hcop : Nat.Coprime p p') {k : ℕ} (hk : 1 ≤ k)
    (hb : b ^ 2 = -(p' : ℂ) / p) (i : ℕ) :
    κof b ((((k : ℤ) * p * p' - p : ℤ) : ℂ) / p) ≠ i := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast (show 0 < p by omega).ne'
  intro h
  unfold κof at h
  rw [hb] at h
  have hz : ((k : ℤ) * p - 1) * p' = 2 * p * i := by
    have : (((((k : ℤ) * p - 1) * p' : ℤ)) : ℂ) = ((2 * p * i : ℤ) : ℂ) := by
      push_cast
      rw [← h]
      push_cast
      field_simp
      ring
    exact_mod_cast this
  have h1 : (p : ℤ) ∣ ((k : ℤ) * p - 1) * p' := ⟨2 * i, by rw [hz]; ring⟩
  have h2 := (Nat.isCoprime_iff_coprime.2 hcop).dvd_of_dvd_mul_right h1
  have h3 : (p : ℤ) ∣ 1 := by
    have := dvd_sub (dvd_mul_left (p : ℤ) k) h2
    rwa [sub_sub_cancel] at this
  have h4 := Int.eq_one_of_dvd_one (by positivity) h3
  omega

/-- The nonvanishing of the sum of the two summands of Theorem 5.3 (l.1617–1691), with `ε` the
lower branch (`ℓ^ε_k < ℓ^{¬ε}_k`). -/
theorem sharp_pair_ne (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) (hBPZ : Cited_BPZEquation) (hK : Cited_KacDeterminant)
    (hset : MinimalSetting p p' r s b) {k N : ℕ} (hk : 1 ≤ k) (ε : Bool) {ns nb : ℕ}
    (hns : ellOrb p p' r s ε k = ns) (hnb : ellOrb p p' r s (!ε) k = nb) (hlt : ns < nb)
    (hsN : ns ≤ N) (xs : Nat.Partition ns → ℂ) (xb : Nat.Partition nb → ℂ)
    (hxs : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) ns xs) ns)
    (hxb : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) nb xb) nb)
    (hγ : jform (kacC b) (kacH r s b) ns k xs xs ≠ 0)
    (hdets : ∀ M : ℕ, M ≤ N - ns → (gram (kacC b) (kacH r s b + (ns : ℂ)) M).det ≠ 0)
    (hdetb : nb ≤ N → (gram (kacC b) (kacH r s b + (nb : ℂ)) (N - nb)).det ≠ 0) :
    topTermSph (Bsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N ns k xs +
      topTermSph (Bsph (cK (kacC b)) ΔK) (kacC b) (kacH r s b) N nb k xb ≠ 0 := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt', hb⟩ := id hset
  obtain ⟨hb0, -⟩ := inv_sq_min (by omega) (by omega) hb
  rw [topTermSph_eq_topR k xs (fun _ => hdets _ le_rfl), topTermSph_eq_topR k xb hdetb, ← map_add]
  -- the momenta
  set m : ℤ := nOrb p p' r s ε k with hm_def
  set mb : ℤ := nOrb p p' r s (!ε) k with hmb_def
  have hsum : m + mb = 2 * k * p * p' := nOrb_add_not ε k
  have hm2 := TT.nOrb_sq (p := p) (p' := p') hrp hsp ε hk
  have hmb2 := TT.nOrb_sq (p := p) (p' := p') hrp hsp (!ε) hk
  rw [← hm_def, hns] at hm2
  rw [← hmb_def, hnb] at hmb2
  have hkpp : (0 : ℤ) < 2 * k * p * p' := by positivity
  have hnsnb : (ns : ℤ) < nb := by exact_mod_cast hlt
  have hppos : (0 : ℤ) < 4 * p * p' := by positivity
  have hpos : 0 < m + mb := by rw [hsum]; exact hkpp
  have hmlt : m < mb := by
    nlinarith [hpos, hm2, hmb2, mul_lt_mul_of_pos_left hnsnb hppos]
  -- the point
  set a₃ : ℤ := (k : ℤ) * p * p' - p with ha₃
  set P : Fin 4 → ℂ := bpzWeights b (-(m : ℂ) / p) ((a₃ : ℂ) / p)
    (β4of b (-(m : ℂ) / p) ((a₃ : ℂ) / p)) with hP_def
  have hsumc : (m : ℂ) + mb = 2 * k * p * p' := by exact_mod_cast hsum
  have ha₃c : (a₃ : ℂ) = (k : ℂ) * p * p' - p := by rw [ha₃]; push_cast; ring
  obtain ⟨hP0, hP1, hP2, hP3⟩ := bpzWeights_min (by omega) (by omega) hb (m : ℂ) (a₃ : ℂ)
  rw [← hP_def] at hP0 hP1 hP2 hP3
  refine algebraMap_K4_ne P ?_
  rw [map_add, eval_topR k xs hsN (hdets _ le_rfl) P, hP0, hP1, hP2, hP3]
  -- (a) the higher branch vanishes at `P`
  have hbig : MvPolynomial.eval P (topR (kacC b) (kacH r s b) N nb k xb) = 0 := by
    unfold topR
    split_ifs with hbN
    · rw [map_mul, map_mul, map_mul, eval_piR, hP3, hP2]
      have hz := (pi_iii_any hH hF hU hset (!ε) hk hnb xb hxb ((m : ℂ) + p' - a₃ - p)
        (a₃ : ℂ)).2 (Or.inr (by rw [← hmb_def]; push_cast; linear_combination hsumc - 2 * ha₃c))
      rw [hz, zero_mul, zero_mul, zero_mul]
    · rw [map_zero]
  rw [hbig, add_zero]
  -- (b) the lower-branch factors do not vanish
  have hπ1 : piScalar (kacH r s b) xs (momC p p' ((m : ℂ) + p')) (momC p p' (2 * p' - p)) ≠ 0 := by
    intro h0
    obtain ⟨c₀, hc₀, hc⟩ := (pi_iii_any hH hF hU hset ε hk hns xs hxs _ _).1 h0
    rw [← hm_def] at hc₀
    have habs := le_abs_self c₀
    rcases hc with hc | hc
    · have : m + 3 * p' - p = c₀ := by
        have : ((m + 3 * p' - p : ℤ) : ℂ) = (c₀ : ℂ) := by push_cast; linear_combination hc
        exact_mod_cast this
      linarith
    · have : m - p' + p = c₀ := by
        have : ((m - p' + p : ℤ) : ℂ) = (c₀ : ℂ) := by push_cast; linear_combination hc
        exact_mod_cast this
      linarith
  have hπ2 : piScalar (kacH r s b) xs (momC p p' ((m : ℂ) + p' - a₃ - p)) (momC p p' (a₃ : ℂ))
      ≠ 0 := by
    intro h0
    obtain ⟨c₀, hc₀, hc⟩ := (pi_iii_any hH hF hU hset ε hk hns xs hxs _ _).1 h0
    rw [← hm_def] at hc₀
    have habs := le_abs_self c₀
    have habs' := neg_le_abs c₀
    rcases hc with hc | hc
    · have : m + p' - p = c₀ := by
        have : ((m + p' - p : ℤ) : ℂ) = (c₀ : ℂ) := by
          push_cast; linear_combination hc
        exact_mod_cast this
      linarith
    · have : m + p' - 2 * a₃ - p = c₀ := by
        have : ((m + p' - 2 * a₃ - p : ℤ) : ℂ) = (c₀ : ℂ) := by
          push_cast; linear_combination hc
        exact_mod_cast this
      rw [ha₃] at this
      linarith
  -- (c) the block coefficient at `P`
  have hμ : kacH r s b + (ns : ℂ) = wtB b (-(m : ℂ) / p) := by
    rw [kacH_min_add (by omega) (by omega) hb r s ns hm2, wtB_neg_min (by omega) (by omega) hb]
    unfold momC
    push_cast
    ring
  have hdet' : ∀ j ≤ N - ns, (gram (kacC b) (wtB b (-(m : ℂ) / p)) j).det ≠ 0 := by
    intro j hj
    rw [← hμ]
    exact hdets j hj
  have hB := block_point b (-(m : ℂ) / p) ((a₃ : ℂ) / p) hBPZ hK hb0 (N - ns) hdet' (N - ns) le_rfl
  rw [← hP_def, ← hμ] at hB
  have hBne : blockAt (kacC b) (kacH r s b + (ns : ℂ)) P (N - ns) ≠ 0 := by
    rw [hB]
    exact gSeq_ne_zero fun i _ => kappa_ne_nat hp (by omega) hcop hk hb i
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hπ2 hπ1) (inv_ne_zero hγ)) hBne

end Point

/-- Theorem 5.4 (sphere/paper.tex l.1607–1615, proof l.1617–1691).
Paper label: thm:sharp-B -/
theorem thm_sharp_B_of_cited (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) (hBPZ : Cited_BPZEquation) (hK : Cited_KacDeterminant) :
    Stmt_thm_sharp_B := by
  intro p p' r s b hset N hN
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  obtain ⟨wp, wm, hsing, hjan, -, -⟩ :=
    thm_jantzen_smith hJ p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hT : TopLayerSetting p p' r s b wp wm := ⟨hsing, hjan⟩
  have hle := (thm_jantzen_bound_of_cited hJ p p' r s b hset N).1
  rcases Nat.eq_zero_or_pos (jDepth p p' r s N) with h0 | hk
  · rw [h0] at hle ⊢
    exact Nat.le_zero.1 hle
  obtain ⟨hN1, hN2⟩ := jDepth_range hp hp' hr hrp hs hsp hk
  generalize jDepth p p' r s N = k at hle hk hN1 hN2 ⊢
  have top := thm_top_layer_of_cited hI p p' r s b hset wp wm hT k N hk hN1 hN2
  have hcp : pbwCoord (ellPlus p p' r s k) (comp (ellPlus p p' r s k) (wp k)) = wp k :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsing k hk).1.2.1)
  have hcm : pbwCoord (ellMinus p p' r s k) (comp (ellMinus p p' r s k) (wm k)) = wm k :=
    pbwCoord_comp_of_mem_level (mem_level_of_L_zero (hsing k hk).2.2.1)
  obtain ⟨hpo, hpc⟩ := (top.2.2.2 _ _ hcp hcm).1
  have tp := top.2.1 _ hcp
  have tm := top.2.2.1 _ hcm
  have hsp' : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellPlus p p' r s k)
      (comp (ellPlus p p' r s k) (wp k))) (ellPlus p p' r s k) := by
    rw [hcp]; exact (hsing k hk).1
  have hsm' : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellMinus p p' r s k)
      (comp (ellMinus p p' r s k) (wm k))) (ellMinus p p' r s k) := by
    rw [hcm]; exact (hsing k hk).2
  have hplus : ellOrb p p' r s true k = ellPlus p p' r s k := by
    rw [ellOrb, if_neg (by omega)]; rfl
  have hminus : ellOrb p p' r s (!true) k = ellMinus p p' r s k := by
    rw [ellOrb, if_neg (by omega)]; rfl
  have hminus' : ellOrb p p' r s false k = ellMinus p p' r s k := by
    rw [ellOrb, if_neg (by omega)]; rfl
  have hplus' : ellOrb p p' r s (!false) k = ellPlus p p' r s k := by
    rw [ellOrb, if_neg (by omega)]; rfl
  refine poleOrder_eq_of_ppCoeff_ne hpo ?_
  rw [hpc]
  have hne := ellPlus_ne_ellMinus hcop hr hrp hsp hlt hk
  rcases lt_or_gt_of_ne hne with hpm | hmp
  · have hpN : ellPlus p p' r s k ≤ N := (min_eq_left hpm.le).symm ▸ hN1
    exact sharp_pair_ne hH hF hU hBPZ hK hset hk true hplus hminus hpm hpN _ _ hsp' hsm'
      (tp hpN).1 (tp hpN).2 (fun h => (tm h).2 _ le_rfl)
  · have hmN : ellMinus p p' r s k ≤ N := (min_eq_right hmp.le).symm ▸ hN1
    rw [add_comm]
    exact sharp_pair_ne hH hF hU hBPZ hK hset hk false hminus' hplus' hmp hmN _ _ hsm' hsp'
      (tm hmN).1 (tm hmN).2 (fun h => (tp h).2 _ le_rfl)

example (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) (hBPZ : Cited_BPZEquation) (hK : Cited_KacDeterminant) :
    Stmt_thm_sharp_B := thm_sharp_B_of_cited hJ hI hH hF hU hBPZ hK

end Virasoro.Sphere
