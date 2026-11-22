import Virasoro.Proofs.Sec6TwoTermSwap
import Virasoro.Proofs.Sec6TauFactor
import Virasoro.Proofs.Sec5Sharp
import Virasoro.Proofs.SingularOnes

/-!
# Proposition 6.9: the rational model of `P_N` (paper.tex l.1428–1446)

"Normalize each `w^±_k` to `L_{-1}^{ℓ^±_k}`-coefficient `1`": with `a = x(1^ℓ) ≠ 0` (Lemma 5.7),
`τ(x) = a² τ(x/a)`, and `τ(x/a)` is the product of the `𝒫_{R,S}(b⋆,d)` (l.1433–1443).  At
`b⋆² = −p'/p` every factor of `𝒫_{R,S}` is `d_x − d` with `d_x = (x² − (p'−p)²)/(4pp')`,
`x = p'a' ∓ pl`, a rational number, and `H_M(c⋆, μ^±_k, d)` is a rational polynomial in `d`.  With
`γ^±_k = [d^k]τ^±_k/(c_k(±ρ)^k)` (Proposition 6.7), `P_N = c_k ρ^k · coreP`, where
`coreP = τ⁺/[d^k]τ⁺ · H⁺ + (−1)^k τ⁻/[d^k]τ⁻ · H⁻` over `ℚ`.
-/

namespace Virasoro

namespace TT

open Polynomial Verma Finset

/-- `d_x = (x² − (p'−p)²)/(4pp')` (paper.tex l.1431). -/
def dQ (p p' : ℕ) (x : ℤ) : ℚ := ((x : ℚ) ^ 2 - ((p' : ℚ) - p) ^ 2) / (4 * p * p')

/-- `𝒫_{R,S}(b⋆, d)` over `ℚ` (paper.tex l.1441–1443). -/
noncomputable def PQ (p p' R S : ℕ) : ℚ[X] :=
  ∏ a ∈ oddsBelow R, ∏ l ∈ oddsBelow S,
    (C (dQ p p' ((a : ℤ) * p' - (l : ℤ) * p)) - X) * (C (dQ p p' ((a : ℤ) * p' + (l : ℤ) * p)) - X)

theorem genPpoly_min {p p' : ℕ} {b : ℂ} (hp : 0 < p) (hp' : 0 < p') (hb : b ^ 2 = -(p' : ℂ) / p)
    (R S : ℕ) : genPpoly R S b = (PQ p p' R S).map (Rat.castHom ℂ) := by
  obtain ⟨hb0, hbi⟩ := inv_sq_min hp hp' hb
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
  have h1 : (b + b⁻¹) ^ 2 = b ^ 2 + 2 + b⁻¹ ^ 2 := by
    field_simp
    ring
  have e1 : ∀ a l : ℕ, ((b + b⁻¹) ^ 2 - ((a : ℂ) * b + (l : ℂ) * b⁻¹) ^ 2) / 4 =
      ((dQ p p' ((a : ℤ) * p' - (l : ℤ) * p) : ℚ) : ℂ) := by
    intro a l
    have h2 : ((a : ℂ) * b + (l : ℂ) * b⁻¹) ^ 2 =
        (a : ℂ) ^ 2 * b ^ 2 + 2 * a * l + (l : ℂ) ^ 2 * b⁻¹ ^ 2 := by
      field_simp
      ring
    rw [h1, h2, hb, hbi, dQ]
    push_cast
    field_simp
    ring
  have e2 : ∀ a l : ℕ, ((b + b⁻¹) ^ 2 - ((a : ℂ) * b - (l : ℂ) * b⁻¹) ^ 2) / 4 =
      ((dQ p p' ((a : ℤ) * p' + (l : ℤ) * p) : ℚ) : ℂ) := by
    intro a l
    have h2 : ((a : ℂ) * b - (l : ℂ) * b⁻¹) ^ 2 =
        (a : ℂ) ^ 2 * b ^ 2 - 2 * a * l + (l : ℂ) ^ 2 * b⁻¹ ^ 2 := by
      field_simp
      ring
    rw [h1, h2, hb, hbi, dQ]
    push_cast
    field_simp
    ring
  unfold genPpoly PQ
  rw [Polynomial.map_prod]
  refine prod_congr rfl fun a _ => ?_
  rw [Polynomial.map_prod]
  refine prod_congr rfl fun l _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_C, Polynomial.map_X, eq_ratCast, eq_ratCast, e1, e2]

/-- `τ^ε_k` over `ℚ` (paper.tex l.1437–1440). -/
noncomputable def tauQ (p p' r s : ℕ) (ε : Bool) (k : ℕ) : ℚ[X] :=
  if k % 2 = 1 then
    (if ε then PQ p p' (r + k / 2 * p) (s + k / 2 * p')
      else PQ p p' ((k / 2 + 1) * p - r) ((k / 2 + 1) * p' - s))
  else PQ p p' (r + (k / 2 - 1) * p) (s + (k / 2 - 1) * p') *
    (if ε then PQ p p' ((k - 1) * p + r) (p' - s) else PQ p p' (p - r) ((k - 1) * p' + s))

theorem tau_min (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) {p p' r s : ℕ}
    {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool) {k : ℕ} (hk : 1 ≤ k)
    (x : Nat.Partition (ellOrb p p' r s ε k) → ℂ) (hx1 : x (onesPartition _) = 1)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellOrb p p' r s ε k) x)
      (ellOrb p p' r s ε k)) :
    torusPolyForm (kacC b) (kacH r s b) x = (tauQ p p' r s ε k).map (Rat.castHom ℂ) := by
  obtain ⟨hp, hp', -, -, -, -, -, -, hb⟩ := id hset
  obtain ⟨h1, h2⟩ := sub_tau_factorization hH hU p p' r s b hset k ε hk x hx1 hx
  unfold tauQ
  by_cases hodd : k % 2 = 1
  · rw [h1 hodd, if_pos hodd]
    split_ifs <;> exact genPpoly_min (by omega) (by omega) hb _ _
  · rw [h2 (by omega), if_neg hodd, Polynomial.map_mul, genPpoly_min (by omega) (by omega) hb]
    split_ifs <;> rw [genPpoly_min (by omega) (by omega) hb]

/-- `τ(x) = x(1^ℓ)² τ(x/x(1^ℓ))`, with `x(1^ℓ) ≠ 0` (Lemma 5.7). -/
theorem tau_norm (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) {p p' r s : ℕ}
    {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool) {k : ℕ} (hk : 1 ≤ k) {n : ℕ}
    (hn : ellOrb p p' r s ε k = n) (hn1 : 1 ≤ n) (x : Nat.Partition n → ℂ)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) n x) n) :
    torusPolyForm (kacC b) (kacH r s b) x =
      C (x (onesPartition n) ^ 2) * (tauQ p p' r s ε k).map (Rat.castHom ℂ) := by
  subst hn
  have ha := sub_singular_ones_coeff _ _ _ hn1 x hx
  obtain ⟨a, ha_def⟩ : ∃ a, a = x (onesPartition (ellOrb p p' r s ε k)) := ⟨_, rfl⟩
  rw [← ha_def] at ha ⊢
  have hx' : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellOrb p p' r s ε k)
      (a⁻¹ • x)) (ellOrb p p' r s ε k) := by
    rw [map_smul]
    exact isSingular_smul hx (inv_ne_zero ha)
  have h1 : (a⁻¹ • x) (onesPartition _) = 1 := by
    rw [Pi.smul_apply, smul_eq_mul, ← ha_def, inv_mul_cancel₀ ha]
  have ht := tau_min hH hU hset ε hk (a⁻¹ • x) h1 hx'
  have hxa : x = a • (a⁻¹ • x) := by rw [smul_smul, mul_inv_cancel₀ ha, one_smul]
  rw [← ht]
  refine Polynomial.funext fun d => ?_
  rw [eval_mul, eval_C, torusPolyForm_eval, torusPolyForm_eval]
  conv_lhs => rw [hxa]
  rw [torusForm_smul]

/-! ### The levels and momenta -/

theorem nOrb_sq {p p' r s : ℕ} (hrp : r < p) (hsp : s < p') (ε : Bool) {k : ℕ} (hk : 1 ≤ k) :
    nOrb p p' r s ε k ^ 2 =
      ((p' : ℤ) * r - (p : ℤ) * s) ^ 2 + 4 * p * p' * (ellOrb p p' r s ε k : ℤ) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have h2 : 2 * j % 2 = 0 := by omega
    simp only [nOrb, ellOrb, h2, if_true, show 2 * j ≠ 0 by omega, if_false]
    cases ε
    · simp only [Bool.false_eq_true, if_false]
      rw [ellMinus_even_cast hrp j]
      push_cast
      ring
    · simp only [if_true]
      rw [ellPlus_even_cast hsp j]
      push_cast
      ring
  · have h2 : (2 * j + 1) % 2 = 1 := by omega
    simp only [nOrb, ellOrb, h2, show (1 : ℕ) ≠ 0 by omega, show 2 * j + 1 ≠ 0 by omega, if_false]
    cases ε
    · simp only [Bool.false_eq_true, if_false]
      rw [ellMinus_odd_cast hrp hsp j]
      push_cast
      ring
    · simp only [if_true]
      rw [ellPlus_odd_cast j]
      push_cast
      ring

theorem ellOrb_pos {p p' r s : ℕ} (hp : 2 ≤ p) (hp' : 2 ≤ p') (hr : 0 < r) (hrp : r < p)
    (hs : 0 < s) (hsp : s < p') (ε : Bool) {k : ℕ} (hk : 1 ≤ k) : 1 ≤ ellOrb p p' r s ε k := by
  have hpp : (0 : ℤ) ≤ (p : ℤ) * p' := by positivity
  have key : (1 : ℤ) ≤ (ellOrb p p' r s ε k : ℤ) := by
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · have hj : (1 : ℤ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
      have hjp := mul_le_mul_of_nonneg_right hj hpp
      rw [ellOrb, if_neg (by omega)]
      cases ε
      · simp only [Bool.false_eq_true, if_false]
        rw [ellMinus_even_cast hrp j]
        have h1 : (1 : ℤ) ≤ (j : ℤ) * p * p' - ((p' : ℤ) * r - (p : ℤ) * s) := by
          have : (r : ℤ) + 1 ≤ p := by exact_mod_cast hrp
          nlinarith
        nlinarith
      · simp only [if_true]
        rw [ellPlus_even_cast hsp j]
        have h1 : (1 : ℤ) ≤ (j : ℤ) * p * p' + ((p' : ℤ) * r - (p : ℤ) * s) := by
          have : (s : ℤ) + 1 ≤ p' := by exact_mod_cast hsp
          have : (1 : ℤ) ≤ r := by exact_mod_cast hr
          nlinarith
        nlinarith
    · rw [ellOrb, if_neg (by omega)]
      cases ε
      · simp only [Bool.false_eq_true, if_false]
        rw [ellMinus_odd_cast hrp hsp j]
        have h1 : (1 : ℤ) ≤ ((j : ℤ) + 1) * p - r := by
          have : (r : ℤ) + 1 ≤ p := by exact_mod_cast hrp
          nlinarith
        have h2 : (1 : ℤ) ≤ ((j : ℤ) + 1) * p' - s := by
          have : (s : ℤ) + 1 ≤ p' := by exact_mod_cast hsp
          nlinarith
        nlinarith
      · simp only [if_true]
        rw [ellPlus_odd_cast j]
        have h1 : (1 : ℤ) ≤ (r : ℤ) + j * p := by
          have : (1 : ℤ) ≤ r := by exact_mod_cast hr
          nlinarith
        have h2 : (1 : ℤ) ≤ (s : ℤ) + j * p' := by
          have : (1 : ℤ) ≤ s := by exact_mod_cast hs
          nlinarith
        nlinarith
  exact_mod_cast key

/-! ### The rational polynomial -/

/-- `c⋆ = 1 − 6(p'−p)²/(pp')`. -/
def cs (p p' : ℕ) : ℚ := 1 - 6 * ((p' : ℚ) - p) ^ 2 / (p * p')

/-- `μ^ε_k = d_{n^ε_k}`. -/
def muQ (p p' r s : ℕ) (ε : Bool) (k : ℕ) : ℚ := dQ p p' (nOrb p p' r s ε k)

/-- `P_N/(c_k ρ^k) = τ⁺/[d^k]τ⁺ · H⁺ + (−1)^k τ⁻/[d^k]τ⁻ · H⁻` over `ℚ`. -/
noncomputable def coreP (p p' r s k N : ℕ) : ℚ[X] :=
  tauQ p p' r s true k * C ((tauQ p p' r s true k).coeff k)⁻¹ *
      HpolyD (cs p p') (muQ p p' r s true k) (N - ellPlus p p' r s k) +
    C ((-1 : ℚ) ^ k) * (tauQ p p' r s false k * C ((tauQ p p' r s false k).coeff k)⁻¹ *
      HpolyD (cs p p') (muQ p p' r s false k) (N - ellMinus p p' r s k))

theorem H_min {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool) {k : ℕ}
    (hk : 1 ≤ k) (M : ℕ) :
    HpolyD (kacC b) (kacH r s b + (ellOrb p p' r s ε k : ℂ)) M =
      (HpolyD (cs p p') (muQ p p' r s ε k) M).map (Rat.castHom ℂ) := by
  obtain ⟨hp, hp', -, -, hrp, -, hsp, -, hb⟩ := id hset
  rw [kacC_min (by omega) (by omega) hb,
    kacH_min_add (by omega) (by omega) hb r s _ (nOrb_sq hrp hsp ε hk)]
  change HpolyD (Rat.castHom ℂ _) (Rat.castHom ℂ _) M = _
  rw [HpolyD_map]
  rfl

theorem det_min {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) (ε : Bool) {k : ℕ}
    (hk : 1 ≤ k) (M : ℕ)
    (h : (gram (kacC b) (kacH r s b + (ellOrb p p' r s ε k : ℂ)) M).det ≠ 0) :
    (gram (cs p p') (muQ p p' r s ε k) M).det ≠ 0 := by
  obtain ⟨hp, hp', -, -, hrp, -, hsp, -, hb⟩ := id hset
  intro h0
  apply h
  rw [kacC_min (by omega) (by omega) hb,
    kacH_min_add (by omega) (by omega) hb r s _ (nOrb_sq hrp hsp ε hk)]
  change (gram (Rat.castHom ℂ (cs p p')) (Rat.castHom ℂ (muQ p p' r s ε k)) M).det = 0
  rw [gram_map]
  exact (RingHom.map_det (Rat.castHom ℂ) (gram (cs p p') (muQ p p' r s ε k) M)).symm.trans
    (by rw [h0, map_zero])

/-! ### Reduction of `P_N ≢ 0` to `coreP ≠ 0` -/

theorem ellOrb_true {p p' r s k : ℕ} (hk : 1 ≤ k) : ellOrb p p' r s true k = ellPlus p p' r s k := by
  rw [ellOrb, if_neg (by omega), if_pos rfl]

theorem ellOrb_false {p p' r s k : ℕ} (hk : 1 ≤ k) :
    ellOrb p p' r s false k = ellMinus p p' r s k := by
  rw [ellOrb, if_neg (by omega)]
  rfl

/-- The hypotheses under which `coreP ≠ 0` is proved. -/
def CoreHyp (p p' r s k N : ℕ) : Prop :=
  2 ≤ p ∧ 2 ≤ p' ∧ Nat.Coprime p p' ∧ 0 < r ∧ r < p ∧ 0 < s ∧ s < p' ∧
    p' * r + p * s < p * p' ∧ (∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ∣ p') ∧ 1 ≤ k ∧
    max (ellPlus p p' r s k) (ellMinus p p' r s k) < N ∧ N < ellMin p p' r s (k + 1) ∧
    (∀ ε : Bool, ∀ M, M ≤ N - ellOrb p p' r s ε k →
      (gram (cs p p') (muQ p p' r s ε k) M).det ≠ 0) ∧
    (∀ ε : Bool, ∀ n < k, (tauQ p p' r s ε k).coeff n = 0) ∧
    (∀ ε : Bool, (tauQ p p' r s ε k).coeff k ≠ 0)

theorem coeff_tau_norm {a : ℂ} {T : ℚ[X]} {τ : ℂ[X]} (hτ : τ = C (a ^ 2) * T.map (Rat.castHom ℂ))
    (n : ℕ) : τ.coeff n = a ^ 2 * (T.coeff n : ℂ) := by
  rw [hτ, coeff_C_mul, coeff_map, eq_ratCast]

/-- `P_N ≢ 0` from `coreP ≠ 0` (paper.tex l.1428–1446). -/
theorem two_term_odd_of_core (hI : Cited_VermaHomInjective) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (h67 : Stmt_prop_layer_coefficients)
    (hcore : ∀ p p' r s k N : ℕ, CoreHyp p p' r s k N → coreP p p' r s k N ≠ 0) :
    Stmt_sub_two_term_nonzero_odd := by
  intro p p' r s b hset hodd wp wm hT k N hk hN1 hN2 xp xm hxp hxm
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  have hpN : ellPlus p p' r s k ≤ N := (le_max_left _ _).trans hN1.le
  have hmN : ellMinus p p' r s k ≤ N := (le_max_right _ _).trans hN1.le
  have hmin : ellMin p p' r s k ≤ N := (min_le_left _ _).trans hpN
  have top := thm_top_layer_of_cited hI p p' r s b hset wp wm hT k N hk hmin hN2
  obtain ⟨hγp, hdp, -⟩ := top.2.1 xp hxp hpN
  obtain ⟨hγm, hdm, -⟩ := top.2.2.1 xm hxm hmN
  obtain ⟨l67p, l67m⟩ := h67 p p' r s b hset wp wm hT k hk
  obtain ⟨lp0, lpk, lpne⟩ := l67p xp hxp
  obtain ⟨lm0, lmk, lmne⟩ := l67m xm hxm
  have hsp' := (hT.1 k hk).1
  rw [← hxp] at hsp'
  have hsm' := (hT.1 k hk).2
  rw [← hxm] at hsm'
  have hτp := tau_norm hH hU hset true hk (ellOrb_true hk)
    ((ellOrb_true hk) ▸ ellOrb_pos hp hp' hr hrp hs hsp true hk) xp hsp'
  have hτm := tau_norm hH hU hset false hk (ellOrb_false hk)
    ((ellOrb_false hk) ▸ ellOrb_pos hp hp' hr hrp hs hsp false hk) xm hsm'
  have hap := sub_singular_ones_coeff _ _ _
    ((ellOrb_true hk) ▸ ellOrb_pos hp hp' hr hrp hs hsp true hk) xp hsp'
  have ham := sub_singular_ones_coeff _ _ _
    ((ellOrb_false hk) ▸ ellOrb_pos hp hp' hr hrp hs hsp false hk) xm hsm'
  have hHp := H_min hset true hk (N - ellPlus p p' r s k)
  have hHm := H_min hset false hk (N - ellMinus p p' r s k)
  rw [ellOrb_true hk] at hHp
  rw [ellOrb_false hk] at hHm
  -- the hypotheses of the rational statement
  have hdQ : ∀ ε : Bool, ∀ M, M ≤ N - ellOrb p p' r s ε k →
      (gram (cs p p') (muQ p p' r s ε k) M).det ≠ 0 := by
    intro ε M hM
    refine det_min hset ε hk M ?_
    cases ε
    · rw [ellOrb_false hk] at hM ⊢
      exact hdm M hM
    · rw [ellOrb_true hk] at hM ⊢
      exact hdp M hM
  have hc0 : ∀ ε : Bool, ∀ n < k, (tauQ p p' r s ε k).coeff n = 0 := by
    intro ε n hn
    cases ε
    · have := lm0 n hn
      rw [coeff_tau_norm hτm] at this
      exact_mod_cast (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 ham)
    · have := lp0 n hn
      rw [coeff_tau_norm hτp] at this
      exact_mod_cast (mul_eq_zero.1 this).resolve_left (pow_ne_zero 2 hap)
  have hck : ∀ ε : Bool, (tauQ p p' r s ε k).coeff k ≠ 0 := by
    intro ε
    cases ε
    · intro h0
      apply lmne
      rw [coeff_tau_norm hτm, h0, Rat.cast_zero, mul_zero]
    · intro h0
      apply lpne
      rw [coeff_tau_norm hτp, h0, Rat.cast_zero, mul_zero]
  have hc := hcore p p' r s k N ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hodd, hk, hN1, hN2, hdQ,
    hc0, hck⟩
  -- the identity `P_N = c_k ρ^k coreP`
  rw [topTerm_eq_poly _ _ k xp hpN hdp, topTerm_eq_poly _ _ k xm hmN hdm, ← map_add]
  refine (map_ne_zero_iff _ (IsFractionRing.injective ℂ[X] Kd)).2 ?_
  set ρ : ℂ := -((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p)) with hρ
  set κ : ℂ := (layerConst k : ℂ) * ρ ^ k with hκ
  rw [coeff_tau_norm hτp] at lpk lpne
  rw [coeff_tau_norm hτm] at lmk lmne
  have hTp : ((tauQ p p' r s true k).coeff k : ℂ) ≠ 0 := by exact_mod_cast hck true
  have hTm : ((tauQ p p' r s false k).coeff k : ℂ) ≠ 0 := by exact_mod_cast hck false
  have hκ0 : κ ≠ 0 := by
    intro h0
    apply lpne
    rw [lpk, mul_assoc, ← hκ, h0, mul_zero]
  have eγp : jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp =
      xp (onesPartition _) ^ 2 * ((tauQ p p' r s true k).coeff k : ℂ) / κ := by
    rw [lpk, mul_assoc, ← hκ]
    exact (mul_div_cancel_right₀ _ hκ0).symm
  have eγm : jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm =
      xm (onesPartition _) ^ 2 * ((tauQ p p' r s false k).coeff k : ℂ) / ((-1) ^ k * κ) := by
    have h1 : (-ρ) ^ k = (-1) ^ k * ρ ^ k := by rw [neg_eq_neg_one_mul, mul_pow]
    have h2 : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [lmk, h1, show jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm *
        (layerConst k : ℂ) * ((-1) ^ k * ρ ^ k) =
        jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm * ((-1) ^ k * κ) by
      rw [hκ]; ring]
    exact (mul_div_cancel_right₀ _ (mul_ne_zero h2 hκ0)).symm
  have key : torusPolyForm (kacC b) (kacH r s b) xp *
        C (jform (kacC b) (kacH r s b) (ellPlus p p' r s k) k xp xp)⁻¹ *
        HpolyD (kacC b) (kacH r s b + (ellPlus p p' r s k : ℂ)) (N - ellPlus p p' r s k) +
      torusPolyForm (kacC b) (kacH r s b) xm *
        C (jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm)⁻¹ *
        HpolyD (kacC b) (kacH r s b + (ellMinus p p' r s k : ℂ)) (N - ellMinus p p' r s k) =
      C κ * (coreP p p' r s k N).map (Rat.castHom ℂ) := by
    rw [hτp, hτm, hHp, hHm, eγp, eγm, coreP]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, eq_ratCast,
      Rat.cast_inv, Rat.cast_pow, Rat.cast_neg, Rat.cast_one]
    have h2 : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h3 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
    refine Polynomial.funext fun d => ?_
    simp only [eval_add, eval_mul, eval_C]
    field_simp
  rw [key]
  exact mul_ne_zero (C_ne_zero.2 hκ0) ((Polynomial.map_ne_zero_iff (Rat.castHom ℂ).injective).2 hc)

end TT

end Virasoro
