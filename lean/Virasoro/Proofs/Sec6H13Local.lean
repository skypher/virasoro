import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Proposition 6.8(i): the local step (paper.tex l.1275–1291)

The paper works in `𝒪_𝔭`, the localization of `ℤ_(ℓ)[b,b⁻¹,α][q₀]` at a prime above `ℓ`, and
uses: an element of `𝒪_𝔭` times a unit is in `𝒪_𝔭`, and
`𝒪_𝔭 ∩ ℚ[t,Y] = ℤ_(ℓ)[t,Y]` because `t` and `Y` are algebraically independent modulo `𝔭`.

Here the field is `ℚ(s)(α)` with `q₀ = 1/s − s/2` and `t = −s²/2` (so that
`(t+1)² = −2q₀² t`, that is `c = 13 + 6t + 6/t = 1 − 12 q₀²`).  It contains `t`, `q₀`, `α` and
`Y = ½ t² α (α − 2q₀)`, which are all the quantities of l.1261–1291.  The ring
`ℤ[1/2][s,s⁻¹,α]` (`S0`) plays the part of the integral elements, and the reduction modulo `ℓ`,
`ℤ[s][α] → 𝔽_ℓ[s][α]`, plays the part of the reduction modulo `𝔭`.
-/

namespace Virasoro.H13Local

open Polynomial

/-- `ℚ(s)(α)`. -/
abbrev K0 : Type := RatFunc (RatFunc ℚ)

/-- `ℤ[s][α]`. -/
abbrev PZ : Type := Polynomial (Polynomial ℤ)

/-- `ℤ[s][α] → ℚ(s)(α)`. -/
noncomputable def iota : PZ →+* K0 :=
  (algebraMap (RatFunc ℚ)[X] K0).comp
    (mapRingHom ((algebraMap ℚ[X] (RatFunc ℚ)).comp (mapRingHom (Int.castRingHom ℚ))))

theorem iota_injective : Function.Injective iota := by
  have h1 : Function.Injective ((algebraMap ℚ[X] (RatFunc ℚ)).comp
      (mapRingHom (Int.castRingHom ℚ))) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective ℚ[X] (RatFunc ℚ)).comp
      (Polynomial.map_injective _ Int.cast_injective)
  unfold iota
  rw [RingHom.coe_comp]
  exact (IsFractionRing.injective (RatFunc ℚ)[X] K0).comp (Polynomial.map_injective _ h1)

/-- `s`. -/
noncomputable def sK : K0 := iota (C X)

/-- `α`. -/
noncomputable def aK : K0 := iota X

/-- `2s ∈ ℤ[s][α]`. -/
noncomputable def ts : PZ := C (C 2 * X)

theorem iota_CC (z : ℤ) : iota (C (C z)) = (z : K0) := by
  simp [iota]

theorem iota_ts : iota ts = 2 * sK := by
  have h := iota_CC 2
  rw [ts, C_mul, map_mul, h, sK]
  norm_num

theorem sK_ne_zero : sK ≠ 0 := by
  unfold sK
  rw [Ne, map_eq_zero_iff _ iota_injective]
  exact C_ne_zero.2 X_ne_zero

theorem iota_ts_ne_zero : iota ts ≠ 0 := by
  rw [iota_ts]
  exact mul_ne_zero two_ne_zero sK_ne_zero

/-- `t = −s²/2`. -/
noncomputable def tK : K0 := -(sK ^ 2) / 2

/-- `q₀ = 1/s − s/2`. -/
noncomputable def qK : K0 := sK⁻¹ - sK / 2

/-- `Δ = ½ α (α − 2q₀)`. -/
noncomputable def DK : K0 := 1 / 2 * aK ^ 2 - qK * aK

/-- `Y = t² Δ`. -/
noncomputable def YK : K0 := tK ^ 2 * DK

/-- `8 s³ Y = s⁷ α² + (s⁸ − 2 s⁶) α`. -/
noncomputable def yts : PZ := C (X ^ 7) * X ^ 2 + C (X ^ 8 - C 2 * X ^ 6) * X

theorem tK_mul : tK * iota ts = iota (C (-(X ^ 3))) := by
  rw [iota_ts]
  have : iota (C (-(X ^ 3))) = -(sK ^ 3) := by simp [sK]
  rw [this, tK]
  ring

theorem YK_mul : YK * iota ts ^ 3 = iota yts := by
  have hs := sK_ne_zero
  rw [iota_ts]
  have : iota yts = sK ^ 7 * aK ^ 2 + (sK ^ 8 - 2 * sK ^ 6) * aK := by
    have h := iota_CC 2
    simp only [yts, map_add, map_mul, map_sub, map_pow, C_mul, C_sub, C_pow, h, sK, aK]
    norm_num
  rw [this, YK, DK, tK, qK]
  field_simp
  ring

/-- The integral elements `ℤ[1/2][s, s⁻¹, α]`. -/
noncomputable def S0 : Subring K0 where
  carrier := {x | ∃ (n : ℕ) (a : PZ), x * iota ts ^ n = iota a}
  mul_mem' := by
    rintro x y ⟨n, a, ha⟩ ⟨m, b, hb⟩
    exact ⟨n + m, a * b, by rw [map_mul, ← ha, ← hb]; ring⟩
  one_mem' := ⟨0, 1, by simp⟩
  add_mem' := by
    rintro x y ⟨n, a, ha⟩ ⟨m, b, hb⟩
    exact ⟨n + m, a * ts ^ m + b * ts ^ n, by
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hb]; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro x ⟨n, a, ha⟩
    exact ⟨n, -a, by rw [map_neg, ← ha]; ring⟩

theorem iota_mem (a : PZ) : iota a ∈ S0 := ⟨0, a, by simp⟩

theorem half_mem : (1 / 2 : K0) ∈ S0 :=
  ⟨1, C X, by rw [pow_one, iota_ts]; show _ = sK; ring⟩

theorem sK_mem : sK ∈ S0 := iota_mem _

theorem aK_mem : aK ∈ S0 := iota_mem _

theorem sK_inv_mem : sK⁻¹ ∈ S0 :=
  ⟨1, 2, by rw [pow_one, iota_ts, map_ofNat]; field_simp [sK_ne_zero]⟩

theorem qK_mem : qK ∈ S0 := by
  have h : qK = sK⁻¹ - sK * (1 / 2) := by rw [qK]; ring
  rw [h]
  exact S0.sub_mem sK_inv_mem (S0.mul_mem sK_mem half_mem)

theorem tK_mem : tK ∈ S0 := by
  have h : tK = -(sK ^ 2 * (1 / 2)) := by rw [tK]; ring
  rw [h]
  exact S0.neg_mem (S0.mul_mem (S0.pow_mem sK_mem 2) half_mem)

theorem tK_ne_zero : tK ≠ 0 := by
  rw [tK]
  exact div_ne_zero (neg_ne_zero.2 (pow_ne_zero _ sK_ne_zero)) two_ne_zero

theorem tK_inv_mem : tK⁻¹ ∈ S0 := by
  have h : tK⁻¹ = -(2 * sK⁻¹ ^ 2) := by
    rw [tK]
    field_simp [sK_ne_zero]
  rw [h]
  refine S0.neg_mem (S0.mul_mem ?_ (S0.pow_mem sK_inv_mem 2))
  rw [show (2 : K0) = 1 + 1 by norm_num]
  exact S0.add_mem S0.one_mem S0.one_mem

theorem DK_mem : DK ∈ S0 :=
  S0.sub_mem (S0.mul_mem half_mem (S0.pow_mem aK_mem 2)) (S0.mul_mem qK_mem aK_mem)

variable (ℓ : ℕ)

/-- Reduction modulo `ℓ`: `ℤ[s][α] → 𝔽_ℓ[s][α]`. -/
noncomputable def red : PZ →+* Polynomial (Polynomial (ZMod ℓ)) :=
  mapRingHom (mapRingHom (Int.castRingHom (ZMod ℓ)))

/-- The elements of `ℤ[1/2][s,s⁻¹,α]` with nonzero reduction modulo `ℓ`: the units at `𝔭`. -/
def Unit0 (x : K0) : Prop :=
  ∃ (n : ℕ) (a : PZ), x * iota ts ^ n = iota a ∧ red ℓ a ≠ 0

variable [hℓ : Fact ℓ.Prime]

theorem two_ne_zero_zmod (h2 : ℓ ≠ 2) : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 h')

theorem red_ts : red ℓ ts = C (C 2 * X) := by
  simp [red, ts]
  exact (map_ofNat C 2).symm

theorem red_ts_ne_zero (h2 : ℓ ≠ 2) : red ℓ ts ≠ 0 := by
  rw [red_ts]
  exact C_ne_zero.2 (mul_ne_zero (C_ne_zero.2 (two_ne_zero_zmod ℓ h2)) X_ne_zero)

theorem Unit0.mul {x y : K0} (hx : Unit0 ℓ x) (hy : Unit0 ℓ y) : Unit0 ℓ (x * y) := by
  obtain ⟨n, a, ha, ha'⟩ := hx
  obtain ⟨m, b, hb, hb'⟩ := hy
  exact ⟨n + m, a * b, by rw [map_mul, ← ha, ← hb]; ring, by
    rw [map_mul]; exact mul_ne_zero ha' hb'⟩

theorem Unit0.prod {ι' : Type*} (s : Finset ι') (f : ι' → K0) (h : ∀ i ∈ s, Unit0 ℓ (f i)) :
    Unit0 ℓ (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, by simp, by simp⟩
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul ℓ
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Unit0.pow {x : K0} (hx : Unit0 ℓ x) (k : ℕ) : Unit0 ℓ (x ^ k) := by
  induction k with
  | zero => exact ⟨0, 1, by simp, by simp⟩
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul ℓ hx

/-! ### Algebraic independence of `t`, `Y` modulo `ℓ` -/

/-- `t` modulo `ℓ`: `−s²/2`. -/
noncomputable def tbar : Polynomial (ZMod ℓ) := C ((2 : ZMod ℓ)⁻¹) * -(X ^ 2)

/-- `Y` modulo `ℓ`: `(s⁴ α² + (s⁵ − 2 s³) α)/8`. -/
noncomputable def Ybar : Polynomial (Polynomial (ZMod ℓ)) :=
  C (C ((8 : ZMod ℓ)⁻¹)) * (C (X ^ 4) * X ^ 2 + C (X ^ 5 - C 2 * X ^ 3) * X)

/-- `𝔽_ℓ[t,Y] → 𝔽_ℓ[s][α]`. -/
noncomputable def evbar : MvPolynomial (Fin 2) (ZMod ℓ) →+* Polynomial (Polynomial (ZMod ℓ)) :=
  MvPolynomial.eval₂Hom (C.comp C) ![C (tbar ℓ), Ybar ℓ]

/-- `𝔽_ℓ[t,Y] → 𝔽_ℓ[t][Y]`. -/
noncomputable def theta : MvPolynomial (Fin 2) (ZMod ℓ) →+* Polynomial (Polynomial (ZMod ℓ)) :=
  MvPolynomial.eval₂Hom (C.comp C) ![C X, X]

noncomputable def thetaInv : Polynomial (Polynomial (ZMod ℓ)) →+* MvPolynomial (Fin 2) (ZMod ℓ) :=
  eval₂RingHom (eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)) (MvPolynomial.X 1)

theorem theta_injective : Function.Injective (theta ℓ) := by
  have h : (thetaInv ℓ).comp (theta ℓ) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [theta, thetaInv]
    · fin_cases i <;> simp [theta, thetaInv]
  intro a b hab
  have := congrArg (thetaInv ℓ) hab
  rwa [← RingHom.comp_apply, ← RingHom.comp_apply, h] at this

/-- `p(t) ↦ p(−s²/2)`. -/
noncomputable def phis : Polynomial (ZMod ℓ) →+* Polynomial (ZMod ℓ) := eval₂RingHom C (tbar ℓ)

theorem phis_injective (h2 : ℓ ≠ 2) : Function.Injective (phis ℓ) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hp' : p.comp (tbar ℓ) = 0 := hp
  rcases comp_eq_zero_iff.1 hp' with h | ⟨_, h⟩
  · exact h
  · exfalso
    have h3 := congrArg (fun r => r.coeff 2) h
    have h4 : (tbar ℓ).coeff 2 = -(2 : ZMod ℓ)⁻¹ := by
      simp [tbar]
    simp only [h4, coeff_C] at h3
    norm_num at h3
    exact two_ne_zero_zmod ℓ h2 h3

/-- `g(t,Y) ↦ g(−s²/2, Ȳ)`. -/
noncomputable def Phis : Polynomial (Polynomial (ZMod ℓ)) →+* Polynomial (Polynomial (ZMod ℓ)) :=
  eval₂RingHom (C.comp (phis ℓ)) (Ybar ℓ)

theorem Phis_injective (h2 : ℓ ≠ 2) : Function.Injective (Phis ℓ) := by
  rw [injective_iff_map_eq_zero]
  intro g hg
  have hg' : (g.map (phis ℓ)).comp (Ybar ℓ) = 0 := by
    rw [comp, eval₂_map]
    exact hg
  have h8 : (8 : ZMod ℓ) ≠ 0 := by
    have : (8 : ZMod ℓ) = 2 ^ 3 := by norm_num
    rw [this]
    exact pow_ne_zero _ (two_ne_zero_zmod ℓ h2)
  rcases comp_eq_zero_iff.1 hg' with h | ⟨_, h⟩
  · exact Polynomial.map_injective _ (phis_injective ℓ h2) (by rw [h, Polynomial.map_zero])
  · exfalso
    have h3 := congrArg (fun r => (r.coeff 2).coeff 4) h
    have h4 : ((Ybar ℓ).coeff 2).coeff 4 = (8 : ZMod ℓ)⁻¹ := by
      rw [Ybar, coeff_C_mul, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, if_pos rfl,
        if_neg (by norm_num), add_zero, coeff_C_mul_X_pow, if_pos rfl]
    simp only [h4, coeff_C] at h3
    norm_num at h3
    exact h8 h3

theorem evbar_eq : evbar ℓ = (Phis ℓ).comp (theta ℓ) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [evbar, theta, Phis, phis]
  · fin_cases i <;> simp [evbar, theta, Phis, phis]

/-- `t` and `Y` are algebraically independent modulo `ℓ` (paper.tex l.1288–1290). -/
theorem evbar_injective (h2 : ℓ ≠ 2) : Function.Injective (evbar ℓ) := by
  rw [evbar_eq, RingHom.coe_comp]
  exact (Phis_injective ℓ h2).comp (theta_injective ℓ)

/-! ### Reduction of `P(t,Y)` -/

/-- `ℤ[t,Y] → ℚ(s)(α)`. -/
noncomputable def psiZ : MvPolynomial (Fin 2) ℤ →+* K0 :=
  MvPolynomial.eval₂Hom (Int.castRingHom K0) ![tK, YK]

theorem red_t (h2 : ℓ ≠ 2) : red ℓ (C (-(X ^ 3))) = red ℓ ts * C (tbar ℓ) := by
  have h := two_ne_zero_zmod ℓ h2
  rw [red_ts, ← C_mul]
  simp only [red, coe_mapRingHom, map_C, Polynomial.map_neg, Polynomial.map_pow, map_X, tbar]
  congr 1
  have : C (2 : ZMod ℓ) * X * (C ((2 : ZMod ℓ)⁻¹) * -(X ^ 2)) =
      C ((2 : ZMod ℓ) * (2 : ZMod ℓ)⁻¹) * -(X ^ 3) := by
    rw [C_mul]
    ring
  rw [this, mul_inv_cancel₀ h, C_1, one_mul]

theorem red_y (h2 : ℓ ≠ 2) : red ℓ yts = red ℓ ts ^ 3 * Ybar ℓ := by
  have h8 : (8 : ZMod ℓ) ≠ 0 := by
    have : (8 : ZMod ℓ) = 2 ^ 3 := by norm_num
    rw [this]
    exact pow_ne_zero _ (two_ne_zero_zmod ℓ h2)
  rw [red_ts, Ybar]
  have e1 : red ℓ yts = C (X ^ 7) * X ^ 2 + C (X ^ 8 - C 2 * X ^ 6) * X := by
    simp [red, yts]
    exact (map_ofNat C 2).symm
  have a1 : (C (C (2 : ZMod ℓ) * X) : Polynomial (Polynomial (ZMod ℓ))) ^ 3 =
      C (C 8) * C (X ^ 3) := by
    rw [← C_pow, mul_pow, ← C_pow, ← C_mul]
    norm_num
  have a2 : (C (X ^ 3) : Polynomial (Polynomial (ZMod ℓ))) *
      (C (X ^ 4) * X ^ 2 + C (X ^ 5 - C 2 * X ^ 3) * X) =
      C (X ^ 7) * X ^ 2 + C (X ^ 8 - C 2 * X ^ 6) * X := by
    simp only [C_mul, C_pow, C_sub]
    ring
  have h88 : (C (C (8 : ZMod ℓ)) : Polynomial (Polynomial (ZMod ℓ))) * C (C ((8 : ZMod ℓ)⁻¹)) =
      1 := by
    rw [← C_mul, ← C_mul, mul_inv_cancel₀ h8, C_1, C_1]
  rw [e1, a1, ← a2]
  linear_combination (-((C (X ^ 3) : Polynomial (Polynomial (ZMod ℓ))) *
    (C (X ^ 4) * X ^ 2 + C (X ^ 5 - C 2 * X ^ 3) * X))) * h88

/-- Clearing the powers of `2s`: `P̃(t,Y) (2s)ⁿ ∈ ℤ[s][α]`, compatibly with the reduction. -/
theorem psiZ_clear (h2 : ℓ ≠ 2) (P : MvPolynomial (Fin 2) ℤ) :
    ∃ (n : ℕ) (a : PZ), psiZ P * iota ts ^ n = iota a ∧
      red ℓ a = red ℓ ts ^ n * evbar ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0, C (C c), ?_, ?_⟩
    · simp [psiZ, iota]
    · simp [red, evbar]
  | add p q hp hq =>
    obtain ⟨n, a, ha, ha'⟩ := hp
    obtain ⟨m, b, hb, hb'⟩ := hq
    refine ⟨n + m, a * ts ^ m + b * ts ^ n, ?_, ?_⟩
    · rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← ha, ← hb]
      ring
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, ha', hb', map_add, map_add]
      ring
  | mul_X p i hp =>
    obtain ⟨n, a, ha, ha'⟩ := hp
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · refine ⟨n + 1, a * C (-(X ^ 3)), ?_, ?_⟩
      · have : psiZ (p * MvPolynomial.X 0) = psiZ p * tK := by simp [psiZ]
        rw [this, map_mul, ← ha, ← tK_mul]
        ring
      · have : evbar ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) (p * MvPolynomial.X 0)) =
            evbar ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) p) * C (tbar ℓ) := by
          simp [evbar]
        rw [this, map_mul, ha', red_t ℓ h2]
        ring
    · refine ⟨n + 3, a * yts, ?_, ?_⟩
      · have : psiZ (p * MvPolynomial.X 1) = psiZ p * YK := by simp [psiZ]
        rw [this, map_mul, ← ha, ← YK_mul]
        ring
      · have : evbar ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) (p * MvPolynomial.X 1)) =
            evbar ℓ (MvPolynomial.map (Int.castRingHom (ZMod ℓ)) p) * Ybar ℓ := by
          simp [evbar]
        rw [this, map_mul, ha', red_y ℓ h2]
        ring

/-- If `P̃(t,Y) · (unit at 𝔭) ∈ ℓ · ℤ[1/2][s,s⁻¹,α]` then `ℓ` divides `P̃`
(paper.tex l.1287–1290). -/
theorem dvd_of_unit (h2 : ℓ ≠ 2) (P : MvPolynomial (Fin 2) ℤ) {δ N : K0} (hδ : Unit0 ℓ δ)
    (hN : N ∈ S0) (h : psiZ P * δ = (ℓ : K0) * N) :
    MvPolynomial.C ((ℓ : ℕ) : ℤ) ∣ P := by
  rw [MvPolynomial.C_dvd_iff_zmod]
  obtain ⟨n₁, a₁, h₁, hr₁⟩ := psiZ_clear ℓ h2 P
  obtain ⟨n₂, a₂, h₂, hr₂⟩ := hδ
  obtain ⟨n₃, a₃, h₃⟩ := hN
  have hι : iota (a₁ * a₂ * ts ^ n₃) = iota (C (C ((ℓ : ℕ) : ℤ)) * a₃ * ts ^ (n₁ + n₂)) := by
    have hl : iota (C (C ((ℓ : ℕ) : ℤ))) = (ℓ : K0) := by rw [iota_CC]; norm_num
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, hl, ← h₁, ← h₂, ← h₃]
    linear_combination (iota ts ^ n₁ * iota ts ^ n₂ * iota ts ^ n₃) * h
  have hPZ := iota_injective hι
  have hred := congrArg (red ℓ) hPZ
  have hl0 : red ℓ (C (C ((ℓ : ℕ) : ℤ))) = 0 := by
    simp [red]
  rw [map_mul, map_mul, map_mul, map_mul, hl0, zero_mul, zero_mul, map_pow] at hred
  have h4 : red ℓ a₁ = 0 := by
    rcases mul_eq_zero.1 hred with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h hr₂
    · exact absurd h (pow_ne_zero _ (red_ts_ne_zero ℓ h2))
  rw [hr₁] at h4
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h (pow_ne_zero _ (red_ts_ne_zero ℓ h2))
  · exact evbar_injective ℓ h2 (by rw [h, map_zero])

/-! ### `𝒪_𝔭 ∩ ℚ[t,Y] = ℤ_(ℓ)[t,Y]` -/

theorem exists_clear (P : MvPolynomial (Fin 2) ℚ) :
    ∃ (D : ℕ) (Pt : MvPolynomial (Fin 2) ℤ), D ≠ 0 ∧
      MvPolynomial.map (Int.castRingHom ℚ) Pt = MvPolynomial.C (D : ℚ) * P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨c.den, MvPolynomial.C c.num, c.den_nz, ?_⟩
    rw [MvPolynomial.map_C, ← MvPolynomial.C_mul]
    congr 1
    rw [mul_comm, eq_intCast, Rat.mul_den_eq_num]
  | add p q hp hq =>
    obtain ⟨D1, P1, h1, e1⟩ := hp
    obtain ⟨D2, P2, h2, e2⟩ := hq
    refine ⟨D1 * D2, MvPolynomial.C (D2 : ℤ) * P1 + MvPolynomial.C (D1 : ℤ) * P2,
      mul_ne_zero h1 h2, ?_⟩
    rw [map_add, map_mul, map_mul, e1, e2, MvPolynomial.map_C, MvPolynomial.map_C]
    simp only [eq_intCast, Int.cast_natCast, Nat.cast_mul, MvPolynomial.C_mul]
    ring
  | mul_X p i hp =>
    obtain ⟨D, Pt, h, e⟩ := hp
    exact ⟨D, Pt * MvPolynomial.X i, h, by rw [map_mul, MvPolynomial.map_X, e]; ring⟩

theorem psiZ_map (Pt : MvPolynomial (Fin 2) ℤ) :
    psiZ Pt = MvPolynomial.aeval ![tK, YK] (MvPolynomial.map (Int.castRingHom ℚ) Pt) := by
  show MvPolynomial.eval₂ (Int.castRingHom K0) ![tK, YK] Pt = _
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  congr 1
  exact RingHom.ext_int _ _

theorem psiZ_C (z : ℤ) : psiZ (MvPolynomial.C z) = (z : K0) := by
  simp [psiZ]

/-- An element of `ℚ[t,Y]` whose value at `(t,Y)`, times a unit at `𝔭`, is integral has
`ℓ`-integral coefficients (paper.tex l.1287–1290). -/
theorem local_integral (h2 : ℓ ≠ 2) (P : MvPolynomial (Fin 2) ℚ) {δ N : K0}
    (hδ : Unit0 ℓ δ) (hN : N ∈ S0) (h : MvPolynomial.aeval ![tK, YK] P * δ = N)
    (e : Fin 2 →₀ ℕ) :
    ∃ a b : ℤ, ¬ ((ℓ : ℤ) ∣ b) ∧ MvPolynomial.coeff e P = (a : ℚ) / b := by
  obtain ⟨D, Pt, hD, hPt⟩ := exists_clear P
  have hψ : psiZ Pt = (D : K0) * MvPolynomial.aeval ![tK, YK] P := by
    rw [psiZ_map, hPt, map_mul, MvPolynomial.aeval_C, map_natCast]
  have hl : (ℓ : K0) ≠ 0 := Nat.cast_ne_zero.2 hℓ.out.ne_zero
  have key : ∀ j : ℕ, j ≤ D.factorization ℓ → MvPolynomial.C (((ℓ : ℕ) : ℤ) ^ j) ∣ Pt := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [pow_zero, MvPolynomial.C_1]
      exact one_dvd _
    | succ j ih =>
      intro hj
      obtain ⟨Q, hQ⟩ := ih (by omega)
      obtain ⟨D2, hD2⟩ : ℓ ^ (j + 1) ∣ D := (pow_dvd_pow ℓ hj).trans (Nat.ordProj_dvd D ℓ)
      have h1 : psiZ Pt = (ℓ : K0) ^ j * psiZ Q := by
        rw [hQ, map_mul, psiZ_C]
        push_cast
        rfl
      have hDK : (D : K0) = (ℓ : K0) ^ (j + 1) * (D2 : K0) := by
        rw [hD2]
        push_cast
        rfl
      have h3 : (ℓ : K0) ^ j * (psiZ Q * δ) = (ℓ : K0) ^ j * ((ℓ : K0) * ((D2 : K0) * N)) := by
        rw [← mul_assoc, ← h1, hψ, ← h, hDK]
        ring
      have hQψ := mul_left_cancel₀ (pow_ne_zero _ hl) h3
      obtain ⟨Q', hQ'⟩ := dvd_of_unit ℓ h2 Q hδ (S0.mul_mem (natCast_mem S0 D2) hN) hQψ
      exact ⟨Q', by rw [hQ, hQ', ← mul_assoc, ← MvPolynomial.C_mul, pow_succ]⟩
  obtain ⟨Q, hQ⟩ := key _ le_rfl
  have hc : (D : ℚ) * MvPolynomial.coeff e P =
      (ℓ : ℚ) ^ D.factorization ℓ * ((MvPolynomial.coeff e Q : ℤ) : ℚ) := by
    have := congrArg (MvPolynomial.coeff e) hPt
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, hQ, MvPolynomial.coeff_C_mul] at this
    rw [← this, eq_intCast]
    push_cast
    rfl
  have hDv : (D : ℚ) = (ℓ : ℚ) ^ D.factorization ℓ * ((D / ℓ ^ D.factorization ℓ : ℕ) : ℚ) := by
    exact_mod_cast (Nat.ordProj_mul_ordCompl_eq_self D ℓ).symm
  have hlq : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hℓ.out.ne_zero
  have hne : ((D / ℓ ^ D.factorization ℓ : ℕ) : ℚ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hDv
    exact hD (by exact_mod_cast hDv)
  refine ⟨MvPolynomial.coeff e Q, ((D / ℓ ^ D.factorization ℓ : ℕ) : ℤ), ?_, ?_⟩
  · intro hd
    exact Nat.not_dvd_ordCompl hℓ.out hD (by exact_mod_cast hd)
  · rw [Int.cast_natCast, eq_div_iff hne]
    apply mul_left_cancel₀ (pow_ne_zero (D.factorization ℓ) hlq)
    rw [← hc, hDv]
    ring

end Virasoro.H13Local

namespace Virasoro.H13Local

/-- A rational number that is `ℓ`-integral for every odd prime `ℓ` lies in `ℤ[1/2]`
(paper.tex l.1290–1291). -/
theorem two_pow_of_odd (c : ℚ)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ 2 → ∃ a b : ℤ, ¬ ((ℓ : ℤ) ∣ b) ∧ c = (a : ℚ) / b) :
    ∃ (z : ℤ) (n : ℕ), c = (z : ℚ) / 2 ^ n := by
  have hden : c.den = 2 ^ c.den.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd c.den_nz ?_
    intro d hd hdvd
    by_contra hne
    obtain ⟨a, b, hb, hc⟩ := h d hd hne
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hb (dvd_zero _)
    have e : c.num * b = a * (c.den : ℤ) := by
      have h1 : (c.num : ℚ) / (c.den : ℚ) = (a : ℚ) / b := by rw [Rat.num_div_den, hc]
      have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb0
      have hdq : (c.den : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
      rw [div_eq_div_iff hdq hbq] at h1
      exact_mod_cast h1
    have h2 : c.den ∣ b.natAbs * c.num.natAbs := by
      have := congrArg Int.natAbs e
      rw [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast] at this
      rw [mul_comm, this]
      exact dvd_mul_left _ _
    have h3 : c.den ∣ b.natAbs := (c.reduced.symm).dvd_of_dvd_mul_right h2
    exact hb (Int.natCast_dvd.2 (hdvd.trans h3))
  refine ⟨c.num, c.den.primeFactorsList.length, ?_⟩
  have : (c.den : ℚ) = 2 ^ c.den.primeFactorsList.length := by exact_mod_cast hden
  rw [← this, Rat.num_div_den]

end Virasoro.H13Local
