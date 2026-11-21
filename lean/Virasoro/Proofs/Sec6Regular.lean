import Virasoro.Proofs.SingularOnes
import Virasoro.Proofs.Sec6Norm
import Virasoro.Statements.Sec6b
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Lemma 6.6 of `paper.tex` at 70bac53: regular normalized singular vectors

Let `e ≥ 0` be minimal such that `(b - b⋆)^e χ_{r,s}(b)` is regular at `b⋆`, with value `w ≠ 0`.
The singularity conditions are linear with coefficients polynomial in `b`, so `w` is singular in
`M(c⋆, h_{r,s}(b⋆))`.  Its `L_{-1}^{rs}`-coefficient is the value of `(b - b⋆)^e`, which is
nonzero by Lemma 5.7; so `e = 0` (paper.tex l.1102–1110).

Over `ℚ(b)` the place `b = b⋆` is given by the minimal polynomial `m` of `b⋆` over `ℚ` when
`b⋆` is algebraic (then `m^e` stands for `(b - b⋆)^e`), and no nonzero element of `ℚ[b]` vanishes
at `b⋆` otherwise.
-/

namespace Virasoro

open Polynomial

section Place

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽] {b : 𝔽}

theorem evTo_poly (q : ℚ[X]) :
    EvTo b (algebraMap ℚ[X] (RatFunc ℚ) q) (q.eval₂ (algebraMap ℚ 𝔽) b) := by
  refine ⟨?_, RatFunc.eval_algebraMap _ _ _⟩
  rw [RatFunc.denom_algebraMap]
  simp

theorem eval₂_ne_of_dvd {D a : ℚ[X]} (h : D ∣ a) (ha : a.eval₂ (algebraMap ℚ 𝔽) b ≠ 0) :
    D.eval₂ (algebraMap ℚ 𝔽) b ≠ 0 := by
  obtain ⟨k, rfl⟩ := h
  intro h0
  exact ha (by rw [eval₂_mul, h0, zero_mul])

variable {m : ℚ[X]} (hirr : Irreducible m)
  (hdvd : ∀ q : ℚ[X], q.eval₂ (algebraMap ℚ 𝔽) b = 0 → m ∣ q)

include hirr hdvd

/-- Some power of `m` clears the pole of `x` at `b`. -/
theorem exists_pow_regular (x : RatFunc ℚ) :
    ∃ k : ℕ, (RatFunc.denom (algebraMap ℚ[X] (RatFunc ℚ) m ^ k * x)).eval₂ (algebraMap ℚ 𝔽) b
      ≠ 0 := by
  obtain ⟨n, a, hna, hda⟩ := WfDvdMonoid.max_power_factor (RatFunc.denom_ne_zero x) hirr
  have hm0 : algebraMap ℚ[X] (RatFunc ℚ) m ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).2 hirr.ne_zero
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact RatFunc.denom_ne_zero x (by rw [hda, mul_zero])
  have ha0' : algebraMap ℚ[X] (RatFunc ℚ) a ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).2 ha0
  have hx : algebraMap ℚ[X] (RatFunc ℚ) m ^ n * x =
      algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.num x) / algebraMap ℚ[X] (RatFunc ℚ) a := by
    conv_lhs => rw [← RatFunc.num_div_denom x, hda, map_mul, map_pow]
    field_simp
  refine ⟨n, ?_⟩
  rw [hx]
  exact eval₂_ne_of_dvd (RatFunc.denom_div_dvd _ _) fun h0 => hna (hdvd a h0)

omit hirr in
/-- If `x` is regular at `b` with value `0`, then `x / m` is regular at `b`. -/
theorem regular_div_of_zero (hm0 : m ≠ 0) {x : RatFunc ℚ} (hx : EvTo b x 0) :
    (RatFunc.denom (x / algebraMap ℚ[X] (RatFunc ℚ) m)).eval₂ (algebraMap ℚ 𝔽) b ≠ 0 := by
  have hnum : (RatFunc.num x).eval₂ (algebraMap ℚ 𝔽) b = 0 := by
    have h2 := hx.2
    rw [RatFunc.eval, div_eq_zero_iff] at h2
    exact h2.resolve_right hx.1
  obtain ⟨n', hn'⟩ := hdvd _ hnum
  have hm0' : algebraMap ℚ[X] (RatFunc ℚ) m ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).2 hm0
  have hd0' : algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom x) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).2 (RatFunc.denom_ne_zero x)
  have hx' : x / algebraMap ℚ[X] (RatFunc ℚ) m =
      algebraMap ℚ[X] (RatFunc ℚ) n' / algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom x) := by
    conv_lhs => rw [← RatFunc.num_div_denom x, hn', map_mul]
    field_simp
  rw [hx']
  exact eval₂_ne_of_dvd (RatFunc.denom_div_dvd _ _) hx.1

end Place

theorem isSingular_smul {K : Type*} [Field K] [CharZero K] {c h : K} {χ : Verma K c h} {ℓ : ℕ}
    (hχ : Verma.IsSingular χ ℓ) {a : K} (ha : a ≠ 0) : Verma.IsSingular (a • χ) ℓ := by
  obtain ⟨h0, h1, h2⟩ := hχ
  refine ⟨smul_ne_zero ha h0, ?_, fun n hn => ?_⟩
  · rw [map_smul, h1, smul_comm]
  · rw [map_smul, h2 n hn]
    exact smul_zero (A := Verma K c h) a

/-- The coordinates of a normalized singular vector over `ℚ(b)` of level `rs` on the Kac curve
are regular at every `b⋆ ∈ ℂ^×`. -/
theorem regular_of_normalized {r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (p : Nat.Partition (r * s) → RatFunc ℚ) (hp1 : p (onesPartition (r * s)) = 1)
    (hsing : Verma.IsSingular
      (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
        (r * s) p) (r * s))
    {b₁ : ℂ} (hb : b₁ ≠ 0) (Y : Nat.Partition (r * s)) :
    Polynomial.eval₂ (algebraMap ℚ ℂ) b₁ (RatFunc.denom (p Y)) ≠ 0 := by
  classical
  by_cases halg : IsAlgebraic ℚ b₁
  swap
  · intro h0
    exact halg ⟨_, RatFunc.denom_ne_zero (p Y), by rw [aeval_def]; exact h0⟩
  have hirr : Irreducible (minpoly ℚ b₁) := minpoly.irreducible halg.isIntegral
  have hdvd : ∀ q : ℚ[X], q.eval₂ (algebraMap ℚ ℂ) b₁ = 0 → minpoly ℚ b₁ ∣ q := fun q hq =>
    minpoly.dvd ℚ b₁ (by rw [aeval_def]; exact hq)
  have hroot : (minpoly ℚ b₁).eval₂ (algebraMap ℚ ℂ) b₁ = 0 := by
    rw [← aeval_def]
    exact minpoly.aeval ℚ b₁
  obtain ⟨M, hM⟩ : ∃ M : RatFunc ℚ, M = algebraMap ℚ[X] (RatFunc ℚ) (minpoly ℚ b₁) := ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective ℚ)).2 hirr.ne_zero
  have hMev : EvTo b₁ M 0 := by
    rw [hM, ← hroot]
    exact evTo_poly _
  -- a power of `m` clears all poles
  have hP : ∃ e : ℕ, ∀ Y, Polynomial.eval₂ (algebraMap ℚ ℂ) b₁ (RatFunc.denom (M ^ e * p Y)) ≠ 0 := by
    choose k hk using fun Y => exists_pow_regular (b := b₁) hirr hdvd (p Y)
    refine ⟨∑ Y, k Y, fun Y => ?_⟩
    have hle : k Y ≤ ∑ Y, k Y := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ Y)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
    have h1 : EvTo b₁ (M ^ k Y * p Y) _ := ⟨by rw [hM]; exact hk Y, rfl⟩
    have h2 := (hMev.pow j).mul h1
    have e3 : M ^ (∑ Y, k Y) * p Y = M ^ j * (M ^ k Y * p Y) := by
      rw [hj, pow_add]
      ring
    rw [e3]
    exact h2.1
  obtain ⟨e, he, hmin⟩ : ∃ e : ℕ, (∀ Y, Polynomial.eval₂ (algebraMap ℚ ℂ) b₁
      (RatFunc.denom (M ^ e * p Y)) ≠ 0) ∧ ∀ e' < e, ¬ ∀ Y, Polynomial.eval₂ (algebraMap ℚ ℂ) b₁
        (RatFunc.denom (M ^ e' * p Y)) ≠ 0 :=
    ⟨Nat.find hP, Nat.find_spec hP, fun e' he' => Nat.find_min hP he'⟩
  rcases Nat.eq_zero_or_pos e with he0 | hepos
  · have := he Y
    rwa [he0, pow_zero, one_mul] at this
  exfalso
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  by_cases hne : ∃ Y, RatFunc.eval (algebraMap ℚ ℂ) b₁ (M ^ (e' + 1) * p Y) ≠ 0
  · -- the value is a singular vector whose `L_{-1}^{rs}`-coefficient vanishes
    have hsing' : Verma.IsSingular
        (Verma.pbwCoord (c := kacC (RatFunc.X : RatFunc ℚ)) (h := kacH r s RatFunc.X)
          (r * s) fun Y => M ^ (e' + 1) * p Y) (r * s) := by
      have e1 : (fun Y => M ^ (e' + 1) * p Y) = M ^ (e' + 1) • p := rfl
      rw [e1, map_smul]
      exact isSingular_smul hsing (pow_ne_zero _ hM0)
    obtain ⟨h1, -, -⟩ := specialize_singular (evTo_kacC hb) (evTo_kacH hb (r : ℤ) (s : ℤ))
      (fun Y => M ^ (e' + 1) * p Y) he hsing' hne
    have h2 := sub_singular_ones_coeff (kacC b₁) (kacH r s b₁) (r * s) (Nat.mul_pos hr hs) _ h1
    apply h2
    show RatFunc.eval (algebraMap ℚ ℂ) b₁ (M ^ (e' + 1) * p (onesPartition (r * s))) = 0
    rw [hp1, mul_one, (hMev.pow (e' + 1)).2, pow_succ, mul_zero]
  · -- all values vanish, so `e' = e - 1` already works
    simp only [not_exists, not_not] at hne
    refine hmin e' (Nat.lt_succ_self _) fun Y => ?_
    have hx : EvTo b₁ (M ^ (e' + 1) * p Y) 0 := ⟨he Y, hne Y⟩
    have h3 := regular_div_of_zero (b := b₁) hdvd hirr.ne_zero hx
    have e2 : M ^ (e' + 1) * p Y / algebraMap ℚ[X] (RatFunc ℚ) (minpoly ℚ b₁) = M ^ e' * p Y := by
      rw [← hM, pow_succ]
      field_simp
    rwa [e2] at h3

/-- Lemma 6.6 from the cited normalization identities of Proposition 6.2. -/
theorem lem_regular_everywhere_of_cited (hH : Cited_HJSNormalizations) :
    Stmt_lem_regular_everywhere := by
  intro r s hr hs p hp1 hsing b₁ hb
  have hreg := fun Y => regular_of_normalized hr hs p hp1 hsing hb Y
  obtain ⟨p₀, -, huniq, -, -, hspec⟩ := normalization_at hH r s hr hs
  obtain rfl : p = p₀ := huniq p hp1 hsing
  obtain ⟨h1, h2, h3, h4⟩ := hspec ℂ b₁ hb hreg
  refine ⟨hreg, h2, h1, h4, fun _ => ?_⟩
  rw [genA_inv]
  exact h3

example (hH : Cited_HJSNormalizations) : Stmt_lem_regular_everywhere :=
  lem_regular_everywhere_of_cited hH

end Virasoro
