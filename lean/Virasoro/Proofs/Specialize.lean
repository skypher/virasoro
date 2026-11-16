import Virasoro.Proofs.RegEval
import Virasoro.Proofs.LevelComp
import Virasoro.Proofs.Naturality
import Virasoro.Statements.Prelude
import Mathlib.Algebra.Polynomial.Roots

/-!
# Specialization of the normalized singular vector and of the two normalization identities

A singular vector of `M(c(b), h_{r,s}(b))` over `ℚ(b)` with coordinates regular at a point `b`
of a field of characteristic zero specializes to a singular vector there, and the crossing
scalar and the torus self-pairing specialize with it.
-/

namespace Virasoro

open Polynomial

section Forms

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (f : R →+* S)

theorem map_gramForm (c h : R) (N : ℕ) (u v : Nat.Partition N → R) :
    f (gramForm c h N u v) = gramForm (f c) (f h) N (fun Y => f (u Y)) (fun Y => f (v Y)) := by
  unfold gramForm
  rw [gram_map, RingHom.map_dotProduct]
  congr 1
  funext Y
  exact RingHom.map_mulVec f (gram c h N) v Y

theorem map_torusForm (c h d : R) (N : ℕ) (u v : Nat.Partition N → R) :
    f (torusForm c h d N u v)
      = torusForm (f c) (f h) (f d) N (fun Y => f (u Y)) (fun Y => f (v Y)) := by
  unfold torusForm
  rw [torus_map, RingHom.map_dotProduct]
  congr 1
  funext Y
  exact RingHom.map_mulVec f (torus c h d N) v Y

/-- The crossing scalar `d/dh ⟨h|ω(P)P|h⟩ |_{h=h₀}` over a commutative ring. -/
noncomputable def crossR (c h₀ : R) {ℓ : ℕ} (p : Nat.Partition ℓ → R) : R :=
  (derivative (gramForm (C c) (X : R[X]) ℓ (fun Y => C (p Y)) (fun Y => C (p Y)))).eval h₀

theorem map_crossR (c h₀ : R) {ℓ : ℕ} (p : Nat.Partition ℓ → R) :
    f (crossR c h₀ p) = crossR (f c) (f h₀) (fun Y => f (p Y)) := by
  unfold crossR
  have h1 := map_gramForm (Polynomial.mapRingHom f) (C c) (X : R[X]) ℓ
    (fun Y => C (p Y)) (fun Y => C (p Y))
  simp only [coe_mapRingHom, map_C, map_X] at h1
  rw [← h1, derivative_map, eval_map, eval₂_at_apply]

/-- The torus self-pairing as a polynomial in the external weight `d`. -/
noncomputable def torusSelf (c h : R) {ℓ : ℕ} (p : Nat.Partition ℓ → R) : R[X] :=
  torusForm (C c) (C h) (X : R[X]) ℓ (fun Y => C (p Y)) (fun Y => C (p Y))

theorem map_torusSelf (c h : R) {ℓ : ℕ} (p : Nat.Partition ℓ → R) :
    (torusSelf c h p).map f = torusSelf (f c) (f h) (fun Y => f (p Y)) := by
  unfold torusSelf
  have h1 := map_torusForm (Polynomial.mapRingHom f) (C c) (C h) (X : R[X]) ℓ
    (fun Y => C (p Y)) (fun Y => C (p Y))
  simp only [coe_mapRingHom, map_C, map_X] at h1
  exact h1

theorem torusSelf_eval (c h d : R) {ℓ : ℕ} (p : Nat.Partition ℓ → R) :
    (torusSelf c h p).eval d = torusForm c h d ℓ p p := by
  unfold torusSelf
  have h1 := map_torusForm (Polynomial.evalRingHom d) (C c) (C h) (X : R[X]) ℓ
    (fun Y => C (p Y)) (fun Y => C (p Y))
  simp only [coe_evalRingHom, eval_C, eval_X] at h1
  exact h1

/-- An injective change of coefficient ring is injective on Verma modules. -/
theorem Verma.baseChange_injective {c h : R} {c' h' : S} (hc : f c = c') (hh : f h = h')
    (hf : Function.Injective f) : Function.Injective (Verma.baseChange f hc hh) := by
  intro u v huv
  have h0 : Verma.baseChange f hc hh (u - v) = 0 := by rw [map_sub, huv, sub_self]
  obtain ⟨ψ, hψ⟩ := Verma.baseChange_eq_zero f hc hh (π := 0)
    (fun a ha => ⟨0, by rw [zero_mul]; exact hf (by rw [ha, map_zero])⟩) (u - v) h0
  rw [zero_smul] at hψ
  exact sub_eq_zero.1 hψ

end Forms

section Field

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

theorem crossScalar_eq_crossR (c h₀ : 𝔽) {ℓ : ℕ} (p : Nat.Partition ℓ → 𝔽) :
    crossScalar c h₀ p = crossR c h₀ p := rfl

/-- The fusion polynomial `𝒫_{r,s}(b,d)` as a polynomial in `d`. -/
noncomputable def genPpoly (r s : ℕ) (b : 𝔽) : 𝔽[X] :=
  ∏ k ∈ oddsBelow r, ∏ l ∈ oddsBelow s,
    (C (((b + b⁻¹) ^ 2 - ((k : 𝔽) * b + (l : 𝔽) * b⁻¹) ^ 2) / 4) - X) *
      (C (((b + b⁻¹) ^ 2 - ((k : 𝔽) * b - (l : 𝔽) * b⁻¹) ^ 2) / 4) - X)

theorem genPpoly_eval (r s : ℕ) (b d : 𝔽) : (genPpoly r s b).eval d = genP r s b d := by
  unfold genPpoly genP lamSq
  rw [eval_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [eval_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [eval_mul, eval_sub, eval_C, eval_X]
  ring

theorem EvTo.unique {b : 𝔽} {x : RatFunc ℚ} {v w : 𝔽} (hv : EvTo b x v) (hw : EvTo b x w) :
    v = w := by rw [← hv.2, ← hw.2]

theorem EvTo.sum {b : 𝔽} {ι : Type*} (s : Finset ι) {x : ι → RatFunc ℚ} {v : ι → 𝔽}
    (h : ∀ i ∈ s, EvTo b (x i) (v i)) : EvTo b (∑ i ∈ s, x i) (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evTo_zero (b := b)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A polynomial over `ℚ(b)` whose coefficients are regular at `b`, with the polynomial of their
values. -/
def PolyEv (b : 𝔽) (P : (RatFunc ℚ)[X]) (P' : 𝔽[X]) : Prop :=
  ∀ n : ℕ, EvTo b (P.coeff n) (P'.coeff n)

theorem PolyEv.mul {b : 𝔽} {P Q : (RatFunc ℚ)[X]} {P' Q' : 𝔽[X]} (hP : PolyEv b P P')
    (hQ : PolyEv b Q Q') : PolyEv b (P * Q) (P' * Q') := by
  intro n
  rw [coeff_mul, coeff_mul]
  exact EvTo.sum _ fun i _ => (hP i.1).mul (hQ i.2)

theorem PolyEv.sub {b : 𝔽} {P Q : (RatFunc ℚ)[X]} {P' Q' : 𝔽[X]} (hP : PolyEv b P P')
    (hQ : PolyEv b Q Q') : PolyEv b (P - Q) (P' - Q') := by
  intro n
  rw [coeff_sub, coeff_sub]
  exact (hP n).sub (hQ n)

theorem polyEv_C {b : 𝔽} {x : RatFunc ℚ} {v : 𝔽} (hx : EvTo b x v) : PolyEv b (C x) (C v) := by
  intro n
  rw [coeff_C, coeff_C]
  split_ifs
  · exact hx
  · exact evTo_zero

theorem polyEv_X {b : 𝔽} : PolyEv b (X : (RatFunc ℚ)[X]) (X : 𝔽[X]) := by
  intro n
  rw [coeff_X, coeff_X]
  split_ifs
  · exact evTo_one
  · exact evTo_zero

theorem polyEv_one {b : 𝔽} : PolyEv b (1 : (RatFunc ℚ)[X]) (1 : 𝔽[X]) := by
  have := polyEv_C (b := b) evTo_one
  simpa using this

theorem PolyEv.prod {b : 𝔽} {ι : Type*} (s : Finset ι) {P : ι → (RatFunc ℚ)[X]}
    {P' : ι → 𝔽[X]} (h : ∀ i ∈ s, PolyEv b (P i) (P' i)) :
    PolyEv b (∏ i ∈ s, P i) (∏ i ∈ s, P' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polyEv_one (b := b)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem PolyEv.unique {b : 𝔽} {P : (RatFunc ℚ)[X]} {P' P'' : 𝔽[X]} (h1 : PolyEv b P P')
    (h2 : PolyEv b P P'') : P' = P'' :=
  Polynomial.ext fun n => (h1 n).unique (h2 n)

theorem polyEv_genPpoly {b : 𝔽} (hb : b ≠ 0) (r s : ℕ) :
    PolyEv b (genPpoly r s (RatFunc.X : RatFunc ℚ)) (genPpoly r s b) := by
  unfold genPpoly
  refine PolyEv.prod _ fun k _ => PolyEv.prod _ fun l _ => ?_
  have hX := evTo_X (b := b)
  have hXi := hX.inv hb
  have h4 : (OfNat.ofNat 4 : 𝔽) ≠ 0 := by norm_num
  refine PolyEv.mul (PolyEv.sub (polyEv_C ?_) polyEv_X) (PolyEv.sub (polyEv_C ?_) polyEv_X)
  · exact EvTo.div (((hX.add hXi).pow 2).sub
      ((((evTo_natCast k).mul hX).add ((evTo_natCast l).mul hXi)).pow 2)) (evTo_ofNat 4) h4
  · exact EvTo.div (((hX.add hXi).pow 2).sub
      ((((evTo_natCast k).mul hX).sub ((evTo_natCast l).mul hXi)).pow 2)) (evTo_ofNat 4) h4

/-- Specialization at `b` of a singular vector over `ℚ(b)` with regular coordinates: it is
singular, and its crossing scalar and torus self-pairing are the specializations. -/
theorem specialize_singular {b : 𝔽} {c₀ h₀ : RatFunc ℚ} {cb hb : 𝔽} (hc : EvTo b c₀ cb)
    (hh : EvTo b h₀ hb) {ℓ : ℕ} (p : Nat.Partition ℓ → RatFunc ℚ)
    (hreg : ∀ Y, Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.denom (p Y)) ≠ 0)
    (hsing : Verma.IsSingular (Verma.pbwCoord (c := c₀) (h := h₀) ℓ p) ℓ)
    (hne : ∃ Y, RatFunc.eval (algebraMap ℚ 𝔽) b (p Y) ≠ 0) :
    Verma.IsSingular (Verma.pbwCoord (c := cb) (h := hb) ℓ
        fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y)) ℓ ∧
      EvTo b (crossScalar c₀ h₀ p)
        (crossScalar cb hb fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y)) ∧
      PolyEv b (torusSelf c₀ h₀ p)
        (torusSelf cb hb fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y)) := by
  set cR : regSub b := ⟨c₀, hc.1⟩ with hcR
  set hR : regSub b := ⟨h₀, hh.1⟩ with hhR
  set pR : Nat.Partition ℓ → regSub b := fun Y => ⟨p Y, hreg Y⟩ with hpR
  set incl : regSub b →+* RatFunc ℚ := ((regSub b).val : regSub b →+* RatFunc ℚ) with hincl
  have hinj : Function.Injective incl := Subtype.val_injective
  have hic : incl cR = c₀ := rfl
  have hih : incl hR = h₀ := rfl
  have hec : evReg b cR = cb := hc.2
  have heh : evReg b hR = hb := hh.2
  set χR := Verma.pbwCoord (c := cR) (h := hR) ℓ pR with hχR
  have hχi : Verma.baseChange incl hic hih χR = Verma.pbwCoord ℓ p := by
    rw [hχR, Verma.baseChange_pbwCoord]
    rfl
  have hχe : Verma.baseChange (evReg b) hec heh χR
      = Verma.pbwCoord ℓ fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y) := by
    rw [hχR, Verma.baseChange_pbwCoord]
    rfl
  have hLR : ∀ n : ℤ, 0 < n → Verma.L n χR = 0 := by
    intro n hn
    apply Verma.baseChange_injective incl hic hih hinj
    rw [Verma.baseChange_L, hχi, hsing.2.2 n hn, map_zero]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h0
    obtain ⟨Y, hY⟩ := hne
    apply hY
    have h1 := Verma.pbwCoord_injective (c := cb) (h := hb) ℓ
      (a₁ := fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y)) (a₂ := 0) (by rw [h0, map_zero])
    exact congrFun h1 Y
  · exact Verma.L_zero_of_mem_level ⟨_, rfl⟩
  · intro n hn
    rw [← hχe, ← Verma.baseChange_L, hLR n hn, map_zero]
  · have h1 : crossScalar c₀ h₀ p = incl (crossR cR hR pR) := by
      rw [crossScalar_eq_crossR, map_crossR incl cR hR pR]
      rfl
    have h2 : (crossScalar cb hb fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y))
        = evReg b (crossR cR hR pR) := by
      rw [crossScalar_eq_crossR, map_crossR (evReg b) cR hR pR, hec, heh]
      rfl
    rw [h1, h2]
    exact ⟨(crossR cR hR pR).2, rfl⟩
  · intro n
    have h1 : torusSelf c₀ h₀ p = (torusSelf cR hR pR).map incl := by
      rw [map_torusSelf incl cR hR pR]
      rfl
    have h2 : (torusSelf cb hb fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (p Y))
        = (torusSelf cR hR pR).map (evReg b) := by
      rw [map_torusSelf (evReg b) cR hR pR, hec, heh]
      rfl
    rw [h1, h2, coeff_map, coeff_map]
    exact ⟨((torusSelf cR hR pR).coeff n).2, rfl⟩

end Field

end Virasoro
