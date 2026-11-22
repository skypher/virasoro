import Virasoro.Statements.Sec10
import Virasoro.Cited2
import Virasoro.Proofs.DefMatrices
import Virasoro.Proofs.Naturality
import Virasoro.Proofs.Shapovalov

/-!
# Lemma 10.1 (two-weight primary Ward identity), paper.tex l.2045–2097

The induction on `N₁ + N₂` of the paper's proof (l.2076–2081) is the recursion `torusWord2`:
positive modes are moved from the left argument to the right one, and at the highest-weight
vector of `M(c,Δ₁)` the negative modes of the right argument are removed one by one.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `ρ_{Δ₁,Δ₂;d}(v_{Δ₁}, L_{-w} v_{Δ₂})`: by (10.1) with `m < 0` and `L_{-m} v_{Δ₁} = 0`,
`ρ(v_{Δ₁}, L_{-m} w') = (Δ₂ - Δ₁ + |w'| + m d) ρ(v_{Δ₁}, w')`. -/
def phi2 (h₁ h₂ d : R) : List ℕ → R
  | [] => 1
  | m :: w => (h₂ - h₁ + ((w.sum : ℕ) : R) + (m : R) * d) * phi2 h₁ h₂ d w

/-- `ρ_{Δ₁,Δ₂;d}(L_{-Y} v_{Δ₁}, L_{-w} v_{Δ₂})`: by (10.1) with `m = y > 0`,
`ρ(L_{-y} u', w) = ρ(u', L_y w) + ((Δ₁ + |u'|) - (Δ₂ + |w|) + y d) ρ(u', w)`. -/
def torusWord2 (c h₁ h₂ d : R) : List ℕ → List ℕ → R
  | [], w => phi2 h₁ h₂ d w
  | y :: Y, w =>
      ((actWord c h₂ (y : ℤ) w).map fun t => t.2 * torusWord2 c h₁ h₂ d Y t.1).sum
        + (h₁ - h₂ + ((Y.sum : ℕ) : R) - ((w.sum : ℕ) : R) + (y : R) * d) *
          torusWord2 c h₁ h₂ d Y w

namespace Verma

variable {c h₁ h₂ d : R} {T : Verma R c h₁ →ₗ[R] Verma R c h₂ →ₗ[R] R}

theorem twoWeight_hw_neg (hT : IsTwoWeightPairing d T) (w : List ℕ) (hw : PosWord w) :
    T Verma.hw (neg w) = phi2 h₁ h₂ d w := by
  induction w with
  | nil => rw [neg_nil, hT.1]; rfl
  | cons m w ih =>
    have hm : 0 < m := hw m List.mem_cons_self
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have e := hT.2 (-(m : ℤ)) Verma.hw (neg w)
    rw [neg_neg, L_hw_pos (by omega), L_hw_zero, L_zero_neg, map_zero, LinearMap.zero_apply,
      map_smul, map_smul, LinearMap.smul_apply, ← neg_cons, ih hw'] at e
    rw [phi2]
    simp only [smul_eq_mul, Int.cast_neg, Int.cast_natCast] at e
    linear_combination -e

theorem twoWeight_toVerma (T : Verma R c h₁ →ₗ[R] Verma R c h₂ →ₗ[R] R) (u : Verma R c h₁)
    (s : St R) : T u (St.toVerma s) = (s.map fun t => t.2 * T u (neg t.1)).sum := by
  induction s with
  | nil => rw [St.toVerma_nil, map_zero]; rfl
  | cons t s ih =>
    rw [St.toVerma_cons, map_add, map_smul, ih, List.map_cons, List.sum_cons, smul_eq_mul]

/-- The matrix elements of a two-weight pairing are computed by the Ward identity (10.1). -/
theorem twoWeight_torusWord (hT : IsTwoWeightPairing d T) : ∀ Y : List ℕ, PosWord Y →
    ∀ w : List ℕ, PosWord w → T (neg Y) (neg w) = torusWord2 c h₁ h₂ d Y w := by
  intro Y
  induction Y with
  | nil =>
    intro _ w hw
    rw [neg_nil, twoWeight_hw_neg hT w hw, torusWord2]
  | cons y Y ih =>
    intro hY w hw
    have hY' : PosWord Y := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    have e := hT.2 (y : ℤ) (neg Y) (neg w)
    rw [← neg_cons, L_neg_actWord w (y : ℤ), L_zero_neg, L_zero_neg, map_smul, map_smul,
      LinearMap.smul_apply, twoWeight_toVerma, ih hY' w hw] at e
    have e2 : ((actWord c h₂ (y : ℤ) w).map fun t => t.2 * T (neg Y) (neg t.1))
        = (actWord c h₂ (y : ℤ) w).map fun t => t.2 * torusWord2 c h₁ h₂ d Y t.1 := by
      refine List.map_congr_left fun t ht => ?_
      rw [ih hY' t.1 (posSt_actWord c h₂ hw (y : ℤ) t ht)]
    rw [e2] at e
    rw [torusWord2]
    simp only [smul_eq_mul, Int.cast_natCast] at e
    linear_combination e

/-- Uniqueness of the two-weight pairing (l.2076–2081). -/
theorem twoWeight_unique {T' : Verma R c h₁ →ₗ[R] Verma R c h₂ →ₗ[R] R}
    (hT : IsTwoWeightPairing d T) (hT' : IsTwoWeightPairing d T') : T = T' :=
  linearMap_ext fun Y hY => linearMap_ext fun w hw => by
    rw [twoWeight_torusWord hT Y hY w hw, twoWeight_torusWord hT' Y hY w hw]

/-- Swapping `(Δ₁,u) ↔ (Δ₂,v)` and `m ↦ -m` leaves (10.1) unchanged (l.2085–2088). -/
theorem IsTwoWeightPairing.flip {T' : Verma R c h₂ →ₗ[R] Verma R c h₁ →ₗ[R] R}
    (hT' : IsTwoWeightPairing d T') : IsTwoWeightPairing d T'.flip := by
  refine ⟨hT'.1, fun n u v => ?_⟩
  have e := hT'.2 (-n) v u
  rw [neg_neg] at e
  simp only [LinearMap.flip_apply]
  push_cast at e
  linear_combination -e

/-- The Shapovalov form satisfies (10.1) with `Δ₁ = Δ₂` and `d = 0` (l.2089–2095). -/
theorem IsShapovalov.isTwoWeight {h : R} {B : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R}
    (hB : IsShapovalov B) : IsTwoWeightPairing 0 B := by
  refine ⟨hB.1, fun n u v => ?_⟩
  have e1 := hB.2 (-n) u v
  have e2 := hB.2 0 u v
  rw [neg_neg] at e1
  rw [neg_zero] at e2
  rw [e1, e2]
  ring

end Verma

section Naturality

variable {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S)

theorem phi2_map (h₁ h₂ d : R) (w : List ℕ) :
    phi2 (f h₁) (f h₂) (f d) w = f (phi2 h₁ h₂ d w) := by
  induction w with
  | nil => simp [phi2]
  | cons m w ih => simp only [phi2, ih, map_mul, map_add, map_sub, map_natCast]

theorem torusWord2_map (c h₁ h₂ d : R) : ∀ (Y w : List ℕ),
    torusWord2 (f c) (f h₁) (f h₂) (f d) Y w = f (torusWord2 c h₁ h₂ d Y w)
  | [], w => by simp [torusWord2, phi2_map]
  | y :: Y, w => by
    unfold torusWord2
    rw [actWord_map, torusWord2_map c h₁ h₂ d Y w]
    simp only [map_add, map_mul, map_sub, map_natCast, mapSt, List.map_map]
    congr 1
    rw [map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp [torusWord2_map c h₁ h₂ d Y t.1]

end Naturality

/-- Paper label: lem:two-weight-ward -/
theorem lem_two_weight_ward_of_cited (hE : Cited_TwoWeightPairingExists) :
    Stmt_lem_two_weight_ward := by
  refine ⟨fun c Δ₁ Δ₂ d => ?_, fun N₁ N₂ Y Y' => ?_, fun c Δ₁ Δ₂ d T T' hT hT' u v => ?_,
    fun c Δ T B hT hB u v => ?_⟩
  · obtain ⟨T, hT⟩ := hE c Δ₁ Δ₂ d
    exact ⟨T, hT, fun T' hT' => Verma.twoWeight_unique hT' hT⟩
  · refine ⟨torusWord2 (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2)
      (MvPolynomial.X 3) Y.word Y'.word, fun c Δ₁ Δ₂ d T hT => ?_⟩
    rw [Verma.twoWeight_torusWord hT _ (word_pos Y) _ (word_pos Y')]
    have h := torusWord2_map
      ((MvPolynomial.aeval ![c, Δ₁, Δ₂, d] : MvPolynomial (Fin 4) ℚ →ₐ[ℚ] ℂ) :
        MvPolynomial (Fin 4) ℚ →+* ℂ)
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) Y.word Y'.word
    simp only [AlgHom.coe_toRingHom, RingHom.coe_coe, MvPolynomial.aeval_X] at h
    simpa using h
  · have := Verma.twoWeight_unique hT hT'.flip
    rw [this, LinearMap.flip_apply]
  · rw [Verma.twoWeight_unique hT hB.isTwoWeight]

example (hE : Cited_TwoWeightPairingExists) : Stmt_lem_two_weight_ward :=
  lem_two_weight_ward_of_cited hE

end Virasoro
