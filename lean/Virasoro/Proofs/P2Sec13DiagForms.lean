import Virasoro.Proofs.P2Sec13DiagOrth
import Virasoro.Proofs.P2Sec11VertexRad
import Virasoro.Proofs.BaseChange

/-!
# Lemma 13.1, Step 4: the forms `B̄^{(1)}_τ` and `ρ̄^{(1)}_τ` on `J^1_τ` (paper.tex l.2997–3017)

"For `a(τ), b(τ) ∈ 𝒥_τ^{(1)}` … shifting either lift by `τ u(τ)` changes `ρ̄_{V,τ}(a,b)` by
`O(τ²)`, so `ρ̄^{(1)}_τ(a(0),b(0)) := [τ¹] ρ̄_{V,τ}(a(τ),b(τ))` is well defined … taking `[τ¹]`
of the Ward identity … shows that `ρ̄^{(1)}_τ` satisfies the exact `V_{d⋆}(1)` Ward identity on
`L(c⋆,ν₂)`.  By uniqueness of the contravariant and primary forms … `B̄^{(1)}_τ = α γ B̄_{L(ν₂)}` and
`ρ̄^{(1)}_τ = α g̃_ρ ρ̄_{L(ν₂),d⋆}`."

Here `b ↦ b⋆ + X`, the module is `M(c(X),h_{R,S}(X))` over `ℂ⟦X⟧`, `J = J¹(c⋆,μ)`; the forms
`R_B`, `R_ρ` are the `X¹`-coefficients of `B_X`, `ρ_X` on lifts.  On the image of
`j : M(c⋆,ν₂) → J` they are their value on `χ₂` times the Shapovalov form and the primary pairing
of `M(c⋆,ν₂)` (`ward_eq_smul_pairing`).
-/

namespace Virasoro

section BC

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (f : R →+* S)
  {c h d : R} {c' h' d' : S} (hc : f c = c') (hh : f h = h') (hd : f d = d')

include hd in
/-- The primary pairings correspond under the change of coefficient ring. -/
theorem Verma.pairing_baseChange (u v : Verma R c h) :
    Verma.pairing c' h' d' (Verma.baseChange f hc hh u) (Verma.baseChange f hc hh v) =
      f (Verma.pairing c h d u v) := by
  refine Verma.induction_neg (P := fun u => ∀ v : Verma R c h,
    Verma.pairing c' h' d' (Verma.baseChange f hc hh u) (Verma.baseChange f hc hh v)
      = f (Verma.pairing c h d u v)) ?_ ?_ ?_ u v
  · intro Y hY v
    refine Verma.induction_neg (P := fun v =>
      Verma.pairing c' h' d' (Verma.baseChange f hc hh (Verma.neg Y)) (Verma.baseChange f hc hh v)
        = f (Verma.pairing c h d (Verma.neg Y) v)) ?_ ?_ ?_ v
    · intro w hw
      rw [Verma.baseChange_neg, Verma.baseChange_neg,
        Verma.primary_torusWord (Verma.isPrimaryPairing_pairing d') Y hY w hw,
        Verma.primary_torusWord (Verma.isPrimaryPairing_pairing d) Y hY w hw,
        ← hc, ← hh, ← hd, torusWord_map]
    · intro a b ha hb
      simp only [map_add, ha, hb]
    · intro r a ha
      simp only [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, map_mul, ha]
  · intro a b ha hb v
    simp only [map_add, LinearMap.add_apply, ha, hb]
  · intro r a ha v
    simp only [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, ha]

end BC

/-- At `d = 0` the primary pairing is the Shapovalov form. -/
theorem pairing_zero_eq_shap {c h : ℂ} : Verma.pairing c h 0 = Verma.shap c h := by
  refine Verma.primary_unique (Verma.isPrimaryPairing_pairing 0) ⟨Verma.isShapovalov_shap.1,
    fun n u v => ?_⟩
  have h1 := Verma.isShapovalov_shap.2 (-n) u v
  have h2 := Verma.isShapovalov_shap.2 0 u v
  rw [neg_neg] at h1
  rw [neg_zero] at h2
  rw [h1, h2]
  ring

namespace P2

open Verma PowerSeries

open scoped PowerSeries

section Forms

variable {b : ℂ} {R S : ℕ}

/-- Evaluation at `X = 0`: `M(c(X),h_{R,S}(X)) → M(c⋆,h_{R,S}(b⋆))`. -/
noncomputable def ev0 (b : ℂ) (R S : ℕ) :
    Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b) →ₛₗ[(constantCoeff : ℂ⟦X⟧ →+* ℂ)]
      Verma ℂ (kacC b) (kacH R S b) :=
  Verma.baseChange (constantCoeff : ℂ⟦X⟧ →+* ℂ) (constantCoeff_cLoc b) (constantCoeff_hLoc R S b)

theorem ev0_L (n : ℤ) (U : Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b)) :
    ev0 b R S (L n U) = L n (ev0 b R S U) :=
  Verma.baseChange_L _ _ _ n U

theorem ev0_pbwCoord (N : ℕ) (w : Nat.Partition N → ℂ⟦X⟧) :
    ev0 b R S (pbwCoord N w) = pbwCoord N fun Y => constantCoeff (w Y) :=
  Verma.baseChange_pbwCoord _ _ _ N w

theorem ev0_surjective (x : Verma ℂ (kacC b) (kacH R S b)) : ∃ W, ev0 b R S W = x := by
  obtain ⟨T, hT⟩ := exists_decomp x
  refine ⟨∑ M ∈ T, pbwCoord M fun Y => (C (Verma.comp M x Y) : ℂ⟦X⟧), ?_⟩
  rw [map_sum]
  conv_rhs => rw [hT]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [ev0_pbwCoord]
  congr 1

set_option maxHeartbeats 2000000 in
theorem ev0_ker {U : Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b)} (h : ev0 b R S U = 0) :
    ∃ U', U = (X : ℂ⟦X⟧) • U' := by
  obtain ⟨T, hT⟩ := exists_decomp U
  have hc : ∀ (M : ℕ) (Y : Nat.Partition M), constantCoeff (Verma.comp M U Y) = 0 := by
    intro M Y
    rw [← comp_baseChange (constantCoeff : ℂ⟦X⟧ →+* ℂ) (constantCoeff_cLoc b)
      (constantCoeff_hLoc R S b) M U Y]
    change Verma.comp M (ev0 b R S U) Y = 0
    rw [h, map_zero]
    rfl
  choose q hq using fun (M : ℕ) (Y : Nat.Partition M) => X_dvd_iff.2 (hc M Y)
  refine ⟨∑ M ∈ T, pbwCoord M (q M), ?_⟩
  conv_lhs => rw [hT]
  have hM : ∀ M ∈ T, pbwCoord (c := cLoc b) (h := hLoc R S b) M (Verma.comp M U) =
      (X : ℂ⟦X⟧) • pbwCoord (c := cLoc b) (h := hLoc R S b) M (q M) := by
    intro M _
    rw [← LinearMap.map_smul (pbwCoord (c := cLoc b) (h := hLoc R S b) M)]
    congr 1
    funext Y
    rw [Pi.smul_apply, smul_eq_mul, ← hq M Y]
  rw [Finset.sum_congr rfl hM]
  exact (Finset.smul_sum (r := (X : ℂ⟦X⟧))
    (f := fun M => pbwCoord (c := cLoc b) (h := hLoc R S b) M (q M)) (s := T)).symm

/-- A chosen lift. -/
noncomputable def lft (b : ℂ) (R S : ℕ) (x : Verma ℂ (kacC b) (kacH R S b)) :
    Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b) :=
  Classical.choose (ev0_surjective (b := b) (R := R) (S := S) x)

theorem ev0_lft (x : Verma ℂ (kacC b) (kacH R S b)) : ev0 b R S (lft b R S x) = x :=
  Classical.choose_spec (ev0_surjective x)

theorem coeff_one_mul' (a c : ℂ⟦X⟧) :
    coeff 1 (a * c) = constantCoeff a * coeff 1 c + coeff 1 a * constantCoeff c := by
  rw [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_cons, Finset.Nat.antidiagonal_zero,
    Finset.sum_map, Finset.sum_singleton]
  simp only [Function.Embedding.coe_prodMap, Function.Embedding.coeFn_mk, Prod.map_apply,
    Function.Embedding.refl_apply, coeff_zero_eq_constantCoeff_apply]

/-- The `X¹`-coefficient of a form on lifts depends only on the values at `X = 0` when these
lie in the radical of the value of the form (l.2978–2983, 3000–3003). -/
theorem coeff_one_indep
    (BX : Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b) →ₗ[ℂ⟦X⟧] Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b) →ₗ[ℂ⟦X⟧] ℂ⟦X⟧)
    (B0 : Verma ℂ (kacC b) (kacH R S b) → Verma ℂ (kacC b) (kacH R S b) → ℂ)
    (hcomp : ∀ U V, constantCoeff (BX U V) = B0 (ev0 b R S U) (ev0 b R S V))
    {x y : Verma ℂ (kacC b) (kacH R S b)} (hx : ∀ z, B0 x z = 0) (hy : ∀ z, B0 z y = 0)
    {U U' V V' : Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b)} (hU : ev0 b R S U = x)
    (hU' : ev0 b R S U' = x) (hV : ev0 b R S V = y) (hV' : ev0 b R S V' = y) :
    coeff 1 (BX U V) = coeff 1 (BX U' V') := by
  obtain ⟨D, hD⟩ := ev0_ker (U := U - U') (by rw [map_sub, hU, hU', sub_self])
  obtain ⟨D', hD'⟩ := ev0_ker (U := V - V') (by rw [map_sub, hV, hV', sub_self])
  have e1 : U = U' + (X : ℂ⟦X⟧) • D := by rw [← hD]; abel
  have e2 : V = V' + (X : ℂ⟦X⟧) • D' := by rw [← hD']; abel
  have hexp : BX U V = BX U' V' + (X : ℂ⟦X⟧) * (BX D V' + BX U' D') +
      (X : ℂ⟦X⟧) ^ 2 * BX D D' := by
    rw [e1, e2]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hD0 : ev0 b R S D = 0 ∨ True := Or.inr trivial
  clear hD0
  have k1 : ∀ a : ℂ⟦X⟧, coeff 1 ((X : ℂ⟦X⟧) * a) = constantCoeff a := fun a => by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have k2 : ∀ a : ℂ⟦X⟧, coeff 1 ((X : ℂ⟦X⟧) ^ 2 * a) = 0 := fun a => by
    rw [coeff_X_pow_mul', if_neg (by norm_num)]
  rw [hexp, map_add, map_add, k1, k2, map_add, hcomp, hcomp, hV', hU', hy, hx, add_zero, add_zero,
    add_zero]

variable (b R S) in
/-- `R_B(x,y) = [X¹] B_X(x̃,ỹ)`. -/
noncomputable def RB (x y : Verma ℂ (kacC b) (kacH R S b)) : ℂ :=
  coeff 1 (shap (cLoc b) (hLoc R S b) (lft b R S x) (lft b R S y))

variable (b R S) in
/-- `R_ρ(x,y) = [X¹] ρ_X(x̃,ỹ)` at `d(X) = h_{u,v}(b⋆+X)`. -/
noncomputable def Rρ (u v : ℤ) (x y : Verma ℂ (kacC b) (kacH R S b)) : ℂ :=
  coeff 1 (pairing (cLoc b) (hLoc R S b) (hLoc u v b) (lft b R S x) (lft b R S y))

/-- The radical `J¹(c⋆,μ)` of the Shapovalov form, on both sides. -/
theorem shap_rad {x : Verma ℂ (kacC b) (kacH R S b)} (hx : x ∈ jantzen (kacC b) (kacH R S b) 1) :
    (∀ z, shap (kacC b) (kacH R S b) z x = 0) ∧ ∀ z, shap (kacC b) (kacH R S b) x z = 0 := by
  have h := jantzen_one_eq_radical (kacC b) (kacH R S b)
  have hx' : x ∈ ({v | ∀ u, shap (kacC b) (kacH R S b) u v = 0} : Set _) := by
    rw [← h]; exact hx
  exact ⟨hx', fun z => by rw [isShapovalov_shap.symm]; exact hx' z⟩

theorem jantzen_one_L {x : Verma ℂ (kacC b) (kacH R S b)}
    (hx : x ∈ jantzen (kacC b) (kacH R S b) 1) (n : ℤ) :
    L n x ∈ jantzen (kacC b) (kacH R S b) 1 := by
  have h := jantzen_one_eq_radical (kacC b) (kacH R S b)
  rw [← SetLike.mem_coe, h]
  intro z
  have e := isShapovalov_shap.2 (-n) z x
  rw [neg_neg] at e
  rw [← e]
  exact (shap_rad hx).1 _

theorem shap_comp (U V : Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b)) :
    constantCoeff (shap (cLoc b) (hLoc R S b) U V) =
      shap (kacC b) (kacH R S b) (ev0 b R S U) (ev0 b R S V) :=
  (Verma.shap_baseChange _ (constantCoeff_cLoc b) (constantCoeff_hLoc R S b) U V).symm

theorem pairing_comp (u v : ℤ) (U V : Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b)) :
    constantCoeff (pairing (cLoc b) (hLoc R S b) (hLoc u v b) U V) =
      pairing (kacC b) (kacH R S b) (kacH u v b) (ev0 b R S U) (ev0 b R S V) :=
  (Verma.pairing_baseChange _ (constantCoeff_cLoc b) (constantCoeff_hLoc R S b)
    (constantCoeff_hLoc u v b) U V).symm

/-- Lift independence of `R_B` on `J¹`. -/
theorem RB_lift {x y : Verma ℂ (kacC b) (kacH R S b)} (hx : x ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy : y ∈ jantzen (kacC b) (kacH R S b) 1) {U V : Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b)}
    (hU : ev0 b R S U = x) (hV : ev0 b R S V = y) :
    coeff 1 (shap (cLoc b) (hLoc R S b) U V) = RB b R S x y :=
  coeff_one_indep _ (fun z z' => shap (kacC b) (kacH R S b) z z') shap_comp (shap_rad hx).2
    (shap_rad hy).1 hU (ev0_lft x) hV (ev0_lft y)

/-- Lift independence of `R_ρ` on `J¹ ⊂ rad ρ₀`. -/
theorem Rρ_lift {u v : ℤ}
    (hrad : ∀ x ∈ jantzen (kacC b) (kacH R S b) 1, ∀ z,
      pairing (kacC b) (kacH R S b) (kacH u v b) x z = 0 ∧
        pairing (kacC b) (kacH R S b) (kacH u v b) z x = 0)
    {x y : Verma ℂ (kacC b) (kacH R S b)} (hx : x ∈ jantzen (kacC b) (kacH R S b) 1)
    (hy : y ∈ jantzen (kacC b) (kacH R S b) 1) {U V : Verma ℂ⟦X⟧ (cLoc b) (hLoc R S b)}
    (hU : ev0 b R S U = x) (hV : ev0 b R S V = y) :
    coeff 1 (pairing (cLoc b) (hLoc R S b) (hLoc u v b) U V) = Rρ b R S u v x y :=
  coeff_one_indep _ (fun z z' => pairing (kacC b) (kacH R S b) (kacH u v b) z z')
    (pairing_comp u v) (fun z => (hrad x hx z).1) (fun z => (hrad y hy z).2) hU (ev0_lft x) hV
    (ev0_lft y)

section Hom

variable {h₂ : ℂ} (j : Verma ℂ (kacC b) h₂ →ₗ[ℂ] Verma ℂ (kacC b) (kacH R S b))
  (hjL : ∀ (n : ℤ) (v : Verma ℂ (kacC b) h₂), j (L n v) = L n (j v))
  (hjJ : ∀ v, j v ∈ jantzen (kacC b) (kacH R S b) 1)

include hjL hjJ in
/-- `R_B` on the image of `j : M(c⋆,ν₂) → J¹` is `R_B(χ₂,χ₂)` times the Shapovalov form of
`M(c⋆,ν₂)` (l.3012–3014). -/
theorem RB_hom (u' v' : Verma ℂ (kacC b) h₂) :
    RB b R S (j u') (j v') = RB b R S (j hw) (j hw) * shap (kacC b) h₂ u' v' := by
  have ladd : ∀ x x' y, x ∈ jantzen (kacC b) (kacH R S b) 1 → x' ∈ jantzen (kacC b) (kacH R S b) 1 →
      y ∈ jantzen (kacC b) (kacH R S b) 1 → RB b R S (x + x') y = RB b R S x y + RB b R S x' y := by
    intro x x' y hx hx' hy
    rw [← RB_lift (Submodule.add_mem _ hx hx') hy (U := lft b R S x + lft b R S x')
      (by rw [map_add, ev0_lft, ev0_lft]) (ev0_lft y), map_add, LinearMap.add_apply, map_add]
    rfl
  have radd : ∀ x y y', x ∈ jantzen (kacC b) (kacH R S b) 1 → y ∈ jantzen (kacC b) (kacH R S b) 1 →
      y' ∈ jantzen (kacC b) (kacH R S b) 1 → RB b R S x (y + y') = RB b R S x y + RB b R S x y' := by
    intro x y y' hx hy hy'
    rw [← RB_lift hx (Submodule.add_mem _ hy hy') (V := lft b R S y + lft b R S y') (ev0_lft x)
      (by rw [map_add, ev0_lft, ev0_lft]), map_add, map_add]
    rfl
  have lsmul : ∀ (a : ℂ) x y, x ∈ jantzen (kacC b) (kacH R S b) 1 →
      y ∈ jantzen (kacC b) (kacH R S b) 1 → RB b R S (a • x) y = a * RB b R S x y := by
    intro a x y hx hy
    rw [← RB_lift (Submodule.smul_mem _ a hx) hy (U := (C a : ℂ⟦X⟧) • lft b R S x)
      (by rw [LinearMap.map_smulₛₗ, ev0_lft, constantCoeff_C]) (ev0_lft y), map_smul,
      LinearMap.smul_apply, smul_eq_mul, coeff_C_mul]
    rfl
  have rsmul : ∀ (a : ℂ) x y, x ∈ jantzen (kacC b) (kacH R S b) 1 →
      y ∈ jantzen (kacC b) (kacH R S b) 1 → RB b R S x (a • y) = a * RB b R S x y := by
    intro a x y hx hy
    rw [← RB_lift hx (Submodule.smul_mem _ a hy) (V := (C a : ℂ⟦X⟧) • lft b R S y) (ev0_lft x)
      (by rw [LinearMap.map_smulₛₗ, ev0_lft, constantCoeff_C]), map_smul, smul_eq_mul,
      coeff_C_mul]
    rfl
  have hLmove : ∀ (k : ℤ) x y, x ∈ jantzen (kacC b) (kacH R S b) 1 →
      y ∈ jantzen (kacC b) (kacH R S b) 1 → RB b R S (L k x) y = RB b R S x (L (-k) y) := by
    intro k x y hx hy
    rw [← RB_lift (jantzen_one_L hx k) hy (U := L k (lft b R S x)) (by rw [ev0_L, ev0_lft])
      (ev0_lft y), isShapovalov_shap.2 k, RB_lift hx (jantzen_one_L hy (-k)) (ev0_lft x)
      (by rw [ev0_L, ev0_lft])]
  let η : Verma ℂ (kacC b) h₂ →ₗ[ℂ] Verma ℂ (kacC b) h₂ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun u' v' => RB b R S (j u') (j v'))
      (fun u₁ u₂ v => by rw [map_add, ladd _ _ _ (hjJ u₁) (hjJ u₂) (hjJ v)])
      (fun a u v => by rw [map_smul, lsmul a _ _ (hjJ u) (hjJ v), smul_eq_mul])
      (fun u v₁ v₂ => by rw [map_add, radd _ _ _ (hjJ u) (hjJ v₁) (hjJ v₂)])
      (fun a u v => by rw [map_smul, rsmul a _ _ (hjJ u) (hjJ v), smul_eq_mul])
  have hη : ∀ u' v', η u' v' = RB b R S (j u') (j v') := fun _ _ => rfl
  have hW : IsWardPairing (0 : ℂ) η := by
    intro n u' v'
    rw [hη, hη, hη, hη, hη, hjL, hjL, hjL, hjL, hLmove _ _ _ (hjJ u') (hjJ v'), neg_neg,
      hLmove 0 _ _ (hjJ u') (hjJ v'), neg_zero]
    ring
  have := ward_eq_smul_pairing hW u' v'
  rw [hη, hη, pairing_zero_eq_shap] at this
  exact this

include hjL hjJ in
/-- `R_ρ` on the image of `j` is `R_ρ(χ₂,χ₂)` times the primary pairing of `M(c⋆,ν₂)`
(l.3004–3017). -/
theorem Rρ_hom {u v : ℤ}
    (hrad : ∀ x ∈ jantzen (kacC b) (kacH R S b) 1, ∀ z,
      pairing (kacC b) (kacH R S b) (kacH u v b) x z = 0 ∧
        pairing (kacC b) (kacH R S b) (kacH u v b) z x = 0)
    (u' v' : Verma ℂ (kacC b) h₂) :
    Rρ b R S u v (j u') (j v') =
      Rρ b R S u v (j hw) (j hw) * pairing (kacC b) h₂ (kacH u v b) u' v' := by
  have ladd : ∀ x x' y, x ∈ jantzen (kacC b) (kacH R S b) 1 → x' ∈ jantzen (kacC b) (kacH R S b) 1 →
      y ∈ jantzen (kacC b) (kacH R S b) 1 →
        Rρ b R S u v (x + x') y = Rρ b R S u v x y + Rρ b R S u v x' y := by
    intro x x' y hx hx' hy
    rw [← Rρ_lift hrad (Submodule.add_mem _ hx hx') hy (U := lft b R S x + lft b R S x')
      (by rw [map_add, ev0_lft, ev0_lft]) (ev0_lft y), map_add, LinearMap.add_apply, map_add]
    rfl
  have radd : ∀ x y y', x ∈ jantzen (kacC b) (kacH R S b) 1 → y ∈ jantzen (kacC b) (kacH R S b) 1 →
      y' ∈ jantzen (kacC b) (kacH R S b) 1 →
        Rρ b R S u v x (y + y') = Rρ b R S u v x y + Rρ b R S u v x y' := by
    intro x y y' hx hy hy'
    rw [← Rρ_lift hrad hx (Submodule.add_mem _ hy hy') (V := lft b R S y + lft b R S y')
      (ev0_lft x) (by rw [map_add, ev0_lft, ev0_lft]), map_add, map_add]
    rfl
  have lsmul : ∀ (a : ℂ) x y, x ∈ jantzen (kacC b) (kacH R S b) 1 →
      y ∈ jantzen (kacC b) (kacH R S b) 1 → Rρ b R S u v (a • x) y = a * Rρ b R S u v x y := by
    intro a x y hx hy
    rw [← Rρ_lift hrad (Submodule.smul_mem _ a hx) hy (U := (C a : ℂ⟦X⟧) • lft b R S x)
      (by rw [LinearMap.map_smulₛₗ, ev0_lft, constantCoeff_C]) (ev0_lft y), map_smul,
      LinearMap.smul_apply, smul_eq_mul, coeff_C_mul]
    rfl
  have rsmul : ∀ (a : ℂ) x y, x ∈ jantzen (kacC b) (kacH R S b) 1 →
      y ∈ jantzen (kacC b) (kacH R S b) 1 → Rρ b R S u v x (a • y) = a * Rρ b R S u v x y := by
    intro a x y hx hy
    rw [← Rρ_lift hrad hx (Submodule.smul_mem _ a hy) (V := (C a : ℂ⟦X⟧) • lft b R S y)
      (ev0_lft x) (by rw [LinearMap.map_smulₛₗ, ev0_lft, constantCoeff_C]), map_smul,
      smul_eq_mul, coeff_C_mul]
    rfl
  have hWard : ∀ (n : ℤ) x y, x ∈ jantzen (kacC b) (kacH R S b) 1 →
      y ∈ jantzen (kacC b) (kacH R S b) 1 →
        Rρ b R S u v (L (-n) x) y - Rρ b R S u v x (L n y) =
          Rρ b R S u v (L 0 x) y - Rρ b R S u v x (L 0 y) + (n : ℂ) * kacH u v b *
            Rρ b R S u v x y := by
    intro n x y hx hy
    have hT := (isPrimaryPairing_pairing (c := cLoc b) (h := hLoc R S b) (hLoc u v b)).2 n
      (lft b R S x) (lft b R S y)
    have h1 := congrArg (coeff 1) hT
    rw [map_sub, map_add, map_sub,
      Rρ_lift hrad (jantzen_one_L hx (-n)) hy (by rw [ev0_L, ev0_lft]) (ev0_lft y),
      Rρ_lift hrad hx (jantzen_one_L hy n) (ev0_lft x) (by rw [ev0_L, ev0_lft]),
      Rρ_lift hrad (jantzen_one_L hx 0) hy (by rw [ev0_L, ev0_lft]) (ev0_lft y),
      Rρ_lift hrad hx (jantzen_one_L hy 0) (ev0_lft x) (by rw [ev0_L, ev0_lft])] at h1
    rw [h1]
    congr 1
    rw [show ((n : ℂ⟦X⟧)) = C (n : ℂ) by simp, mul_assoc, coeff_C_mul,
      coeff_one_mul', pairing_comp, ev0_lft, ev0_lft, (hrad x hx y).1, mul_zero, add_zero,
      constantCoeff_hLoc]
    unfold Rρ
    ring
  let η : Verma ℂ (kacC b) h₂ →ₗ[ℂ] Verma ℂ (kacC b) h₂ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun u' v' => Rρ b R S u v (j u') (j v'))
      (fun u₁ u₂ w => by rw [map_add, ladd _ _ _ (hjJ u₁) (hjJ u₂) (hjJ w)])
      (fun a u₁ w => by rw [map_smul, lsmul a _ _ (hjJ u₁) (hjJ w), smul_eq_mul])
      (fun u₁ w₁ w₂ => by rw [map_add, radd _ _ _ (hjJ u₁) (hjJ w₁) (hjJ w₂)])
      (fun a u₁ w => by rw [map_smul, rsmul a _ _ (hjJ u₁) (hjJ w), smul_eq_mul])
  have hη : ∀ u' v', η u' v' = Rρ b R S u v (j u') (j v') := fun _ _ => rfl
  have hW : IsWardPairing (kacH u v b) η := by
    intro n u' v'
    rw [hη, hη, hη, hη, hη, hjL, hjL, hjL, hjL]
    exact hWard n _ _ (hjJ u') (hjJ v')
  have := ward_eq_smul_pairing hW u' v'
  rw [hη, hη] at this
  exact this

end Hom

end Forms

end P2

end Virasoro
