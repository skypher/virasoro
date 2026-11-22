import Virasoro.Cited
import Virasoro.Cited2
import Virasoro.Proofs.JantzenSub
import Virasoro.Proofs.Sec6Regular
import Virasoro.Proofs.P2Sec10Ward
import Virasoro.Proofs.P2Sec10OrbitArith
import Virasoro.Proofs.P2Sec11WardInd

/-!
# Theorem 9.1(i): descent of the Verma three-point form (paper.tex l.2559–2568)

`ρ(c⋆,λ,d)` descends to `L(c⋆,λ) × L(c⋆,λ)` iff `J¹(c⋆,λ) ⊂ rad ρ`, iff
`ρ(w⁺₁,v_λ) = ρ(w⁻₁,v_λ) = 0` (Lemma 10.3(i) and the Ward-induction fact), iff
`P_{r,s}(b⋆;λ,d) = P_{p-r,p'-s}(b⋆;λ,d) = 0` (Proposition 10.2(ii)), iff `d ∈ ℱ_{p,p'}(r,s)`
(Lemma 11.1(i)).
-/

namespace Virasoro

/-- The primary pairing is symmetric (equation (10.2) with `Δ₁ = Δ₂`). -/
theorem primary_symm {c h d : ℂ} {T : Verma ℂ c h →ₗ[ℂ] Verma ℂ c h →ₗ[ℂ] ℂ}
    (hT : Verma.IsPrimaryPairing d T) (u v : Verma ℂ c h) : T u v = T v u := by
  have hT2 : Verma.IsTwoWeightPairing d T := hT
  have h := Verma.twoWeight_unique hT2 hT2.flip
  conv_lhs => rw [h]
  rfl

/-- `ρ(w, v_h)` for a singular vector `w` of level `RS` in `M(c(b),h)`, `h = h_{R,S}(b)`,
vanishes iff `P_{R,S}(b;h,d) = 0` (Proposition 10.2(ii) and uniqueness of singular vectors). -/
theorem pairing_singular_fus (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique)
    (hF : Cited_FusionPolynomial) {b : ℂ} (hb : b ≠ 0) {R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (h : ℂ) (hh : h = kacH R S b) (d : ℂ)
    (T : Verma ℂ (kacC b) h →ₗ[ℂ] Verma ℂ (kacC b) h →ₗ[ℂ] ℂ) (hT : Verma.IsPrimaryPairing d T)
    (w : Verma ℂ (kacC b) h) (hw : Verma.IsSingular w (R * S)) :
    T w Verma.hw = 0 ↔ fusP R S b h d = 0 := by
  subst hh
  obtain ⟨p, ⟨hp1, hsing⟩, -⟩ := hH R S hR hS
  obtain ⟨-, h1, hs1, -, -⟩ := lem_regular_everywhere_of_cited hH R S hR hS p hp1 hsing b hb
  obtain ⟨a, ha⟩ := hU _ _ (R * S) _ w hs1 hw
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hw.1 (ha.trans (by module))
  obtain ⟨C₀, hC0, hC⟩ := hF R S hR hS b hb _ h1 hs1
  have hT2 : Verma.IsTwoWeightPairing d T := hT
  rw [ha, map_smul, LinearMap.smul_apply, hC (kacH R S b) d T hT2, smul_eq_mul, mul_eq_zero,
    mul_eq_zero]
  constructor
  · rintro (h | h | h)
    · exact absurd h ha0
    · exact absurd h hC0
    · exact h
  · exact fun h => Or.inr (Or.inr h)

/-- Descent is the vanishing of `ρ(w^±, v_h)` when `J¹ = U(Vir_-)w⁺ + U(Vir_-)w⁻`
(l.2560–2566). -/
theorem torusDescends_iff {c h d : ℂ} {wp wm : Verma ℂ c h} {ℓp ℓm : ℕ}
    (hwp : Verma.IsSingular wp ℓp) (hwm : Verma.IsSingular wm ℓm)
    (hJ1 : jantzen c h 1 = Verma.negSpan wp ⊔ Verma.negSpan wm)
    {T : Verma ℂ c h →ₗ[ℂ] Verma ℂ c h →ₗ[ℂ] ℂ} (hT : Verma.IsPrimaryPairing d T) :
    TorusDescends c h d ↔ (T wp Verma.hw = 0 ∧ T wm Verma.hw = 0) := by
  have hrad := jantzen_one_eq_radical c h
  have hmem : ∀ w : Verma ℂ c h, w ∈ Verma.negSpan w := fun w =>
    Submodule.subset_span ⟨[], by simp [VirEnv.negOp]⟩
  constructor
  · intro hdesc
    have hp : wp ∈ (jantzen c h 1 : Set (Verma ℂ c h)) := by
      rw [hJ1]; exact Submodule.mem_sup_left (hmem wp)
    have hm : wm ∈ (jantzen c h 1 : Set (Verma ℂ c h)) := by
      rw [hJ1]; exact Submodule.mem_sup_right (hmem wm)
    rw [hrad] at hp hm
    exact ⟨(hdesc T hT _ Verma.isShapovalov_shap wp hp Verma.hw).1,
      (hdesc T hT _ Verma.isShapovalov_shap wm hm Verma.hw).1⟩
  · rintro ⟨h1, h2⟩ T' hT' B hB u hu v
    obtain rfl : T' = T := Verma.primary_unique hT' hT
    rw [Verma.shapovalov_unique hB Verma.isShapovalov_shap] at hu
    have hu1 : u ∈ (jantzen c h 1 : Set (Verma ℂ c h)) := by rw [hrad]; exact hu
    rw [SetLike.mem_coe, hJ1, Submodule.mem_sup] at hu1
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := hu1
    have k1 := Verma.ward_induction hT'.2 (primary_symm hT') hwp h1 u₁ hu₁ v
    have k2 := Verma.ward_induction hT'.2 (primary_symm hT') hwm h2 u₂ hu₂ v
    constructor
    · rw [map_add, LinearMap.add_apply, k1.1, k2.1, add_zero]
    · rw [map_add, k1.2, k2.2, add_zero]

/-- Theorem 9.1(i) under the labelling `p'r + ps < pp'` (l.2559–2568). -/
theorem descent_iff_minimal (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hfus : Stmt_lem_fusion_injective) {p p' r s : ℕ} {b : ℂ}
    (hset : MinimalSetting p p' r s b) (d : ℂ) :
    TorusDescends (kacC b) (kacH r s b) d ↔ d ∈ fusionSet p p' r s b := by
  obtain ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn1, hb⟩ := id hset
  have hp : 0 < p := by omega
  have hp' : 0 < p' := by omega
  have hb0 : b ≠ 0 := by
    rintro rfl
    have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have hpc' : (p' : ℂ) ≠ 0 := by exact_mod_cast hp'.ne'
    rw [zero_pow two_ne_zero] at hb
    exact div_ne_zero (neg_ne_zero.2 hpc') hpc hb.symm
  have hμ : muOrb p p' r s true 0 = kacH r s b := by
    rw [kacH_momWt hp hp' hb, muOrb]
    congr 1
    simp [nOrb]
  have hrefl := kacH_reflect hp hp' hb hr.le hs.le
  have e := (hfus p p' r s b hp2 hp2' hcop hb hr0 hr hs0 hs).1 d
  rw [← hμ] at e ⊢
  obtain ⟨wp, wm, ⟨hsing, hlayer⟩, -⟩ := hJ p p' r s b hset true 0
  have hl1 : ellOrb p p' r s true (0 + 1) - ellOrb p p' r s true 0 = r * s := by
    simp [ellOrb, ellPlus]
  have hl2 : ellOrb p p' r s false (0 + 1) - ellOrb p p' r s true 0 = (p - r) * (p' - s) := by
    simp [ellOrb, ellMinus]
  obtain ⟨hwp, hwm⟩ := hsing 1 le_rfl
  rw [hl1] at hwp
  rw [hl2] at hwm
  have hT := Verma.isPrimaryPairing_pairing (c := kacC b) (h := muOrb p p' r s true 0) d
  rw [torusDescends_iff hwp hwm (hlayer 1 le_rfl) hT,
    pairing_singular_fus hH hU hF hb0 hr0 hs0 _ hμ d _ hT _ hwp,
    pairing_singular_fus hH hU hF hb0 (by omega : 0 < p - r) (by omega : 0 < p' - s) _
      (hμ.trans hrefl) d _ hT _ hwm]
  exact e

/-- Theorem 9.1(i) (l.2559–2568): for every interior `(r,s)` and every `d`, `ρ(c⋆,λ,d)`
descends to `L(c⋆,λ) × L(c⋆,λ)` iff `d ∈ ℱ_{p,p'}(r,s)`. -/
theorem descent_iff_of_cited (hJ : Cited_JantzenLayersOrbit) (hH : Cited_HJSNormalizations)
    (hU : Cited_SingularUnique) (hF : Cited_FusionPolynomial)
    (hfus : Stmt_lem_fusion_injective) (p p' r s : ℕ) (b : ℂ) (hp2 : 2 ≤ p) (hp2' : 2 ≤ p')
    (hcop : Nat.Coprime p p') (hb : b ^ 2 = -(p' : ℂ) / p) (hr0 : 0 < r) (hr : r < p)
    (hs0 : 0 < s) (hs : s < p') (d : ℂ) :
    TorusDescends (kacC b) (kacH r s b) d ↔ d ∈ fusionSet p p' r s b := by
  by_cases hn : p' * r + p * s < p * p'
  · exact descent_iff_minimal hJ hH hU hF hfus ⟨hp2, hp2', hcop, hr0, hr, hs0, hs, hn, hb⟩ d
  · -- relabel `(r,s) ↦ (p-r,p'-s)` (l.2163–2165)
    have hne : p' * r + p * s ≠ p * p' := by
      intro h
      have hz : (p' : ℤ) * r = p * ((p' : ℤ) - s) := by
        have : ((p' * r + p * s : ℕ) : ℤ) = ((p * p' : ℕ) : ℤ) := by rw [h]
        push_cast at this
        linarith
      have h0 := Int.eq_zero_of_abs_lt_dvd (coprime_two_dvd hcop hz).1
        (abs_lt.2 ⟨by omega, by omega⟩)
      omega
    have hn' : p' * (p - r) + p * (p' - s) < p * p' := by
      rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm p' p]
      have h1 : p' * r < p * p' := by
        rw [Nat.mul_comm p p']; exact Nat.mul_lt_mul_of_pos_left hr (by omega)
      have h2 : p * s < p * p' := Nat.mul_lt_mul_of_pos_left hs (by omega)
      omega
    have h := descent_iff_minimal hJ hH hU hF hfus
      ⟨hp2, hp2', hcop, (by omega : 0 < p - r), (by omega : p - r < p), (by omega : 0 < p' - s),
        (by omega : p' - s < p'), hn', hb⟩ d
    rw [← kacH_reflect (by omega) (by omega) hb hr.le hs.le] at h
    rw [h]
    simp only [fusionSet, Nat.sub_sub_self hr.le, Nat.sub_sub_self hs.le, min_comm (p - r) r,
      min_comm (p' - s) s]

end Virasoro
