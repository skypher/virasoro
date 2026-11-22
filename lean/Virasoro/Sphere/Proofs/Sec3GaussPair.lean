import Virasoro.Sphere.Proofs.Sec3GaussRestrict
import Virasoro.Sphere.Proofs.Sec3GaussTrunc
import Virasoro.Sphere.Proofs.Sec3GaussSubs
import Virasoro.Sphere.Proofs.Sec3LamRegular

/-!
# The pairing `ℬ(z) mod z^{N+1}` as a Fock pairing in `N` modes (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.637–640.  By Lemma 3.2(ii), `ℬ_j` is the pairing (3.1) of the level-`j` parts
of the two Ward solutions.  In `A[[z]]/(z^{N+1})`, the coefficient of `z^j` (`j ≤ N`) of the
pairing `fockP N N z` of the product of the two solutions restricted to the modes `≤ N` is that
level-`j` pairing: `fockP` weights `u^g ū^g` by `∏ g_m!/(2m)^{g_m} z^{|g|}`, and a monomial of
level `j ≤ N` involves only the modes `≤ N`.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open MvPowerSeries

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩

section Level

variable {N : ℕ}

theorem lvl_mapDomain (g : Fin N →₀ ℕ) : lvl (Finsupp.mapDomain (modeEmb N) g) = wtF (⇑g) := by
  show Finsupp.weight fockWeight _ = _
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index_inj modeEmb_injective,
    Finsupp.sum_fintype _ _ (fun i => by simp), wtF]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [fockWeight, modeEmb_coe, mul_comm]

theorem mul_le_lvl (α : ℕ+ →₀ ℕ) (m : ℕ+) : (m : ℕ) * α m ≤ lvl α := by
  by_cases hm : m ∈ α.support
  · show _ ≤ Finsupp.weight fockWeight α
    rw [Finsupp.weight_apply, Finsupp.sum]
    have := Finset.single_le_sum (f := fun i : ℕ+ => α i • fockWeight i)
      (fun i _ => Nat.zero_le _) hm
    simpa [fockWeight, mul_comm] using this
  · rw [Finsupp.notMem_support_iff.1 hm, mul_zero]
    exact Nat.zero_le _

/-- `∏_m α_m!/(2m)^{α_m}` as a rational number. -/
noncomputable def fockNormQ (α : ℕ+ →₀ ℕ) : ℚ :=
  α.prod fun m a => (a.factorial : ℚ) / (2 * ((m : ℕ) : ℚ)) ^ a

theorem fockNorm_eq (α : ℕ+ →₀ ℕ) : fockNorm α = ((fockNormQ α : ℚ) : ℂ) := by
  simp [fockNorm, fockNormQ, Finsupp.prod]

theorem fockNormQ_map (g : Fin N →₀ ℕ) :
    nrmF (⇑g) = fockNormQ (Finsupp.mapDomain (modeEmb N) g) := by
  rw [fockNormQ, Finsupp.prod_mapDomain_index_inj modeEmb_injective,
    Finsupp.prod_fintype _ _ (fun i => by simp), nrmF]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [modeEmb_coe]

end Level

section Pair

variable {N : ℕ} {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The coefficient of `z^j`, `j ≤ N`, of the `N`-mode Fock pairing of a product of a series in
the `u_m` and one in the `ū_m`, both with coefficients constant in `z`: the pairing (3.1) of the
level-`j` parts. -/
theorem cf_fockP_pair (G1 G2 : MvPowerSeries ℕ+ A) {j : ℕ} (hj : j ≤ N) :
    cfT j (fockP N N (mkT N A PowerSeries.X)
        (subst (eS (S := TR N A) Sum.inl) (map ((mkT N A).comp PowerSeries.C) G1) *
          subst (eS (S := TR N A) Sum.inr) (map ((mkT N A).comp PowerSeries.C) G2))) =
      ∑ α ∈ (finite_level j).toFinset,
        algebraMap ℚ A (fockNormQ α) * (coeff α G1 * coeff α G2) := by
  classical
  rw [fockP_subst_mul, cf_sum _ _ hj]
  have h1 : ∀ g : Fin N →₀ ℕ,
      cfT j (algebraMap ℚ (TR N A) (nrmF ⇑g) * mkT N A PowerSeries.X ^ wtF ⇑g *
        (coeff (Finsupp.mapDomain (modeEmb N) g) (map ((mkT N A).comp PowerSeries.C) G1) *
          coeff (Finsupp.mapDomain (modeEmb N) g) (map ((mkT N A).comp PowerSeries.C) G2))) =
      if wtF ⇑g = j then algebraMap ℚ A (nrmF ⇑g) *
        (coeff (Finsupp.mapDomain (modeEmb N) g) G1 *
          coeff (Finsupp.mapDomain (modeEmb N) g) G2) else 0 := by
    intro g
    rw [coeff_map, coeff_map, ← map_mul, algebraMap_TR, RingHom.comp_apply,
      cf_C_mul_X_pow_mul hj]
    split_ifs with h h' h'
    · rw [cf_mkT (by omega), PowerSeries.coeff_C, if_pos (by omega)]
    · rw [cf_mkT (by omega), PowerSeries.coeff_C, if_neg (by omega), mul_zero]
    · omega
    · rfl
  rw [Finset.sum_congr rfl fun g _ => h1 g, ← Finset.sum_filter]
  refine Finset.sum_bij (fun g _ => Finsupp.mapDomain (modeEmb N) g) ?_ ?_ ?_ ?_
  · intro g hg
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, lvl_mapDomain]
    exact (Finset.mem_filter.1 hg).2
  · intro g _ g' _ h
    exact Finsupp.mapDomain_injective modeEmb_injective h
  · intro α hα
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα
    have hb : ∀ m : ℕ+, α m ≠ 0 → (m : ℕ) ≤ N ∧ α m ≤ N := by
      intro m hm
      have h1 := mul_le_lvl α m
      have h2 := m.pos
      have h3 : 0 < α m := Nat.pos_of_ne_zero hm
      constructor <;> nlinarith
    have hmap : Finsupp.mapDomain (modeEmb N)
        (Finsupp.comapDomain (modeEmb N) α modeEmb_injective.injOn) = α :=
      Finsupp.mapDomain_comapDomain _ modeEmb_injective α fun m hm =>
        (mem_range_modeEmb m).2 (hb m (Finsupp.mem_support_iff.1 hm)).1
    refine ⟨Finsupp.comapDomain (modeEmb N) α modeEmb_injective.injOn, ?_, hmap⟩
    rw [Finset.mem_filter, Finset.mem_Iic, Finsupp.le_def]
    refine ⟨fun i => ?_, ?_⟩
    · rw [Finsupp.comapDomain_apply]
      show _ ≤ N
      by_cases h0 : α (modeEmb N i) = 0
      · rw [h0]
        exact Nat.zero_le _
      · exact (hb _ h0).2
    · rw [← lvl_mapDomain, hmap, hα]
  · intro g _
    rw [fockNormQ_map]

end Pair

section PairK

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)

include hF hK in
/-- The pairing `pairK` of the level-`j` parts of the two Ward solutions, expanded at `λ = ∞`,
as a sum over the monomials of level `j`. -/
theorem EInf_pairK (μ : ℝ) (hμ : 0 < μ) (Δe : Fin 4 → ℝ) (j : ℕ) :
    EInf (pairK μ Δe j) =
      ∑ α ∈ (finite_level j).toFinset, algebraMap ℚ LL (fockNormQ α) *
        (coeff α (map EInf (wardSeries (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ)))) *
          coeff α (map (EInf.comp conjK) (wardSeries (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ))))) := by
  classical
  have hW := wardRat_isWard hF hK μ hμ (Δe 0 : ℂ) (Δe 1 : ℂ)
  have hsub : (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ) j).support ⊆ (finite_level j).toFinset := by
    intro α hα
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact hW.2.1 j (MvPolynomial.mem_support_iff.1 hα)
  rw [pairK, map_sum, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun α hα => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hα
    rw [coeff_map, coeff_map, coeff_wardSeries, coeff_wardSeries, hα, map_mul, map_mul, EInf_C,
      fockNorm_eq, RingHom.comp_apply]
    have e : (HahnSeries.C ((fockNormQ α : ℚ) : ℂ) : LL) = algebraMap ℚ LL (fockNormQ α) := by
      rw [eq_ratCast (algebraMap ℚ LL), map_ratCast]
    rw [e]
    ring
  · intro α _ hα
    rw [MvPolynomial.notMem_support_iff.1 hα, mul_zero, zero_mul, map_zero]

include hF hK in
/-- Step 1 of Lemma 3.3(iii) (sphere/paper.tex l.637–640): in `ℂ((t))[[z]]/(z^{N+1})`, `t = 1/λ`,
the coefficient of `z^j` of the `N`-mode Fock pairing of the two Ward solutions is `ℬ_j`. -/
theorem cf_fockP_ward {N : ℕ} (μ : ℝ) (hμ : 0 < μ) (Δe : Fin 4 → ℝ) {j : ℕ} (hj : j ≤ N) :
    cfT j (fockP N N (mkT N LL PowerSeries.X)
        (subst (eS (S := TR N LL) Sum.inl)
            (map ((mkT N LL).comp PowerSeries.C)
              (map EInf (wardSeries (wardRat μ (Δe 0 : ℂ) (Δe 1 : ℂ))))) *
          subst (eS (S := TR N LL) Sum.inr)
            (map ((mkT N LL).comp PowerSeries.C)
              (map (EInf.comp conjK) (wardSeries (wardRat μ (Δe 3 : ℂ) (Δe 2 : ℂ))))))) =
      EInf (pairK μ Δe j) := by
  rw [cf_fockP_pair _ _ hj, EInf_pairK hF hK μ hμ]

end PairK

end Virasoro.Sphere
