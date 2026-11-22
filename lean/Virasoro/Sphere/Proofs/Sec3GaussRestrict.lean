import Virasoro.Sphere.Proofs.Sec3GaussFock

/-!
# Restriction to the modes `u_1, …, u_N` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.638–640: modulo `z^{N+1}` the pairing "depends only on `u_1,…,u_N` and
`ū_1,…,ū_N`".  A series in the variables `u_m` (`m ≥ 1`) is restricted to the first `N` modes
by the substitution `u_m ↦ x_{s(m)}` (`m ≤ N`), `u_m ↦ 0` (`m > N`); here are the coefficients
of the restricted series, of a product of a series in the `u_m` and one in the `ū_m`, and the
Fock pairing of such a product.
-/

namespace Virasoro.Sphere

open MvPowerSeries

section Restrict

variable {N : ℕ}

variable (N) in
/-- The mode `i + 1` of the index `i : Fin N`. -/
def modeEmb : Fin N → ℕ+ := fun i => ⟨(i : ℕ) + 1, Nat.succ_pos _⟩

theorem modeEmb_coe (i : Fin N) : ((modeEmb N i : ℕ+) : ℕ) = (i : ℕ) + 1 := rfl

theorem modeEmb_injective : Function.Injective (modeEmb N) := by
  intro i j h
  have := congrArg (fun m : ℕ+ => (m : ℕ)) h
  simp only [modeEmb_coe] at this
  exact Fin.ext (by omega)

theorem mem_range_modeEmb (m : ℕ+) : m ∈ Set.range (modeEmb N) ↔ (m : ℕ) ≤ N := by
  constructor
  · rintro ⟨i, rfl⟩
    exact i.isLt
  · intro h
    refine ⟨⟨(m : ℕ) - 1, by have := m.pos; omega⟩, PNat.eq ?_⟩
    rw [modeEmb_coe]
    have := m.pos
    simp only
    omega

variable {S : Type*} [CommRing S]

/-- The substitution `u_m ↦ x_{s(m)}` for `m ≤ N` and `u_m ↦ 0` for `m > N`. -/
noncomputable def eS (s : Fin N → Modes N) (m : ℕ+) : MvPowerSeries (Modes N) S :=
  if h : (m : ℕ) ≤ N then X (s ⟨(m : ℕ) - 1, by have := m.pos; omega⟩) else 0

theorem eS_modeEmb (s : Fin N → Modes N) (i : Fin N) : eS (S := S) s (modeEmb N i) = X (s i) := by
  rw [eS, dif_pos (show ((modeEmb N i : ℕ+) : ℕ) ≤ N from i.isLt)]
  congr 2

theorem eS_of_lt (s : Fin N → Modes N) (m : ℕ+) (h : N < (m : ℕ)) : eS (S := S) s m = 0 :=
  dif_neg (by omega)

theorem hasSubst_eS (s : Fin N → Modes N) : HasSubst (eS (S := S) s) where
  const_coeff m := by
    rw [eS]
    split_ifs <;> simp
  coeff_zero d := (Set.finite_range (modeEmb N)).subset fun m hm => by
    rw [mem_range_modeEmb]
    by_contra h
    exact hm (by rw [eS, dif_neg h, map_zero])

theorem prod_eS_map {s : Fin N → Modes N} (hs : Function.Injective s) (g : Fin N →₀ ℕ) :
    (Finsupp.mapDomain (modeEmb N) g).prod (fun m e => eS (S := S) s m ^ e) =
      monomial (Finsupp.mapDomain s g) 1 := by
  rw [Finsupp.prod_mapDomain_index_inj modeEmb_injective, monomial_one_eq,
    Finsupp.prod_mapDomain_index_inj hs]
  simp only [eS_modeEmb]

theorem prod_eS_eq_zero (s : Fin N → Modes N) (d : ℕ+ →₀ ℕ) (m : ℕ+) (hm : m ∈ d.support)
    (h : N < (m : ℕ)) : d.prod (fun m e => eS (S := S) s m ^ e) = 0 :=
  Finset.prod_eq_zero hm (by
    show eS (S := S) s m ^ d m = 0
    rw [eS_of_lt s m h, zero_pow (Finsupp.mem_support_iff.1 hm)])

theorem exists_map_or (d : ℕ+ →₀ ℕ) :
    (∃ g : Fin N →₀ ℕ, d = Finsupp.mapDomain (modeEmb N) g) ∨
      ∃ m ∈ d.support, N < (m : ℕ) := by
  by_cases h : ∀ m ∈ d.support, (m : ℕ) ≤ N
  · exact Or.inl ⟨_, (Finsupp.mapDomain_comapDomain _ modeEmb_injective d fun m hm =>
      (mem_range_modeEmb m).2 (h m hm)).symm⟩
  · push Not at h
    exact Or.inr h

/-- The coefficients of the restricted series. -/
theorem coeff_subst_eS_map {s : Fin N → Modes N} (hs : Function.Injective s)
    (G : MvPowerSeries ℕ+ S) (g : Fin N →₀ ℕ) :
    coeff (Finsupp.mapDomain s g) (subst (eS (S := S) s) G) =
      coeff (Finsupp.mapDomain (modeEmb N) g) G := by
  classical
  have h1 : ∀ d : ℕ+ →₀ ℕ, d ≠ Finsupp.mapDomain (modeEmb N) g →
      coeff d G • coeff (Finsupp.mapDomain s g) (d.prod fun m e => eS (S := S) s m ^ e) = 0 := by
    intro d hd
    rcases exists_map_or (N := N) d with ⟨g', rfl⟩ | ⟨m, hm, h⟩
    · rw [prod_eS_map hs, coeff_monomial_ne, smul_zero]
      intro e
      exact hd (by rw [Finsupp.mapDomain_injective hs e])
    · rw [prod_eS_eq_zero s d m hm h, map_zero, smul_zero]
  rw [coeff_subst (hasSubst_eS s), finsum_eq_single _ _ h1, prod_eS_map hs, coeff_monomial_same,
    smul_eq_mul, mul_one]

theorem coeff_subst_eS_of_not {s : Fin N → Modes N} (hs : Function.Injective s)
    (G : MvPowerSeries ℕ+ S) (γ : Modes N →₀ ℕ)
    (hγ : γ ∉ Set.range (Finsupp.mapDomain s : (Fin N →₀ ℕ) → _)) :
    coeff γ (subst (eS (S := S) s) G) = 0 := by
  classical
  rw [coeff_subst (hasSubst_eS s)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  rcases exists_map_or (N := N) d with ⟨g', rfl⟩ | ⟨m, hm, h⟩
  · rw [prod_eS_map hs, coeff_monomial_ne, smul_zero]
    rintro rfl
    exact hγ ⟨g', rfl⟩
  · rw [prod_eS_eq_zero s d m hm h, map_zero, smul_zero]

/-- The exponent `u^f ū^g`. -/
noncomputable def joinE (f g : Fin N →₀ ℕ) : Modes N →₀ ℕ :=
  Finsupp.mapDomain Sum.inl f + Finsupp.mapDomain Sum.inr g

theorem joinE_inl (f g : Fin N →₀ ℕ) (i : Fin N) : joinE f g (Sum.inl i) = f i := by
  rw [joinE, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective,
    Finsupp.mapDomain_of_notMem_range _ _ (by simp), add_zero]

theorem joinE_inr (f g : Fin N →₀ ℕ) (i : Fin N) : joinE f g (Sum.inr i) = g i := by
  rw [joinE, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inr_injective,
    Finsupp.mapDomain_of_notMem_range _ _ (by simp), zero_add]

theorem joinE_injective {f g f' g' : Fin N →₀ ℕ} (h : joinE f g = joinE f' g') :
    f = f' ∧ g = g' := by
  refine ⟨Finsupp.ext fun i => ?_, Finsupp.ext fun i => ?_⟩
  · have := DFunLike.congr_fun h (Sum.inl i)
    rwa [joinE_inl, joinE_inl] at this
  · have := DFunLike.congr_fun h (Sum.inr i)
    rwa [joinE_inr, joinE_inr] at this

theorem eq_joinE (γ : Modes N →₀ ℕ) :
    γ = joinE (Finsupp.comapDomain Sum.inl γ Sum.inl_injective.injOn)
      (Finsupp.comapDomain Sum.inr γ Sum.inr_injective.injOn) := by
  ext x
  rcases x with i | i
  · rw [joinE_inl, Finsupp.comapDomain_apply]
  · rw [joinE_inr, Finsupp.comapDomain_apply]

theorem mapDomain_inl_eq (f : Fin N →₀ ℕ) : Finsupp.mapDomain Sum.inl f = joinE f 0 := by
  rw [joinE, Finsupp.mapDomain_zero, add_zero]

theorem mapDomain_inr_eq (g : Fin N →₀ ℕ) : Finsupp.mapDomain Sum.inr g = joinE 0 g := by
  rw [joinE, Finsupp.mapDomain_zero, zero_add]

/-- The coefficient of `u^f ū^g` in the product of a series in the `u_m` and a series in the
`ū_m`. -/
theorem coeff_subst_mul (G1 G2 : MvPowerSeries ℕ+ S) (f g : Fin N →₀ ℕ) :
    coeff (joinE f g) (subst (eS (S := S) Sum.inl) G1 * subst (eS (S := S) Sum.inr) G2) =
      coeff (Finsupp.mapDomain (modeEmb N) f) G1 * coeff (Finsupp.mapDomain (modeEmb N) g) G2 := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (Finsupp.mapDomain Sum.inl f, Finsupp.mapDomain Sum.inr g)]
  · rw [coeff_subst_eS_map Sum.inl_injective, coeff_subst_eS_map Sum.inr_injective]
  · rintro ⟨p, q⟩ hpq hne
    rw [Finset.mem_antidiagonal] at hpq
    by_cases hp : p ∈ Set.range (Finsupp.mapDomain Sum.inl : (Fin N →₀ ℕ) → _)
    · by_cases hq : q ∈ Set.range (Finsupp.mapDomain Sum.inr : (Fin N →₀ ℕ) → _)
      · obtain ⟨f', rfl⟩ := hp
        obtain ⟨g', rfl⟩ := hq
        obtain ⟨rfl, rfl⟩ := joinE_injective (f := f') (g := g') (f' := f) (g' := g) hpq
        exact absurd rfl hne
      · rw [coeff_subst_eS_of_not Sum.inr_injective G2 q hq, mul_zero]
    · rw [coeff_subst_eS_of_not Sum.inl_injective G1 p hp, zero_mul]
  · intro h
    refine absurd ?_ h
    rw [Finset.mem_antidiagonal, joinE]

end Restrict

section Pair

variable {N K : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R] (z : R)

/-- The Fock pairing of a product of a series in the `u_m` and a series in the `ū_m`
(sphere/paper.tex l.638–640, with (3.1)): the sum over the exponents `g` of
`∏_m g_m!/(2m)^{g_m} z^{|g|}` times the two coefficients of `u^g`. -/
theorem fockP_subst_mul (G1 G2 : MvPowerSeries ℕ+ R) :
    fockP N K z (subst (eS (S := R) Sum.inl) G1 * subst (eS (S := R) Sum.inr) G2) =
      ∑ g ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin N => K),
        algebraMap ℚ R (nrmF (⇑g)) * z ^ wtF (⇑g) *
          (coeff (Finsupp.mapDomain (modeEmb N) g) G1 *
            coeff (Finsupp.mapDomain (modeEmb N) g) G2) := by
  classical
  have hinj : Function.Injective fun g : Fin N →₀ ℕ => joinE g g := fun g g' h =>
    (joinE_injective h).1
  have hsub : (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin N => K)).image
      (fun g : Fin N →₀ ℕ => joinE g g) ⊆
      Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Modes N => K) := by
    intro γ hγ
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hγ
    rw [Finset.mem_Iic, Finsupp.le_def] at hg ⊢
    intro x
    rcases x with i | i
    · rw [joinE_inl]
      exact hg i
    · rw [joinE_inr]
      exact hg i
  have h0 : ∀ Φ : MvPowerSeries (Modes N) R, fockP N K z Φ =
      ∑ γ ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Modes N => K),
        fockMom N z γ * coeff γ Φ := fun Φ => by
    rw [fockP, LinearMap.sum_apply]
    rfl
  have h1 : ∀ g : Fin N →₀ ℕ, fockMom N z (joinE g g) =
      algebraMap ℚ R (nrmF (⇑g)) * z ^ wtF (⇑g) := fun g => by
    have e1 : (fun i => joinE g g (Sum.inl i)) = ⇑g := funext fun i => joinE_inl g g i
    have e2 : (fun i => joinE g g (Sum.inr i)) = ⇑g := funext fun i => joinE_inr g g i
    rw [fockMom, e1, e2, momF, if_pos rfl]
  have h2 : ∀ γ ∈ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Modes N => K),
      γ ∉ (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : Fin N => K)).image
        (fun g : Fin N →₀ ℕ => joinE g g) → fockMom N z γ = 0 := by
    intro γ hγ hn
    rw [fockMom, momF, if_neg]
    intro he
    apply hn
    refine Finset.mem_image.2 ⟨Finsupp.comapDomain Sum.inl γ Sum.inl_injective.injOn, ?_, ?_⟩
    · rw [Finset.mem_Iic, Finsupp.le_def] at hγ ⊢
      intro i
      exact hγ (Sum.inl i)
    · have e3 : Finsupp.comapDomain Sum.inr γ Sum.inr_injective.injOn =
          Finsupp.comapDomain Sum.inl γ Sum.inl_injective.injOn :=
        Finsupp.ext fun i => (congrFun he i).symm
      conv_rhs => rw [eq_joinE γ, e3]
  rw [h0, ← Finset.sum_subset hsub fun γ hγ hn => by rw [h2 γ hγ hn, zero_mul],
    Finset.sum_image fun _ _ _ _ h => hinj h]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [h1, coeff_subst_mul]

end Pair

end Virasoro.Sphere
