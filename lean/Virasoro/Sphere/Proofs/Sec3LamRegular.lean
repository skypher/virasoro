import Virasoro.Sphere.Proofs.Sec3LamInfty
import Virasoro.Sphere.Proofs.Sec3LamSubs
import Virasoro.Sphere.Proofs.Sec3FockLevel

/-!
# Regularity at `λ = ∞` (sphere paper Lemma 3.3(i))

sphere/paper.tex l.569–600.  At oscillator level `m - k` equation (3.3) isolates `S_m` as
`D_k(λ)S_m = R_{m,k}(S_1,…,S_{m-1};λ)`, and `𝒟_m(∞) = (i∂_k + ∑ nσ_n∂_{n+k})_k` is injective by
the lowest-degree argument.  In terms of the order in `t = 1/λ`: if the coefficients of `S_m`
have order `≥ -(n+1)`, then, by induction on the polynomial degree, the coefficient of `σ^β` in
equation (3.3) for `k` gives order `≥ -n` for the coefficient of `σ^β σ_k`: the term
`∑ nσ_n∂_{n+k}` involves lower degree, the term with `t²` gains two orders, and the remaining
terms involve lower levels.
-/

namespace Virasoro.Sphere

open scoped LaurentSeries

open Finset

local notation "KK" => RatFunc ℂ
local notation "LL" => ℂ⸨X⸩

theorem lvl_eq_zero {α : ℕ+ →₀ ℕ} (h : lvl α = 0) : α = 0 := by
  by_contra hne
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  have e := congrArg lvl (sub_add_single hj)
  rw [lvl_add, lvl_single] at e
  have := j.pos
  omega

/-- There are finitely many monomials of a given oscillator level. -/
theorem finite_level (m : ℕ) : {α : ℕ+ →₀ ℕ | lvl α = m}.Finite := by
  have hinj : Function.Injective
      (fun α : {α : ℕ+ →₀ ℕ // lvl α = m} => partOfExp α.1 α.2) := by
    intro a b hab
    have h1 := partMono_partOfExp a.1 a.2
    have h2 := partMono_partOfExp b.1 b.2
    have hab' : partOfExp a.1 a.2 = partOfExp b.1 b.2 := hab
    rw [hab', h2] at h1
    exact Subtype.ext (MvPolynomial.monomial_left_injective (one_ne_zero (α := ℂ)) h1.symm)
  haveI : Finite ↑{α : ℕ+ →₀ ℕ | lvl α = m} := Finite.of_injective _ hinj
  exact Set.toFinite _

theorem ordGE_natCast (n : ℕ) : OrdGE ((n : LL)) 0 := (regVal_natCast n).1

theorem ordGE_natCast_succ (n : ℕ) : OrdGE ((n : LL) + 1) 0 := (ordGE_natCast n).add ordGE_one

/-- Regularity of the solution of (3.3): if the coefficients `a_k` have value `i` at `t = 0`,
`b_k = O(t²)`, and `q_k, c_k` are regular, then every coefficient of a solution with zero
constant term is regular. -/
theorem regular_of_pde (S : MvPowerSeries ℕ+ LL) (a q b c : ℕ → LL)
    (ha : ∀ k, RegVal (a k) Complex.I) (hq : ∀ k, OrdGE (q k) 0) (hb : ∀ k, OrdGE (b k) 2)
    (hc : ∀ k, OrdGE (c k) 0) (h0 : MvPowerSeries.coeff 0 S = 0)
    (h : ∀ k, 1 ≤ k → pdeLam k (a k) (q k) (b k) (c k) S = 0) :
    ∀ α, OrdGE (MvPowerSeries.coeff α S) 0 := by
  classical
  have key : ∀ m : ℕ, ∀ α, lvl α = m → OrdGE (MvPowerSeries.coeff α S) 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      rcases m.eq_zero_or_pos with rfl | hm
      · intro α hα
        rw [lvl_eq_zero hα, h0]
        exact OrdGE.zero 0
      have step : ∀ n : ℕ,
          (∀ α, lvl α = m → OrdGE (MvPowerSeries.coeff α S) (-((n : ℤ) + 1))) →
          ∀ d : ℕ, ∀ α, lvl α = m → α.degree = d →
            OrdGE (MvPowerSeries.coeff α S) (-(n : ℤ)) := by
        intro n hn d
        induction d using Nat.strong_induction_on with
        | _ d ihd =>
          intro α hα hd
          have hα0 : α ≠ 0 := by
            rintro rfl
            simp [lvl] at hα
            omega
          obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.2 hα0
          have hαβ := sub_add_single hk
          have hlvl : lvl (α - Finsupp.single k 1) + (k : ℕ) = m := by
            rw [← hα, ← lvl_single k, ← lvl_add, hαβ]
          have hdeg : (α - Finsupp.single k 1).degree + 1 = d := by
            have e := congrArg Finsupp.degree hαβ
            rw [map_add, Finsupp.degree_single] at e
            rw [e, hd]
          generalize α - Finsupp.single k 1 = β at hαβ hlvl hdeg
          have hk1 : 1 ≤ (k : ℕ) := k.pos
          have hE := congrArg (MvPowerSeries.coeff β) (h (k : ℕ) hk1)
          rw [pdeLam] at hE
          simp only [map_sub, map_add, map_zero] at hE
          have e1 : MvPowerSeries.coeff β (a (k : ℕ) • pdA (k : ℕ) S) =
              a (k : ℕ) * (MvPowerSeries.coeff α S * ((β k : LL) + 1)) := by
            rw [MvPowerSeries.coeff_smul, coeff_pdA, PNat.coe_toPNat', hαβ]
          have h2 : OrdGE (MvPowerSeries.coeff β (shiftA (k : ℕ) S)) (-(n : ℤ)) := by
            rw [coeff_shiftA]
            refine OrdGE.sum fun j hj => ?_
            have hj' : ((((j : ℕ) + (k : ℕ)).toPNat' : ℕ+) : ℕ) = (j : ℕ) + (k : ℕ) :=
              PNat.toPNat'_coe (by omega)
            have hβj := sub_add_single hj
            have l1 : lvl (β - Finsupp.single j 1 +
                Finsupp.single ((j : ℕ) + (k : ℕ)).toPNat' 1) = m := by
              have e := congrArg lvl hβj
              rw [lvl_add, lvl_single] at e
              rw [lvl_add, lvl_single, hj']
              omega
            have d1 : (β - Finsupp.single j 1 +
                Finsupp.single ((j : ℕ) + (k : ℕ)).toPNat' 1).degree = d - 1 := by
              have e := congrArg Finsupp.degree hβj
              rw [map_add, Finsupp.degree_single] at e
              rw [map_add, Finsupp.degree_single]
              omega
            rw [coeff_pdA]
            exact ((ordGE_natCast _).mul ((ihd (d - 1) (by omega) _ l1 d1).mul
              (ordGE_natCast_succ _))).mono (by omega)
          have h3 : OrdGE (MvPowerSeries.coeff β (levelA S)) (-(n : ℤ)) := by
            rw [coeff_levelA]
            exact ((ordGE_natCast _).mul (ihm (lvl β) (by omega) β rfl)).mono (by omega)
          have h4 : OrdGE (MvPowerSeries.coeff β (q (k : ℕ) •
              ∑ n' ∈ Icc 1 ((k : ℕ) - 1), pdA n' S * pdA ((k : ℕ) - n') S)) (-(n : ℤ)) := by
            rw [MvPowerSeries.coeff_smul, map_sum]
            refine ((hq _).mul (OrdGE.sum (n := 0) fun n' hn' => ?_)).mono (by omega)
            have hn'' := Finset.mem_Icc.1 hn'
            rw [MvPowerSeries.coeff_mul]
            refine OrdGE.sum fun p hp => ?_
            have hpβ : p.1 + p.2 = β := by simpa using hp
            have e := congrArg lvl hpβ
            rw [lvl_add] at e
            have hj1 : ((n'.toPNat' : ℕ+) : ℕ) = n' := PNat.toPNat'_coe hn''.1
            have hj2 : (((((k : ℕ) - n').toPNat' : ℕ+)) : ℕ) = (k : ℕ) - n' :=
              PNat.toPNat'_coe (by omega)
            have l1 : lvl (p.1 + Finsupp.single n'.toPNat' 1) < m := by
              rw [lvl_add, lvl_single, hj1]
              omega
            have l2 : lvl (p.2 + Finsupp.single ((k : ℕ) - n').toPNat' 1) < m := by
              rw [lvl_add, lvl_single, hj2]
              omega
            rw [coeff_pdA, coeff_pdA]
            exact (((ihm _ l1 _ rfl).mul (ordGE_natCast_succ _)).mul
              ((ihm _ l2 _ rfl).mul (ordGE_natCast_succ _))).mono (by omega)
          have h5 : OrdGE (MvPowerSeries.coeff β (b (k : ℕ) •
              ∑ n' ∈ Icc 1 ((k : ℕ) - 1), pdA n' (pdA ((k : ℕ) - n') S))) (-(n : ℤ)) := by
            rw [MvPowerSeries.coeff_smul, map_sum]
            refine ((hb _).mul (OrdGE.sum (n := -((n : ℤ) + 1)) fun n' hn' => ?_)).mono
              (by omega)
            have hn'' := Finset.mem_Icc.1 hn'
            have hj1 : ((n'.toPNat' : ℕ+) : ℕ) = n' := PNat.toPNat'_coe hn''.1
            have hj2 : (((((k : ℕ) - n').toPNat' : ℕ+)) : ℕ) = (k : ℕ) - n' :=
              PNat.toPNat'_coe (by omega)
            have l1 : lvl (β + Finsupp.single n'.toPNat' 1 +
                Finsupp.single ((k : ℕ) - n').toPNat' 1) = m := by
              rw [lvl_add, lvl_add, lvl_single, lvl_single, hj1, hj2]
              omega
            rw [coeff_pdA, coeff_pdA]
            exact (((hn _ l1).mul (ordGE_natCast_succ _)).mul (ordGE_natCast_succ _)).mono
              (by omega)
          have h6 : OrdGE (MvPowerSeries.coeff β (MvPowerSeries.C (c (k : ℕ)) :
              MvPowerSeries ℕ+ LL)) (-(n : ℤ)) := by
            rw [MvPowerSeries.coeff_C]
            split_ifs
            · exact (hc _).mono (by omega)
            · exact OrdGE.zero _
          have hx : a (k : ℕ) * (MvPowerSeries.coeff α S * ((β k : LL) + 1)) =
              -(MvPowerSeries.coeff β (shiftA (k : ℕ) S)) + MvPowerSeries.coeff β (levelA S) +
              MvPowerSeries.coeff β (q (k : ℕ) •
                ∑ n' ∈ Icc 1 ((k : ℕ) - 1), pdA n' S * pdA ((k : ℕ) - n') S) +
              MvPowerSeries.coeff β (b (k : ℕ) •
                ∑ n' ∈ Icc 1 ((k : ℕ) - 1), pdA n' (pdA ((k : ℕ) - n') S)) +
              MvPowerSeries.coeff β (MvPowerSeries.C (c (k : ℕ)) : MvPowerSeries ℕ+ LL) := by
            rw [← e1]
            linear_combination hE
          have hX : OrdGE (a (k : ℕ) * (MvPowerSeries.coeff α S * ((β k : LL) + 1)))
              (-(n : ℤ)) := by
            rw [hx]
            exact (((h2.neg.add h3).add h4).add h5).add h6
          have ha0 : a (k : ℕ) ≠ 0 := fun h0' => by
            have := (ha (k : ℕ)).2
            rw [h0'] at this
            exact Complex.I_ne_zero (by simpa using this.symm)
          have hc1 : RegVal (((β k + 1 : ℕ) : LL)) ((β k + 1 : ℕ) : ℂ) := regVal_natCast _
          have hc0 : ((β k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero (β k))
          have hc10 : ((β k : LL) + 1) ≠ 0 := fun h0' => by
            have := hc1.2
            rw [Nat.cast_add, Nat.cast_one, h0'] at this
            exact hc0 (by simpa using this.symm)
          have hinv1 : OrdGE (a (k : ℕ))⁻¹ 0 := ((ha (k : ℕ)).inv Complex.I_ne_zero).1
          have hinv2 : OrdGE ((β k : LL) + 1)⁻¹ 0 := by
            have := (hc1.inv hc0).1
            rwa [Nat.cast_add, Nat.cast_one] at this
          have hfin : MvPowerSeries.coeff α S = (a (k : ℕ))⁻¹ * (((β k : LL) + 1)⁻¹ *
              (a (k : ℕ) * (MvPowerSeries.coeff α S * ((β k : LL) + 1)))) := by
            field_simp
          have hres := (hinv1.mul (hinv2.mul hX)).mono (m := -(n : ℤ)) (by omega)
          rwa [← hfin] at hres
      have desc : ∀ n : ℕ, (∀ α, lvl α = m → OrdGE (MvPowerSeries.coeff α S) (-(n : ℤ))) →
          ∀ α, lvl α = m → OrdGE (MvPowerSeries.coeff α S) 0 := by
        intro n
        induction n with
        | zero =>
          intro h' α hα
          simpa using h' α hα
        | succ n ih =>
          intro h'
          exact ih fun α hα => step n (fun α hα => (h' α hα).mono (by push_cast; omega))
            α.degree α hα rfl
      let s := (finite_level m).toFinset
      refine desc (s.sup fun α => (-(MvPowerSeries.coeff α S).order).toNat) fun α hα => ?_
      have hmem : α ∈ s := (Set.Finite.mem_toFinset _).2 hα
      have hle := Finset.le_sup (f := fun α => (-(MvPowerSeries.coeff α S).order).toNat) hmem
      have h1 := Int.self_le_toNat (-(MvPowerSeries.coeff α S).order)
      exact (ordGE_order _).mono (by
        have h2 : ((-(MvPowerSeries.coeff α S).order).toNat : ℤ) ≤
            ((s.sup fun α => (-(MvPowerSeries.coeff α S).order).toNat : ℕ) : ℤ) := by
          exact_mod_cast hle
        omega)
  intro α
  exact key (lvl α) α rfl

theorem coeff_zero_SL (F : ℕ → MvPolynomial ℕ+ KK)
    (h1 : MvPowerSeries.constantCoeff (wardSeries F) = 1) :
    MvPowerSeries.coeff 0 (SL F) = 0 := by
  have hg : MvPowerSeries.constantCoeff (wardSeries F - 1) = 0 := by
    rw [map_sub, h1, map_one, sub_self]
  have hz : MvPowerSeries.coeff 0 ((PowerSeries.log KK).subst (wardSeries F - 1)) = 0 := by
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.constantCoeff_subst_eq_zero hg _ PowerSeries.constantCoeff_log
  rw [SL, MvPowerSeries.coeff_map, Slam_eq_rho, coeff_rho, hz, mul_zero, map_zero]

/-- The coefficients of `S(σ;λ)` in the variable `t = 1/λ` have no negative powers. -/
theorem SL_regular {μ Δ1 Δ2 : ℂ} {F : ℕ → MvPolynomial ℕ+ KK}
    (h : IsWardSeries (RatFunc.C μ) (RatFunc.X : KK) (RatFunc.C Δ1) (RatFunc.C Δ2) F)
    (α : ℕ+ →₀ ℕ) : OrdGE (MvPowerSeries.coeff α (SL F)) 0 := by
  refine regular_of_pde (SL F)
    (fun k => HahnSeries.C Complex.I + HahnSeries.C (μ * (k : ℂ)) * tL)
    (fun _ => HahnSeries.C (1 / 4 : ℂ)) (fun _ => HahnSeries.C (1 / 4 : ℂ) * tL ^ 2)
    (fun k => 1 + HahnSeries.C (μ ^ 2 + ((k : ℂ) * Δ2 - Δ1)) * tL ^ 2)
    (fun k => ?_) (fun _ => ordGE_C _) (fun _ => ?_) (fun k => ?_)
    (coeff_zero_SL F (constantCoeff_wardSeries h)) (fun k hk => SL_pde h k hk) α
  · have := (regVal_C Complex.I).add ((regVal_C (μ * (k : ℂ))).mul regVal_tL)
    simpa using this
  · exact ((ordGE_C _).mul (ordGE_tL.pow 2)).mono (by norm_num)
  · exact ordGE_one.add (((ordGE_C _).mul (ordGE_tL.pow 2)).mono (by norm_num))

/-- Step (i-b) of Lemma 3.3: regularity at `λ = ∞`. -/
theorem sub_lam_regular : Stmt_sub_lam_regular := by
  intro μ _ Δ1 Δ2 F h α
  rw [regularAtInfty_iff]
  have := SL_regular h α
  rwa [SL, MvPowerSeries.coeff_map] at this

end Virasoro.Sphere
