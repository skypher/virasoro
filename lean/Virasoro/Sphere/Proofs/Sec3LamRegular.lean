import Virasoro.Sphere.Proofs.Sec3LamInfty
import Virasoro.Sphere.Proofs.Sec3LamSubs
import Virasoro.Sphere.Proofs.Sec3FockLevel
import Virasoro.Sphere.Proofs.Sec3LamLevelSys

/-!
# Regularity at `λ = ∞` (sphere paper Lemma 3.3(i))

Proof of Lemma 3.3(i).  At oscillator level `m - k` equation (3.3) isolates `S_m` as
`D_k(λ)S_m = R_{m,k}(S_1,…,S_{m-1};λ)`; `𝒟_m(∞) = (i∂_k + ∑ nσ_n∂_{n+k})_k` is injective by the
lowest-degree argument, so the rectangular system has an invertible square minor at `λ⁻¹ = 0`,
which gives a left inverse regular in `λ⁻¹` (`Sec3LamMinor.lean`, `Sec3LamLevelSys.lean`).
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
constant term is regular.  By induction on the level `m`: the level-`m` equations form the
rectangular system `𝒟_m(λ)S_m = R_m` with `R_m` regular (`coeff_linLam_level`), whose value at
`λ⁻¹ = 0` is the injective `𝒟_m(∞)` (`Dinf_injective`); an invertible square minor then gives a
left inverse regular in `λ⁻¹` (`regular_of_rect_system`). -/
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
      letI : Fintype {α : ℕ+ →₀ ℕ // lvl α = m} := (finite_level m).fintype
      letI hfib : ∀ k : Fin m, Fintype {β : ℕ+ →₀ ℕ // lvl β + ((k : ℕ) + 1) = m} := fun k =>
        ((finite_level (m - ((k : ℕ) + 1))).subset fun β (hβ : lvl β + ((k : ℕ) + 1) = m) =>
          show lvl β = m - ((k : ℕ) + 1) by omega).fintype
      -- the system: rows `(k, β)` with `lvl β + k = m`, unknowns the level-`m` coefficients
      let M : Matrix (Σ k : Fin m, {β : ℕ+ →₀ ℕ // lvl β + ((k : ℕ) + 1) = m})
          {α : ℕ+ →₀ ℕ // lvl α = m} LL := fun i α =>
        MvPowerSeries.coeff i.2.1 (linLamL ((i.1 : ℕ) + 1) (a ((i.1 : ℕ) + 1))
          (b ((i.1 : ℕ) + 1)) (MvPowerSeries.monomial α.1 1))
      let N : Matrix (Σ k : Fin m, {β : ℕ+ →₀ ℕ // lvl β + ((k : ℕ) + 1) = m})
          {α : ℕ+ →₀ ℕ // lvl α = m} ℂ := fun i α =>
        MvPowerSeries.coeff i.2.1 (linLamL ((i.1 : ℕ) + 1) Complex.I 0
          (MvPowerSeries.monomial α.1 (1 : ℂ)))
      let x : {α : ℕ+ →₀ ℕ // lvl α = m} → LL := fun α => MvPowerSeries.coeff α.1 S
      let r : (Σ k : Fin m, {β : ℕ+ →₀ ℕ // lvl β + ((k : ℕ) + 1) = m}) → LL := fun i =>
        MvPowerSeries.coeff i.2.1 (levelA S) +
          q ((i.1 : ℕ) + 1) * MvPowerSeries.coeff i.2.1
            (∑ n ∈ Icc 1 ((i.1 : ℕ) + 1 - 1), pdA n S * pdA ((i.1 : ℕ) + 1 - n) S) +
          MvPowerSeries.coeff i.2.1 (MvPowerSeries.C (c ((i.1 : ℕ) + 1)) : MvPowerSeries ℕ+ LL)
      have hsys : M.mulVec x = r := by
        funext i
        obtain ⟨k, β, hβ⟩ := i
        have hk1 : 1 ≤ (k : ℕ) + 1 := by omega
        have hE := congrArg (MvPowerSeries.coeff β) (h ((k : ℕ) + 1) hk1)
        have hlin := coeff_linLam_level hk1 (a ((k : ℕ) + 1)) (b ((k : ℕ) + 1)) S β hβ
        rw [pdeLam] at hE
        rw [linLamL_apply] at hlin
        simp only [map_sub, map_add, map_zero, MvPowerSeries.coeff_smul, smul_eq_mul] at hE hlin
        show ∑ α, M ⟨k, β, hβ⟩ α * x α = r ⟨k, β, hβ⟩
        have e : ∑ α, M ⟨k, β, hβ⟩ α * x α = ∑ α : {α : ℕ+ →₀ ℕ // lvl α = m},
            MvPowerSeries.coeff α.1 S * MvPowerSeries.coeff β (linLamL ((k : ℕ) + 1)
              (a ((k : ℕ) + 1)) (b ((k : ℕ) + 1)) (MvPowerSeries.monomial α.1 1)) :=
          sum_congr rfl fun α _ => mul_comm _ _
        rw [e, ← hlin]
        simp only [r]
        linear_combination hE
      have hr : ∀ i, OrdGE (r i) 0 := by
        intro i
        obtain ⟨k, β, hβ⟩ := i
        simp only [r]
        have h3 : OrdGE (MvPowerSeries.coeff β (levelA S)) 0 := by
          rw [coeff_levelA]
          exact ((ordGE_natCast _).mul (ihm (lvl β) (by omega) β rfl)).mono (by omega)
        have h4 : OrdGE (q ((k : ℕ) + 1) * MvPowerSeries.coeff β
            (∑ n ∈ Icc 1 ((k : ℕ) + 1 - 1), pdA n S * pdA ((k : ℕ) + 1 - n) S)) 0 := by
          rw [map_sum]
          refine ((hq _).mul (OrdGE.sum (n := 0) fun n' hn' => ?_)).mono (by omega)
          have hn'' := Finset.mem_Icc.1 hn'
          rw [MvPowerSeries.coeff_mul]
          refine OrdGE.sum fun p hp => ?_
          have hpβ : p.1 + p.2 = β := by simpa using hp
          have e := congrArg lvl hpβ
          rw [lvl_add] at e
          have hj1 : ((n'.toPNat' : ℕ+) : ℕ) = n' := PNat.toPNat'_coe hn''.1
          have hj2 : (((((k : ℕ) + 1 - n').toPNat' : ℕ+)) : ℕ) = (k : ℕ) + 1 - n' :=
            PNat.toPNat'_coe (by omega)
          have l1 : lvl (p.1 + Finsupp.single n'.toPNat' 1) < m := by
            rw [lvl_add, lvl_single, hj1]
            omega
          have l2 : lvl (p.2 + Finsupp.single ((k : ℕ) + 1 - n').toPNat' 1) < m := by
            rw [lvl_add, lvl_single, hj2]
            omega
          rw [coeff_pdA, coeff_pdA]
          exact (((ihm _ l1 _ rfl).mul (ordGE_natCast_succ _)).mul
            ((ihm _ l2 _ rfl).mul (ordGE_natCast_succ _))).mono (by omega)
        have h6 : OrdGE (MvPowerSeries.coeff β (MvPowerSeries.C (c ((k : ℕ) + 1)) :
            MvPowerSeries ℕ+ LL)) 0 := by
          rw [MvPowerSeries.coeff_C]
          split_ifs
          · exact hc _
          · exact OrdGE.zero _
        exact (h3.add h4).add h6
      have hM : ∀ i α, RegVal (M i α) (N i α) := by
        intro i α
        obtain ⟨k, β, hβ⟩ := i
        set P : MvPowerSeries ℕ+ ℂ := MvPowerSeries.monomial α.1 1 with hP
        have hmono : (MvPowerSeries.monomial α.1 (1 : LL)) = MvPowerSeries.map HahnSeries.C P := by
          simp only [hP, MvPowerSeries.map_monomial, map_one]
        set u := MvPowerSeries.coeff β (pdA ((k : ℕ) + 1) P)
        set v := MvPowerSeries.coeff β (shiftA ((k : ℕ) + 1) P)
        set w := MvPowerSeries.coeff β
          (∑ n ∈ Icc 1 ((k : ℕ) + 1 - 1), pdA n (pdA ((k : ℕ) + 1 - n) P))
        have hMv : M ⟨k, β, hβ⟩ α =
            a ((k : ℕ) + 1) * HahnSeries.C u + HahnSeries.C v - b ((k : ℕ) + 1) * HahnSeries.C w := by
          show MvPowerSeries.coeff β (linLamL _ _ _ (MvPowerSeries.monomial α.1 1)) = _
          rw [linLamL_apply, hmono, ← map_pdA, ← map_shiftA]
          simp only [← map_pdA, ← map_sum, map_sub, map_add, MvPowerSeries.coeff_smul,
            MvPowerSeries.coeff_map, smul_eq_mul]
          rfl
        have hNv : N ⟨k, β, hβ⟩ α = Complex.I * u + v := by
          show MvPowerSeries.coeff β (linLamL _ _ _ (MvPowerSeries.monomial α.1 (1 : ℂ))) = _
          rw [linLamL_apply]
          simp only [zero_smul, sub_zero, map_add, MvPowerSeries.coeff_smul, smul_eq_mul]
          rfl
        have hbw : RegVal (b ((k : ℕ) + 1) * HahnSeries.C w) 0 :=
          ⟨((hb _).mul (ordGE_C w)).mono (by norm_num),
            ((hb _).mul (ordGE_C w)).coeff_eq_zero (by norm_num)⟩
        rw [hMv, hNv]
        simpa using (((ha _).mul (regVal_C u)).add (regVal_C v)).sub hbw
      have hN : ∀ v : {α : ℕ+ →₀ ℕ // lvl α = m} → ℂ, N.mulVec v = 0 → v = 0 := by
        intro v hv
        refine Dinf_injective hm v fun k hk β hβ => ?_
        have hkm : k - 1 < m := by omega
        have e := congrFun hv ⟨⟨k - 1, hkm⟩, β, by
          show lvl β + ((k - 1) + 1) = m
          omega⟩
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, N] at e
        rw [show k - 1 + 1 = k by omega] at e
        exact (sum_congr rfl fun α _ => mul_comm _ _).trans e
      have hx := regular_of_rect_system M N hM hN x r hr hsys
      intro α hα
      exact hx ⟨α, hα⟩
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
