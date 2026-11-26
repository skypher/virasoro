import Virasoro.Proofs.Sec7Expansion
import Virasoro.Proofs.Sec4PF

/-!
# Lemma 7.13 and Theorem 7.14 (the recursion at the fixed charge)

Lemma 7.13 is proved as in the paper: induction on the level; for `j = 0` the chain function is
the full moment minus the shorter-chain terms and the truncation error of Lemma 7.12, all regular;
for `j ≥ 1` the cutting identity (Lemma 7.10) and induction on `j`.  Theorem 7.14 evaluates the
truncated chain expansion at `t = 0`.
-/

namespace Virasoro

open scoped LaurentSeries

section General

variable {K : Type} [Field K] [CharZero K]

/-- A germ `x` with `(n : K⸨t⸩) x = y`, `n ≠ 0` and `y` regular is regular. -/
theorem ordGE_of_natCast_mul {n : ℕ} (hn : n ≠ 0) {x y : K⸨X⸩} (h : (n : K⸨X⸩) * x = y)
    (hy : OrdGE y 0) : OrdGE x 0 := by
  have hn' : (n : K⸨X⸩) ≠ 0 := natCast_laurent_ne_zero hn
  have hx : x = y * HahnSeries.C ((n : K)⁻¹) := by
    rw [map_inv₀, map_natCast, ← h]
    field_simp
  rw [hx]
  have := hy.mul (ordGE_C ((n : K)⁻¹))
  simpa using this

/-- Lemma 7.13 over an arbitrary coefficient field. -/
theorem chainFn_regular {bs : K} (hbs : bs ≠ 0) (d : K)
    (hrec : ∀ M, 1 ≤ M →
      GenericRecursionAt (RatFunc K)⸨X⸩ (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (mapL (algebraMap K (RatFunc K)) (HahnSeries.C d)) M) :
    ∀ D : ℕ, 1 ≤ D → ∀ (lam : K) (k j : ℕ), 1 ≤ k → OrdGE (chainFn bs d lam D k j) 0 := by
  classical
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro hD lam k j
  induction j generalizing k with
  | zero =>
    intro hk
    by_cases hL : (labelsAt bs D lam).Nonempty
    · obtain ⟨a, ha⟩ := hL
      obtain ⟨hal, haw⟩ := (mem_labelsAt bs).1 ha
      have hlam : lam ∈ Lam D bs := by
        rw [← haw]
        exact Finset.mem_image_of_mem _ hal
      obtain ⟨c, hc⟩ := moment_expansion bs d hbs hD lam k
      set J : ℕ := (-c).toNat with hJdef
      have hJ : (0 : ℤ) ≤ (J : ℤ) + c := by omega
      have hC : OrdGE (fullMoment bs d D lam k) 0 := ordGE_iff.2 fun m hm =>
        moment_coeff_neg hbs d hD (fun M h1 _ => hrec M h1) hlam hk hm
      set S : K⸨X⸩ := ∑ n ∈ Finset.Ioo 0 D, ∑ j ∈ Finset.range J,
        chainFn bs d lam n k j * phiRem bs d (D - n) (lam + (n : K)) j with hSdef
      have hS : OrdGE S 0 := by
        refine OrdGE.sum fun n hn => OrdGE.sum fun j _ => ?_
        have hn' := Finset.mem_Ioo.1 hn
        have h1 := ih n hn'.2 hn'.1 lam k j hk
        have h2 := (phiRem_regular hbs d (M := D - n) (by omega) (fun M' h1 _ => hrec M' h1)
          (lam + (n : K)) j).1
        simpa using h1.mul h2
      have hE := (hc J).mono hJ
      have hid : chainFn bs d lam D k 0 =
          fullMoment bs d D lam k - S - (fullMoment bs d D lam k - (chainFn bs d lam D k 0 + S)) := by
        ring
      rw [hid]
      exact (hC.sub hS).sub hE
    · rw [Finset.not_nonempty_iff_eq_empty] at hL
      have h0 : chainFn bs d lam D k 0 = 0 := by
        unfold chainFn
        rw [hL, Finset.sum_empty]
      rw [h0]
      exact OrdGE.zero (K := K) _
  | succ j ihj =>
    intro hk
    have hcut := chainFn_cut bs d (linkNe_germ bs) lam hD hk (Nat.succ_pos j)
    simp only [Nat.succ_sub_one, Nat.succ_eq_add_one] at hcut
    have hR : OrdGE (chainFn bs d lam D (k + 1) j -
        ∑ n ∈ Finset.Ioo 0 D, chainFn bs d lam n k 0 *
          chainFn bs d (lam + (n : K)) (D - n) 1 j) 0 := by
      refine (ihj (k + 1) (by omega)).sub (OrdGE.sum fun n hn => ?_)
      have hn' := Finset.mem_Ioo.1 hn
      have h1 := ih n hn'.2 hn'.1 lam k 0 hk
      have h2 := ih (D - n) (by omega) (by omega) (lam + (n : K)) 1 j le_rfl
      simpa using h1.mul h2
    exact ordGE_of_natCast_mul (Nat.succ_ne_zero j) hcut hR

end General

/-- Lemma 7.13 from the generic recursion in its uniform form. -/
theorem lem_chain_regular_of (hrec : GenericRecursionUniform) : Stmt_lem_chain_regular := by
  intro b hb lam D k j hD hk
  have hbs : bsC b ≠ 0 := by simpa [bsC] using hb
  have h : OrdGE (chainFnC b lam D k j) 0 :=
    chainFn_regular hbs dvar (fun M h1 => germ_recursion hrec (bsC b) dvar M h1) D hD (pt lam)
      k j hk
  simpa [OrdGE] using h

/-- Lemma 7.13, from the two cited results (through Proposition 6.4).

Paper label: lem:chain-regular -/
theorem lem_chain_regular_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_lem_chain_regular :=
  lem_chain_regular_of (genericRecursionUniform hK hH)

/-- Theorem 7.14 from the generic recursion in its uniform form. -/
theorem thm_fixed_charge_of (hrec : GenericRecursionUniform) : Stmt_thm_fixed_charge := by
  intro b hb N hN
  have hbs : bsC b ≠ 0 := by simpa [bsC] using hb
  have hrecK := fun (M : ℕ) (h1 : 1 ≤ M) => germ_recursion hrec (bsC b) dvar M h1
  have hreg : ∀ (lam : ℂ) (D k j : ℕ), 1 ≤ D → 1 ≤ k → OrdGE (chainFnC b lam D k j) 0 :=
    fun lam D k j hD hk => chainFn_regular hbs dvar hrecK D hD (pt lam) k j hk
  have hpf := thm_general_partial_fractions_of_recursion hrec
  refine ⟨fun lam hlam k hk => ?_, ((hpf b hb).2.1 N hN).2.2.1,
    fun lam D k j hD hk => by simpa [OrdGE] using hreg lam D k j hD hk⟩
  refine ⟨fun n _ => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := chainFn_ord (bsC b) dvar hbs (pt lam) n k
    refine ⟨(1 - c).toNat, fun j hj => ?_⟩
    exact (hc j).coeff_eq_zero (by omega)
  obtain ⟨c, hc⟩ := moment_expansion (bsC b) dvar hbs hN (pt lam) k
  refine ⟨(1 - c).toNat, fun J hJ => ?_⟩
  have hlt : (0 : ℤ) < (J : ℤ) + c := by omega
  have h0 := (hc J).coeff_eq_zero hlt
  rw [HahnSeries.coeff_sub, sub_eq_zero] at h0
  have hA : (fullMoment (bsC b) dvar N (pt lam) k).coeff 0 = Astar b N lam k :=
    (((lem_full_moments_of hrec) b hb).2 N hN lam hlam k hk).2
  rw [← hA, h0, HahnSeries.coeff_add, HahnSeries.coeff_sum]
  unfold fixedChargeRHS
  refine congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun n hn => ?_)
  rw [HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hn' := Finset.mem_Ioo.1 hn
  have h1 : RegVal (chainFn (bsC b) dvar (pt lam) n k j) ((chainFnC b lam n k j).coeff 0) :=
    ⟨hreg lam n k j hn'.1 hk, rfl⟩
  have h2 := phiRem_regular hbs dvar (M := N - n) (by omega) (fun M' h1 _ => hrecK M' h1)
    (pt lam + (n : Kd)) j
  have h2' : RegVal (phiRem (bsC b) dvar (N - n) (pt lam + (n : Kd)) j)
      ((j.factorial : Kd) * lcoeff (HN (kacC b) (N - n)) (pt (lam + n)) j) := by
    refine ⟨h2.1, ?_⟩
    rw [h2.2, pt_add_natCast, HN, bsC, kacC_ratC]
  exact (h1.mul h2').2

/-- Theorem 7.14, from the two cited results (through Proposition 6.4).

Paper label: thm:fixed-charge -/
theorem thm_fixed_charge_of_cited (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_thm_fixed_charge :=
  thm_fixed_charge_of (genericRecursionUniform hK hH)

end Virasoro
