import Virasoro.Sphere.Statements.Rev20261125
import Virasoro.Sphere.Proofs.Rev20261124
import Virasoro.Sphere.Proofs.Sec4PolyPart

/-!
# Proof of the sphere confluence theorem in the form of 2026-11-25

It follows from the 70bac53 form (`Stmt_thm_confluence`) and the vanishing of the collision
moments beyond the a priori bound (`Atildeg_eq_zero`).
-/

namespace Virasoro.Sphere

open Polynomial

theorem Atildeg_sph_eq_zero {b : ℂ} (hb : b ≠ 0) (N : ℕ) (lam : ℂ) {k : ℕ}
    (hk : Mhatg (cK b) (RgSph b) N (cK lam) < k) : Atildeg (cK b) (RgSph b) N (cK lam) k = 0 := by
  have hbs : cK b ≠ 0 := (map_ne_zero (algebraMap ℂ K4)).2 hb
  exact Atildeg_eq_zero ΔK hbs N (cK lam) hk

/-- The sphere confluence theorem in its current form, from the 70bac53 form. -/
theorem thm_confluence_rev25_of (h : Stmt_thm_confluence) : Stmt_thm_confluence_rev25 := by
  classical
  intro b hb N hN
  obtain ⟨hA, hH, hB⟩ := h b hb N hN
  refine ⟨fun lam hlam k hk1 => ?_, ⟨(Lam N b).sup (fun lam => Mhatg (cK b) (RgSph b) N (cK lam)),
    fun lam hlam k hk => ?_, ?_⟩, hB⟩
  · by_cases hk2 : k ≤ Mhatg (cK b) (RgSph b) N (cK lam)
    · exact hA lam hlam k hk1 hk2
    · refine ⟨0, fun m => by simp [zero_mem], ?_⟩
      rw [Atildeg_sph_eq_zero hb N lam (by omega), map_zero]
  · exact Atildeg_sph_eq_zero hb N lam
      (lt_of_le_of_lt (Finset.le_sup (f := fun lam => Mhatg (cK b) (RgSph b) N (cK lam)) hlam) hk)
  · rw [hH]
    refine Finset.sum_congr rfl fun lam hlam => ?_
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, le_trans hk.2
        (Finset.le_sup (f := fun lam => Mhatg (cK b) (RgSph b) N (cK lam)) hlam)⟩
    · intro k hkK hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hkK).1
      simp only [Finset.mem_Icc, not_and, not_le] at hk
      rw [Atildeg_sph_eq_zero hb N lam (hk hk1), map_zero, zero_div]

/-- The sphere confluence theorem, from the cited results.

Paper label: thm:confluence -/
theorem thm_confluence_rev25_of_cited (hF : Cited_FeiginFuchsOperators)
    (hK : Cited_KacDeterminant) (hJ1 : Cited_JacobiIdentities) (hJ2 : Cited_JacobiIdentities2)
    (hH : Cited_HJSNormalizations) (hFus : Cited_SphereFusionPolynomial) :
    Stmt_thm_confluence_rev25 :=
  thm_confluence_rev25_of (thm_confluence_of_cited hF hK hJ1 hJ2 hH hFus)

end Virasoro.Sphere
