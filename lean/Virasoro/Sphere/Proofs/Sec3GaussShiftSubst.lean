import Virasoro.Sphere.Proofs.Sec3GaussQuadPart
import Virasoro.Sphere.Proofs.Sec3GaussShift

/-!
# The shifted variables `z^m u_m = λσ_{*,m} + U_m` (sphere paper Lemma 3.3(iii))

sphere/paper.tex l.663–665 and l.686–691.  A series in `t u` (`t = 1/λ`), restricted to the modes
`≤ n` and translated by `λ a`, is the series in the variables `t x_m + a_m`:
`T(t(x + λa)) = T(a + t x)`.  Also here: such a substituted series is the rescaling by `t` of the
series in `x_m + a_m`, and its constant term does not depend on the variable part.
-/

namespace Virasoro.Sphere

open MvPowerSeries

section ShiftSubst

variable {n : ℕ} {S : Type*} [CommRing S]

/-- The constants `a_{s(m)}` (`m ≤ n`), `0` (`m > n`). -/
noncomputable def cS (s : Fin n → Modes n) (a : Modes n → S) (m : ℕ+) :
    MvPowerSeries (Modes n) S :=
  if h : (m : ℕ) ≤ n then C (a (s ⟨(m : ℕ) - 1, by have := m.pos; omega⟩)) else 0

theorem cS_of_lt (s : Fin n → Modes n) (a : Modes n → S) (m : ℕ+) (h : n < (m : ℕ)) :
    cS s a m = 0 :=
  dif_neg (by omega)

theorem hasSubst_cS (s : Fin n → Modes n) {a : Modes n → S} (ha : ∀ x, IsNilpotent (a x)) :
    HasSubst (cS s a) where
  const_coeff m := by
    rw [cS]
    split_ifs
    · rw [constantCoeff_C]
      exact ha _
    · rw [map_zero]
      exact IsNilpotent.zero
  coeff_zero d := (Set.finite_range (modeEmb n)).subset fun m hm => by
    rw [mem_range_modeEmb]
    by_contra h
    exact hm (by rw [cS, dif_neg h, map_zero])

/-- The substitution `u_m ↦ r x_{s(m)} + a_{s(m)}` (`m ≤ n`), `u_m ↦ 0` (`m > n`). -/
noncomputable def bS (s : Fin n → Modes n) (r : S) (a : Modes n → S) (m : ℕ+) :
    MvPowerSeries (Modes n) S :=
  C r * eS s m + cS s a m

theorem hasSubst_bS (s : Fin n → Modes n) (r : S) {a : Modes n → S}
    (ha : ∀ x, IsNilpotent (a x)) : HasSubst (bS s r a) :=
  ((hasSubst_eS s).mul_left fun _ => C r).add (hasSubst_cS s ha)

theorem bS_of_lt (s : Fin n → Modes n) (r : S) (a : Modes n → S) (m : ℕ+) (h : n < (m : ℕ)) :
    bS s r a m = 0 := by
  rw [bS, eS_of_lt s m h, cS_of_lt s a m h, mul_zero, add_zero]

theorem map_bS {S' : Type*} [CommRing S'] (ψ : S →+* S') (s : Fin n → Modes n) (r : S)
    (a : Modes n → S) (m : ℕ+) :
    map ψ (bS s r a m) = bS s (ψ r) (fun x => ψ (a x)) m := by
  rw [bS, bS, eS, cS, eS, cS]
  split_ifs <;> simp

/-- `T(t(x + λa)) = T(a + t x)` for `t λ = 1` (sphere/paper.tex l.663–665). -/
theorem trans_subst_rescale (s : Fin n → Modes n) {a : Modes n → S}
    (ha : ∀ x, IsNilpotent (a x)) (lam t : S) (htl : t * lam = 1) (G : MvPowerSeries ℕ+ S) :
    trans (fun x => lam * a x) (subst (eS (S := S) s) (rescale (fun _ => t) G)) =
      subst (bS s t a) G := by
  have ha' : ∀ x, IsNilpotent (lam * a x) := fun x => by
    obtain ⟨k, hk⟩ := ha x
    exact ⟨k, by rw [mul_pow, hk, mul_zero]⟩
  have hcomp : HasSubst (fun m => subst (fun i => (X i + C (lam * a i) : MvPowerSeries (Modes n) S))
      (eS (S := S) s m)) := by
    have := (hasSubst_eS (S := S) s).comp (hasSubst_trans ha')
    simpa only [coe_substAlgHom] using this
  rw [trans, subst_comp_subst_apply (hasSubst_eS s) (hasSubst_trans ha'), subst_rescale hcomp]
  congr 1
  funext m
  by_cases h : (m : ℕ) ≤ n
  · rw [bS, eS, cS, dif_pos h, dif_pos h, subst_X (hasSubst_trans ha'), mul_add, ← map_mul,
      ← mul_assoc, htl, one_mul]
  · rw [bS, eS, cS, dif_neg h, dif_neg h, ← coe_substAlgHom (hasSubst_trans ha'), map_zero]
    simp

/-- `T(a + r x)` is the rescaling by `r` of `T(a + x)`. -/
theorem subst_bS_eq_rescale (s : Fin n → Modes n) (r : S) {a : Modes n → S}
    (ha : ∀ x, IsNilpotent (a x)) (G : MvPowerSeries ℕ+ S) :
    subst (bS s r a) G = rescale (fun _ => r) (subst (bS s 1 a) G) := by
  rw [rescale_eq_subst, subst_comp_subst_apply (hasSubst_bS s 1 ha) (HasSubst.smul_X _)]
  congr 1
  funext m
  have hX : HasSubst ((fun _ => r) • X : Modes n → MvPowerSeries (Modes n) S) :=
    HasSubst.smul_X _
  by_cases h : (m : ℕ) ≤ n
  · rw [bS, bS, eS, cS, dif_pos h, dif_pos h, map_one, one_mul, subst_add hX, subst_X hX,
      ← coe_substAlgHom hX]
    congr 1
    · show _ = r • (X _ : MvPowerSeries (Modes n) S)
      rw [smul_eq_C_mul]
    · exact ((substAlgHom hX).commutes _).symm
  · rw [bS_of_lt s r a m (by omega), bS_of_lt s 1 a m (by omega), ← coe_substAlgHom hX, map_zero]

/-- The constant term of a substituted series depends only on the constant terms of the
substitution. -/
theorem constantCoeff_subst_congr {τ : Type*} {b b' : ℕ+ → MvPowerSeries τ S}
    (hb : HasSubst b) (hb' : HasSubst b') (h : ∀ m, constantCoeff (b m) = constantCoeff (b' m))
    (G : MvPowerSeries ℕ+ S) : constantCoeff (subst b G) = constantCoeff (subst b' G) := by
  rw [constantCoeff_subst hb, constantCoeff_subst hb']
  refine finsum_congr fun d => ?_
  rw [Finsupp.prod, Finsupp.prod, map_prod, map_prod]
  simp only [map_pow, h]

end ShiftSubst

end Virasoro.Sphere
