import Virasoro.Proofs.JFormSeries
import Virasoro.Proofs.JantzenSub
import Virasoro.Proofs.ResidueCore1
import Virasoro.Proofs.Family
import Virasoro.Proofs.PBWBasis
import Virasoro.Statements.Sec5c

/-!
# Lemma 5.4 of `paper.tex` at 70bac53: Jantzen forms and the top coefficient

(i) Two families for `u` differ by `x f(x)`, and `v(x)ᵀ G x f(x) = x (G v(x))ᵀ f(x) ∈ x^{i+1}`
by the symmetry of `G_N`; `L_{-n}u(x)` and `L_n v(x)`, computed in `M(c,h+x)`, are families, and
contravariance of the Shapovalov form of `M(c,h+x)` gives `B^i(L_{-n}u,v) = B^i(u,L_nv)`.
(ii) For `u ∈ J^k_N` with `G u(x) = x^k g(x)`: `B^k(u,v) = vᵀ g(0)`; the family `x^k G⁻¹ w` has
value `S w` and `g(0) = w`.  (iii) The families `u` and `u + x u₁`.
-/

namespace Virasoro

open Polynomial

variable {K : Type*} [Field K] [CharZero K] (c h : K)

theorem isJFamily_coe {N i : ℕ} {v : Nat.Partition N → K} {w : Nat.Partition N → K[X]}
    (hw : IsJFamily c h N i v w) :
    PSFam (gramLocal c h N) i v (fun Y => ((w Y : K[X]) : PowerSeries K)) := by
  obtain ⟨hw0, hdvd⟩ := hw
  refine ⟨fun Y => ?_, fun Y => ?_⟩
  · rw [← hw0 Y, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero]
  · rw [← coe_mulVec]
    have := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := K)) (hdvd Y)
    simpa [Polynomial.coeToPowerSeries.ringHom] using this

theorem jformFam_eq_psForm (N i : ℕ) (wu wv : Nat.Partition N → K[X]) :
    jformFam c h N i wu wv = psForm (gramLocal c h N) i
      (fun Y => ((wu Y : K[X]) : PowerSeries K)) (fun Y => ((wv Y : K[X]) : PowerSeries K)) := by
  have key : ∀ p : K[X], (p : PowerSeries K) = Polynomial.coeToPowerSeries.ringHom p :=
    fun _ => rfl
  rw [jformFam, psForm, ← Polynomial.coeff_coe, key, dotProduct, map_sum, dotProduct]
  congr 1
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_mul, ← key, ← key, coe_mulVec]

/-- `B^i(u,v)` is the top coefficient for every pair of power-series families. -/
theorem jform_eq_psForm {N i : ℕ} {u v : Nat.Partition N → K}
    {Vu Vv : Nat.Partition N → PowerSeries K} (hu : PSFam (gramLocal c h N) i u Vu)
    (hv : PSFam (gramLocal c h N) i v Vv) :
    jform c h N i u v = psForm (gramLocal c h N) i Vu Vv := by
  have hu' : ∃ w, IsJFamily c h N i u w := by
    have : u ∈ jantzenLayer c h N i := by
      rw [jantzenLayer_eq_layer]
      exact ⟨Vu, hu⟩
    exact this
  have hv' : ∃ w, IsJFamily c h N i v w := by
    have : v ∈ jantzenLayer c h N i := by
      rw [jantzenLayer_eq_layer]
      exact ⟨Vv, hv⟩
    exact this
  rw [jform, dif_pos hu', dif_pos hv', jformFam_eq_psForm]
  exact psForm_congr (gramLocal_isSymm c h N) (isJFamily_coe c h hu'.choose_spec) hu
    (isJFamily_coe c h hv'.choose_spec) hv

theorem jformFam_eq_jform {N i : ℕ} {u v : Nat.Partition N → K} {wu wv : Nat.Partition N → K[X]}
    (hu : IsJFamily c h N i u wu) (hv : IsJFamily c h N i v wv) :
    jformFam c h N i wu wv = jform c h N i u v := by
  rw [jform_eq_psForm c h (isJFamily_coe c h hu) (isJFamily_coe c h hv), jformFam_eq_psForm]

/-- `B^i(u,v) = uᵀ g(0)` where `G v(x) = x^i g(x)`. -/
theorem jform_eq_dot {N i : ℕ} {u v : Nat.Partition N → K} (hu : u ∈ jantzenLayer c h N i)
    {Vv : Nat.Partition N → PowerSeries K} (hv : PSFam (gramLocal c h N) i v Vv) :
    jform c h N i u v = u ⬝ᵥ topVec (gramLocal c h N) i Vv := by
  rw [jantzenLayer_eq_layer] at hu
  obtain ⟨Vu, hVu⟩ := hu
  have e : (fun j => PowerSeries.constantCoeff (Vu j)) = u := funext hVu.1
  rw [jform_eq_psForm c h hVu hv, psForm_left (gramLocal_isSymm c h N) hv.2, e]

theorem jform_symm {N i : ℕ} {u v : Nat.Partition N → K} (hu : u ∈ jantzenLayer c h N i)
    (hv : v ∈ jantzenLayer c h N i) : jform c h N i u v = jform c h N i v u := by
  rw [jantzenLayer_eq_layer] at hu hv
  obtain ⟨Vu, hVu⟩ := hu
  obtain ⟨Vv, hVv⟩ := hv
  rw [jform_eq_psForm c h hVu hVv, jform_eq_psForm c h hVv hVu,
    psForm_symm (gramLocal_isSymm c h N)]

/-- If `w(x)` is a family in the `i`-th layer, so are the coordinates of `L_n w(x)`, computed in
`M(c,h+x)` (proof of Lemma 5.3). -/
theorem dvd_gramShift_L {N M : ℕ} {n : ℤ} (hM : (M : ℤ) = (N : ℤ) - n) (i : ℕ)
    (w : Nat.Partition N → K[X]) (hdvd : ∀ Y, (X : K[X]) ^ i ∣ (gramShift c h N).mulVec w Y)
    (w₁ : Nat.Partition M → K[X])
    (hw₁ : Verma.pbwCoord (c := C c) (h := C h + (X : K[X])) M w₁ =
      Verma.L n (Verma.pbwCoord N w)) (Y : Nat.Partition M) :
    (X : K[X]) ^ i ∣ (gramShift c h M).mulVec w₁ Y := by
  have hBX := Verma.isShapovalov_shap (c := C c) (h := C h + (X : K[X]))
  have h3 := Verma.shap_neg_pbwCoord (c := C c) (h := C h + (X : K[X])) Y w₁
  rw [hw₁, ← neg_neg n, ← hBX.2] at h3
  rw [show gramShift c h M = gram (C c) (C h + (X : K[X])) M from rfl, ← h3]
  have hN : ((N : ℕ) : ℤ) = ((Y.word.sum : ℕ) : ℤ) - (-n) := by
    rw [Verma.word_sum']
    omega
  obtain ⟨a, ha⟩ := Verma.L_neg_mem_level (c := C c) (h := C h + (X : K[X]))
    (Verma.posWord_word Y) hN
  rw [← ha, Verma.pbwCoord_apply, map_sum, LinearMap.sum_apply]
  refine Finset.dvd_sum fun Z _ => ?_
  rw [map_smul, LinearMap.smul_apply, Verma.shap_neg_pbwCoord, smul_eq_mul]
  exact Dvd.dvd.mul_left (hdvd Z) _

/-- The value at `x = 0` of `L_n w(x)` is `L_n w(0)`. -/
theorem eval_L_coords {N M : ℕ} {n : ℤ} (w : Nat.Partition N → K[X]) (w₁ : Nat.Partition M → K[X])
    (hw₁ : Verma.pbwCoord (c := C c) (h := C h + (X : K[X])) M w₁ =
      Verma.L n (Verma.pbwCoord N w)) :
    Verma.L n (Verma.pbwCoord (c := c) (h := h) N fun Y => (w Y).eval 0) =
      Verma.pbwCoord M fun Y => (w₁ Y).eval 0 := by
  have hc : (evalRingHom (0 : K)) (C c) = c := by simp
  have hh : (evalRingHom (0 : K)) (C h + X) = h := by simp
  have h1 := congrArg (Verma.baseChange (evalRingHom (0 : K)) hc hh) hw₁
  rw [Verma.baseChange_pbwCoord, Verma.baseChange_L, Verma.baseChange_pbwCoord] at h1
  exact h1.symm

/-- Lemma 5.4(i), contravariance: `B^i(L_{-n}u, v) = B^i(u, L_n v)`. -/
theorem jform_contra {M n i : ℕ} {u : Nat.Partition M → K} {v : Nat.Partition (M + n) → K}
    (hu : u ∈ jantzenLayer c h M i) (hv : v ∈ jantzenLayer c h (M + n) i)
    {u' : Nat.Partition (M + n) → K} {v' : Nat.Partition M → K}
    (hu' : Verma.pbwCoord (c := c) (h := h) (M + n) u' =
      Verma.L (-(n : ℤ)) (Verma.pbwCoord (c := c) (h := h) M u))
    (hv' : Verma.pbwCoord (c := c) (h := h) M v' =
      Verma.L (n : ℤ) (Verma.pbwCoord (c := c) (h := h) (M + n) v)) :
    u' ∈ jantzenLayer c h (M + n) i ∧ v' ∈ jantzenLayer c h M i ∧
      jform c h (M + n) i u' v = jform c h M i u v' := by
  obtain ⟨wu, hwu⟩ := hu
  obtain ⟨wv, hwv⟩ := hv
  have hwu : IsJFamily c h M i u wu := hwu
  have hwv : IsJFamily c h (M + n) i v wv := hwv
  have hM1 : ((M + n : ℕ) : ℤ) = (M : ℤ) - (-(n : ℤ)) := by
    push_cast
    ring
  have hM2 : (M : ℤ) = ((M + n : ℕ) : ℤ) - (n : ℤ) := by
    push_cast
    ring
  obtain ⟨wu', hwu'⟩ := Verma.L_mem_level (c := C c) (h := C h + (X : K[X])) hM1
    (v := Verma.pbwCoord M wu) ⟨wu, rfl⟩
  obtain ⟨wv', hwv'⟩ := Verma.L_mem_level (c := C c) (h := C h + (X : K[X])) hM2
    (v := Verma.pbwCoord (M + n) wv) ⟨wv, rfl⟩
  have eu : (fun Y => (wu Y).eval 0) = u := funext hwu.1
  have ev : (fun Y => (wv Y).eval 0) = v := funext hwv.1
  have hu0 : u' = fun Y => (wu' Y).eval 0 := by
    apply Verma.pbwCoord_injective (c := c) (h := h) (M + n)
    rw [hu', ← eu, eval_L_coords c h wu wu' hwu']
  have hv0 : v' = fun Y => (wv' Y).eval 0 := by
    apply Verma.pbwCoord_injective (c := c) (h := h) M
    rw [hv', ← ev, eval_L_coords c h wv wv' hwv']
  have hfu : IsJFamily c h (M + n) i u' wu' :=
    ⟨fun Y => (congrFun hu0 Y).symm, dvd_gramShift_L c h hM1 i wu hwu.2 wu' hwu'⟩
  have hfv : IsJFamily c h M i v' wv' :=
    ⟨fun Y => (congrFun hv0 Y).symm, dvd_gramShift_L c h hM2 i wv hwv.2 wv' hwv'⟩
  refine ⟨⟨wu', hfu⟩, ⟨wv', hfv⟩, ?_⟩
  rw [← jformFam_eq_jform c h hfu hwv, ← jformFam_eq_jform c h hwu hfv, jformFam, jformFam]
  congr 1
  have h1 := Verma.shap_pbwCoord (c := C c) (h := C h + (X : K[X])) (M + n) wv wu'
  have h2 := Verma.shap_pbwCoord (c := C c) (h := C h + (X : K[X])) M wv' wu
  rw [gramForm] at h1 h2
  show wv ⬝ᵥ (gram (C c) (C h + (X : K[X])) (M + n)).mulVec wu' =
    wv' ⬝ᵥ (gram (C c) (C h + (X : K[X])) M).mulVec wu
  rw [← h1, ← h2, hwu', hwv', Verma.shap_L]

/-- Lemma 5.4(ii). -/
theorem jform_top {N k : ℕ} (hdet : (gramLocal c h N).det ≠ 0) {s : Multiset ℕ}
    (hs : IsSmith (gramLocal c h N) s) (hsup : s.sup = k) :
    (∀ v ∈ jantzenLayer c h N k,
      (∀ u ∈ jantzenLayer c h N k, jform c h N k u v = 0) → v = 0) ∧
    ∀ w : Nat.Partition N → K,
      (invCoeff (gramLocal c h N) (-(k : ℤ))).mulVec w ∈ jantzenLayer c h N k ∧
      ∀ u ∈ jantzenLayer c h N k,
        jform c h N k u ((invCoeff (gramLocal c h N) (-(k : ℤ))).mulVec w) = u ⬝ᵥ w := by
  have hpole : poleOrderInv (gramLocal c h N) = k := by rw [(smith_main hs).2.2, hsup]
  have hp : MatOrdGE (invLaurent (gramLocal c h N)) (-(k : ℤ)) := by
    have := matOrdGE_inv (gramLocal c h N)
    rwa [hpole] at this
  have hS := fun w : Nat.Partition N → K => scaled_psFam hdet hp w
  have hmem : ∀ w : Nat.Partition N → K,
      (invCoeff (gramLocal c h N) (-(k : ℤ))).mulVec w ∈ jantzenLayer c h N k := fun w => by
    rw [jantzenLayer_eq_layer]
    exact ⟨_, (hS w).1⟩
  have hval : ∀ w : Nat.Partition N → K, ∀ u ∈ jantzenLayer c h N k,
      jform c h N k u ((invCoeff (gramLocal c h N) (-(k : ℤ))).mulVec w) = u ⬝ᵥ w :=
    fun w u hu => by rw [jform_eq_dot c h hu (hS w).1, (hS w).2]
  refine ⟨fun v hv hzero => ?_, fun w => ⟨hmem w, hval w⟩⟩
  funext Y
  have h1 := hzero _ (hmem (Pi.single Y 1))
  rw [jform_symm c h (hmem _) hv, hval _ v hv] at h1
  simpa using h1

/-- Lemma 5.4(iii), first form. -/
theorem jform_one {N : ℕ} {u v : Nat.Partition N → K} (hu : u ∈ jantzenLayer c h N 1)
    (hv : v ∈ jantzenLayer c h N 1) :
    jform c h N 1 u v = cross1 (gramLocal c h N) v u := by
  have hu2 := hu
  rw [jantzenLayer_eq_layer] at hu2
  obtain ⟨Vu, hVu⟩ := hu2
  have h0 := coeffMat_zero_mulVec_of_psFam le_rfl hVu
  have hfam : PSFam (gramLocal c h N) 1 u (fun Y => PowerSeries.C (u Y)) := by
    refine ⟨fun Y => by simp, fun Y => ?_⟩
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    obtain rfl : m = 0 := by omega
    rw [coeff_mulVec_C, h0]
    rfl
  rw [jform_symm c h hu hv, jform_eq_dot c h hv hfam, cross1]
  congr 1
  funext Y
  exact coeff_mulVec_C _ 1 u Y

/-- Lemma 5.4(iii), second form. -/
theorem jform_two {N : ℕ} {u v : Nat.Partition N → K} (hu : u ∈ jantzenLayer c h N 2)
    (hv : v ∈ jantzenLayer c h N 2) {u₁ : Nat.Partition N → K}
    (hu₁ : (coeffMat 0 (gramLocal c h N)).mulVec u₁ = -(coeffMat 1 (gramLocal c h N)).mulVec u) :
    jform c h N 2 u v = cross2 (gramLocal c h N) v u u₁ := by
  have hu2 := hu
  rw [jantzenLayer_eq_layer] at hu2
  obtain ⟨Vu, hVu⟩ := hu2
  have h0 := coeffMat_zero_mulVec_of_psFam (by norm_num) hVu
  have hfam : PSFam (gramLocal c h N) 2 u
      (fun Y => PowerSeries.C (u Y) + PowerSeries.X * PowerSeries.C (u₁ Y)) := by
    refine ⟨fun Y => by simp, fun Y => ?_⟩
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    obtain rfl | rfl : m = 0 ∨ m = 0 + 1 := by omega
    · rw [coeff_zero_mulVec_lin, h0]
      rfl
    · rw [coeff_succ_mulVec_lin, hu₁]
      simp
  rw [jform_symm c h hu hv, jform_eq_dot c h hv hfam, cross2]
  congr 1
  funext Y
  exact coeff_succ_mulVec_lin _ 1 u u₁ Y

/-- Paper label: lem:top-coefficient -/
theorem lem_top_coefficient : Stmt_lem_top_coefficient := by
  intro c h
  refine ⟨fun N i _ => ⟨?_, ?_, ?_⟩, ?_, ?_, fun N => ⟨?_, ?_⟩⟩
  · intro u v wu wv hu hv
    exact jformFam_eq_jform c h hu hv
  · intro u hu v hv
    exact jform_symm c h hu hv
  · intro a u hu u' hu' v hv
    have hv2 := hv
    rw [jantzenLayer_eq_layer] at hv2
    obtain ⟨Vv, hVv⟩ := hv2
    rw [jform_eq_dot c h ((jantzenLayer c h N i).add_mem ((jantzenLayer c h N i).smul_mem a hu)
        hu') hVv, jform_eq_dot c h hu hVv, jform_eq_dot c h hu' hVv, add_dotProduct,
      smul_dotProduct, smul_eq_mul]
  · intro M n i _ _ u hu v hv u' v' hu' hv'
    exact jform_contra c h hu hv hu' hv'
  · rintro N k _ hdet ⟨s, hs, hsup⟩
    exact jform_top c h hdet hs hsup
  · intro u hu v hv
    exact jform_one c h hu hv
  · intro u hu v hv u₁ hu₁
    exact jform_two c h hu hv hu₁

example : Stmt_lem_top_coefficient := lem_top_coefficient

end Virasoro
