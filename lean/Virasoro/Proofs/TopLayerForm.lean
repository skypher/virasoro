import Virasoro.Proofs.Sec5TopCoeff
import Virasoro.Proofs.SingularPull
import Virasoro.Proofs.GramDet

/-!
# Theorem 5.9 of `paper.tex` at 70bac53: the form `B^k` on `U(Vir_-)w⁺ + U(Vir_-)w⁻`

Paper.tex l.850–869.  For singular vectors `χ`, `χ'` of different levels `ℓ`, `ℓ'` with
`J^k = U(Vir_-)χ + U(Vir_-)χ'`:
`B^k(L_{-Z}χ, j_χ y) = B^k(χ,χ) ⟨L_{-Z}|y⟩_{h+ℓ}` (contravariance and singularity of `χ`), the two
summands are `B^k`-orthogonal, and nondegeneracy of `B^k` on `J^k_N` together with injectivity
of `j_χ` gives `B^k(χ,χ) ≠ 0` and `ker G_M(c,h+ℓ) = 0`.
-/

namespace Virasoro

open Verma Module

section Form

variable {K : Type*} [Field K] [CharZero K] (c h : K)

/-- `B^i(x,y)` for vectors `x, y ∈ (J^i)_N`, through their level-`N` coordinates. -/
noncomputable def jv (i N : ℕ) (x y : Verma K c h) : K :=
  jform c h N i (comp N x) (comp N y)

variable {c h}

theorem comp_mem_layer {i N : ℕ} {x : Verma K c h} (hx : x ∈ jantzen c h i)
    (hxl : x ∈ level N) : comp N x ∈ jantzenLayer c h N i := by
  have hm : x ∈ (jantzenLayer c h N i).map (pbwCoord N) := by
    rw [map_jantzenLayer]
    exact ⟨hx, hxl⟩
  obtain ⟨u, hu, rfl⟩ := hm
  rw [comp_pbwCoord_same]
  exact hu

theorem pbwCoord_mem_jantzen {i N : ℕ} {u : Nat.Partition N → K}
    (hu : u ∈ jantzenLayer c h N i) : pbwCoord (c := c) (h := h) N u ∈ jantzen c h i := by
  have hm : pbwCoord (c := c) (h := h) N u ∈ (jantzenLayer c h N i).map (pbwCoord N) :=
    ⟨u, hu, rfl⟩
  rw [map_jantzenLayer] at hm
  exact hm.1

theorem jform_add_smul_left {N i : ℕ} (a : K) {u u' v : Nat.Partition N → K}
    (hu : u ∈ jantzenLayer c h N i) (hu' : u' ∈ jantzenLayer c h N i)
    (hv : v ∈ jantzenLayer c h N i) :
    jform c h N i (a • u + u') v = a * jform c h N i u v + jform c h N i u' v := by
  have hv2 := hv
  rw [jantzenLayer_eq_layer] at hv2
  obtain ⟨Vv, hVv⟩ := hv2
  rw [jform_eq_dot c h ((jantzenLayer c h N i).add_mem ((jantzenLayer c h N i).smul_mem a hu)
      hu') hVv, jform_eq_dot c h hu hVv, jform_eq_dot c h hu' hVv, add_dotProduct,
    smul_dotProduct, smul_eq_mul]

theorem jv_symm {i N : ℕ} {x y : Verma K c h} (hx : x ∈ jantzen c h i) (hxl : x ∈ level N)
    (hy : y ∈ jantzen c h i) (hyl : y ∈ level N) : jv c h i N x y = jv c h i N y x :=
  jform_symm c h (comp_mem_layer hx hxl) (comp_mem_layer hy hyl)

theorem jv_add_smul_left {i N : ℕ} (a : K) {x x' y : Verma K c h} (hx : x ∈ jantzen c h i)
    (hxl : x ∈ level N) (hx' : x' ∈ jantzen c h i) (hxl' : x' ∈ level N)
    (hy : y ∈ jantzen c h i) (hyl : y ∈ level N) :
    jv c h i N (a • x + x') y = a * jv c h i N x y + jv c h i N x' y := by
  unfold jv
  rw [map_add, map_smul]
  exact jform_add_smul_left a (comp_mem_layer hx hxl) (comp_mem_layer hx' hxl')
    (comp_mem_layer hy hyl)

theorem jv_zero_left {i N : ℕ} {y : Verma K c h} (hy : y ∈ jantzen c h i) (hyl : y ∈ level N) :
    jv c h i N 0 y = 0 := by
  have h1 := jv_add_smul_left (i := i) (N := N) (1 : K) (Submodule.zero_mem _)
    (Submodule.zero_mem _) (Submodule.zero_mem _) (Submodule.zero_mem _) hy hyl
  have e : (1 : K) • (0 : Verma K c h) + 0 = 0 := by
    rw [add_zero]
    exact smul_zero (M := K) (A := Verma K c h) 1
  rw [e, one_mul] at h1
  exact left_eq_add.mp h1

theorem jv_add_left {i N : ℕ} {x x' y : Verma K c h} (hx : x ∈ jantzen c h i)
    (hxl : x ∈ level N) (hx' : x' ∈ jantzen c h i) (hxl' : x' ∈ level N)
    (hy : y ∈ jantzen c h i) (hyl : y ∈ level N) :
    jv c h i N (x + x') y = jv c h i N x y + jv c h i N x' y := by
  have h1 := jv_add_smul_left (1 : K) hx hxl hx' hxl' hy hyl
  have e : (1 : K) • x + x' = x + x' := congrArg (· + x') (one_smul K x)
  rw [e, one_mul] at h1
  exact h1

theorem jv_smul_left {i N : ℕ} (a : K) {x y : Verma K c h} (hx : x ∈ jantzen c h i)
    (hxl : x ∈ level N) (hy : y ∈ jantzen c h i) (hyl : y ∈ level N) :
    jv c h i N (a • x) y = a * jv c h i N x y := by
  have h1 := jv_add_smul_left a hx hxl (Submodule.zero_mem _) (Submodule.zero_mem _) hy hyl
  rw [add_zero, jv_zero_left hy hyl, add_zero] at h1
  exact h1

theorem jv_zero_right {i N : ℕ} {x : Verma K c h} (hx : x ∈ jantzen c h i) (hxl : x ∈ level N) :
    jv c h i N x 0 = 0 := by
  rw [jv_symm hx hxl (Submodule.zero_mem _) (Submodule.zero_mem _)]
  exact jv_zero_left hx hxl

theorem jv_add_smul_right {i N : ℕ} (a : K) {x y y' : Verma K c h} (hx : x ∈ jantzen c h i)
    (hxl : x ∈ level N) (hy : y ∈ jantzen c h i) (hyl : y ∈ level N)
    (hy' : y' ∈ jantzen c h i) (hyl' : y' ∈ level N) :
    jv c h i N x (a • y + y') = a * jv c h i N x y + jv c h i N x y' := by
  rw [jv_symm hx hxl (Submodule.add_mem _ (Submodule.smul_mem _ a hy) hy')
      (Submodule.add_mem _ (Submodule.smul_mem _ a hyl) hyl'),
    jv_add_smul_left a hy hyl hy' hyl' hx hxl, jv_symm hy hyl hx hxl, jv_symm hy' hyl' hx hxl]

theorem jv_add_right {i N : ℕ} {x y y' : Verma K c h} (hx : x ∈ jantzen c h i)
    (hxl : x ∈ level N) (hy : y ∈ jantzen c h i) (hyl : y ∈ level N)
    (hy' : y' ∈ jantzen c h i) (hyl' : y' ∈ level N) :
    jv c h i N x (y + y') = jv c h i N x y + jv c h i N x y' := by
  rw [jv_symm hx hxl (Submodule.add_mem _ hy hy') (Submodule.add_mem _ hyl hyl'),
    jv_add_left hy hyl hy' hyl' hx hxl, jv_symm hy hyl hx hxl, jv_symm hy' hyl' hx hxl]

/-- A linear identity `B^i(t, v) = φ(t)` extends from a set to its span. -/
theorem jv_span {i N : ℕ} {T : Set (Verma K c h)} {v : Verma K c h} (hv : v ∈ jantzen c h i)
    (hvl : v ∈ level N) (φ : Verma K c h →ₗ[K] K)
    (hT : ∀ t ∈ T, t ∈ jantzen c h i ∧ t ∈ level N ∧ jv c h i N t v = φ t) :
    ∀ z ∈ Submodule.span K T, z ∈ jantzen c h i ∧ z ∈ level N ∧ jv c h i N z v = φ z := by
  intro z hz
  refine Submodule.span_induction (p := fun z _ => z ∈ jantzen c h i ∧ z ∈ level N ∧
    jv c h i N z v = φ z) (fun t ht => hT t ht)
    ⟨Submodule.zero_mem _, Submodule.zero_mem _, (jv_zero_left hv hvl).trans (map_zero φ).symm⟩
    ?_ ?_ hz
  · rintro x1 x2 _ _ ⟨h1, h2, h3⟩ ⟨h4, h5, h6⟩
    refine ⟨Submodule.add_mem _ h1 h4, Submodule.add_mem _ h2 h5, ?_⟩
    rw [jv_add_left h1 h2 h4 h5 hv hvl, h3, h6, map_add]
  · rintro b x _ ⟨h1, h2, h3⟩
    refine ⟨Submodule.smul_mem _ _ h1, Submodule.smul_mem _ _ h2, ?_⟩
    exact (jv_smul_left b h1 h2 hv hvl).trans (by rw [h3, map_smul, smul_eq_mul])

theorem jv_sum_right {i N : ℕ} {ι : Type*} (s : Finset ι) (a : ι → K) (y : ι → Verma K c h)
    {x : Verma K c h} (hx : x ∈ jantzen c h i) (hxl : x ∈ level N)
    (hy : ∀ t ∈ s, y t ∈ jantzen c h i) (hyl : ∀ t ∈ s, y t ∈ level N) :
    jv c h i N x (∑ t ∈ s, a t • y t) = ∑ t ∈ s, a t * jv c h i N x (y t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact jv_zero_right hx hxl
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht,
      jv_add_smul_right (a t) hx hxl (hy t (Finset.mem_insert_self t s))
        (hyl t (Finset.mem_insert_self t s))
        (Submodule.sum_mem _ fun r hr =>
          Submodule.smul_mem _ _ (hy r (Finset.mem_insert_of_mem hr)))
        (Submodule.sum_mem _ fun r hr =>
          Submodule.smul_mem _ _ (hyl r (Finset.mem_insert_of_mem hr))),
      ih (fun r hr => hy r (Finset.mem_insert_of_mem hr))
        (fun r hr => hyl r (Finset.mem_insert_of_mem hr))]

/-- Lemma 5.4(i) for vectors: `B^i(L_{-n}x, y) = B^i(x, L_n y)`. -/
theorem jv_contra {i M n N : ℕ} (hN : N = M + n) {x y : Verma K c h}
    (hx : x ∈ jantzen c h i) (hxl : x ∈ level M) (hy : y ∈ jantzen c h i) (hyl : y ∈ level N) :
    jv c h i N (L (-(n : ℤ)) x) y = jv c h i M x (L (n : ℤ) y) := by
  subst hN
  have h1 : L (-(n : ℤ)) x ∈ level (M + n) := by
    refine L_mem_level ?_ hxl
    push_cast
    ring
  have h2 : L (n : ℤ) y ∈ level M := by
    refine L_mem_level ?_ hyl
    push_cast
    ring
  refine (jform_contra c h (comp_mem_layer hx hxl) (comp_mem_layer hy hyl)
    (u' := comp (M + n) (L (-(n : ℤ)) x)) (v' := comp M (L (n : ℤ) y)) ?_ ?_).2.2
  · rw [pbwCoord_comp_of_mem_level h1, pbwCoord_comp_of_mem_level hxl]
  · rw [pbwCoord_comp_of_mem_level h2, pbwCoord_comp_of_mem_level hyl]

end Form

variable {c h : ℂ}

/-- The embedding `j_χ` of a singular vector with the properties used below. -/
theorem exists_emb (hI : Cited_VermaHomInjective) {χ : Verma ℂ c h} {ℓ : ℕ}
    (hχ : IsSingular χ ℓ) :
    ∃ j : Verma ℂ c (h + ℓ) →ₗ[ℂ] Verma ℂ c h, Function.Injective j ∧ j hw = χ ∧
      (∀ (n : ℤ) v, j (L n v) = L n (j v)) ∧ (∀ x, j x ∈ negSpan χ) ∧
      (∀ (n : ℕ) (x : Verma ℂ c (h + ℓ)), x ∈ level n → j x ∈ level (ℓ + n)) ∧
      ∀ w : List ℕ, j (neg w) = VirEnv.negOp c w • χ := by
  obtain ⟨j, hjhw, hjL, hjneg⟩ := exists_singularHom hχ.2.1 hχ.2.2
  have hj0 : j ≠ 0 := by
    intro h0
    apply hχ.1
    rw [← hjhw, h0]
    rfl
  refine ⟨j, hI c h (h + ℓ) j hjL hj0, hjhw, hjL, ?_, ?_, hjneg⟩
  · intro x
    rw [negSpan_eq_range j hjneg]
    exact ⟨x, rfl⟩
  · intro n x hx
    obtain ⟨a, rfl⟩ := hx
    rw [pbwCoord_apply, map_sum]
    refine Submodule.sum_mem _ fun Y _ => ?_
    rw [map_smul, hjneg]
    have := negOp_smul_mem_level (mem_level_of_L_zero hχ.2.1) Y.word
    rw [word_sum'] at this
    exact Submodule.smul_mem _ _ this

/-- A vector of level `0` is a multiple of the highest-weight vector. -/
theorem exists_smul_hw_of_level_zero {h' : ℂ} {y : Verma ℂ c h'} (hy : y ∈ level 0) :
    ∃ a : ℂ, y = a • hw := by
  obtain ⟨a, rfl⟩ := hy
  refine ⟨∑ Y : Nat.Partition 0, a Y, ?_⟩
  have e := Finset.sum_smul (R := ℂ) (M := Verma ℂ c h') (s := Finset.univ) (f := a) (x := hw)
  rw [pbwCoord_apply]
  refine Eq.trans (Finset.sum_congr rfl fun Y _ => ?_) e.symm
  have hY : Y.word = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro e he
    have h1 := posWord_word Y e he
    have h2 := List.sum_eq_zero_iff.1 (word_sum' Y) e he
    omega
  rw [hY, neg_nil]

/-- `B^k(L_{-w}χ, j_χ y) = B^k(χ,χ) ⟨L_{-w}|y⟩_{h+ℓ}`. -/
theorem jv_emb {k ℓ : ℕ} {χ : Verma ℂ c h} (hχ : IsSingular χ ℓ)
    (hsub : negSpan χ ≤ jantzen c h k) (j : Verma ℂ c (h + ℓ) →ₗ[ℂ] Verma ℂ c h)
    (hjhw : j hw = χ) (hjL : ∀ (n : ℤ) v, j (L n v) = L n (j v))
    (hjr : ∀ x, j x ∈ negSpan χ)
    (hjl : ∀ (n : ℕ) (x : Verma ℂ c (h + ℓ)), x ∈ level n → j x ∈ level (ℓ + n)) :
    ∀ w : List ℕ, PosWord w → ∀ y ∈ level (c := c) (h := h + ℓ) w.sum,
      jv c h k (ℓ + w.sum) (j (neg w)) (j y) =
        jv c h k ℓ χ χ * shap c (h + ℓ) (neg w) y := by
  have hχJ : χ ∈ jantzen c h k := by
    rw [← hjhw]
    exact hsub (hjr _)
  have hχl : χ ∈ level ℓ := mem_level_of_L_zero hχ.2.1
  intro w
  induction w with
  | nil =>
    intro _ y hy
    obtain ⟨a, rfl⟩ := exists_smul_hw_of_level_zero hy
    rw [neg_nil, hjhw, map_smul, hjhw, map_smul, List.sum_nil, add_zero]
    have h1 := jv_add_smul_right a hχJ hχl hχJ hχl (Submodule.zero_mem _) (Submodule.zero_mem _)
    rw [add_zero, jv_zero_right hχJ hχl, add_zero] at h1
    rw [h1, shap_hw, isVacuum_vacuum.1, smul_eq_mul, mul_one, mul_comm]
  | cons n w ih =>
    intro hw y hy
    have hn : 0 < n := hw n (List.mem_cons_self ..)
    have hw' : PosWord w := fun e he => hw e (List.mem_cons_of_mem _ he)
    rw [List.sum_cons] at hy ⊢
    have hLy : L (n : ℤ) y ∈ level (c := c) (h := h + ℓ) w.sum := by
      refine L_mem_level ?_ hy
      push_cast
      ring
    have hneg : neg (c := c) (h := h + ℓ) w ∈ level w.sum := neg_mem_level _ w hw' le_rfl
    rw [neg_cons, hjL, jv_contra (M := ℓ + w.sum) (n := n) (by omega) (hsub (hjr _))
        (hjl _ _ hneg) (hsub (hjr _)) (hjl _ _ hy), ← hjL, ih hw' _ hLy,
      shap_neg (by exact_mod_cast hn)]

/-- The summands `U(Vir_-)χ` and `U(Vir_-)χ'` are `B^k`-orthogonal when the levels differ. -/
theorem jv_orth {k ℓ ℓ' : ℕ} {χ χ' : Verma ℂ c h} (hχ : IsSingular χ ℓ)
    (hne : ℓ ≠ ℓ')
    (hsub : negSpan χ ≤ jantzen c h k) (hsub' : negSpan χ' ≤ jantzen c h k)
    (j : Verma ℂ c (h + ℓ) →ₗ[ℂ] Verma ℂ c h)
    (hjhw : j hw = χ) (hjL : ∀ (n : ℤ) v, j (L n v) = L n (j v))
    (hjr : ∀ x, j x ∈ negSpan χ)
    (hjl : ∀ (n : ℕ) (x : Verma ℂ c (h + ℓ)), x ∈ level n → j x ∈ level (ℓ + n))
    (j' : Verma ℂ c (h + ℓ') →ₗ[ℂ] Verma ℂ c h)
    (hjL' : ∀ (n : ℤ) v, j' (L n v) = L n (j' v))
    (hjr' : ∀ x, j' x ∈ negSpan χ')
    (hjl' : ∀ (n : ℕ) (x : Verma ℂ c (h + ℓ')), x ∈ level n → j' x ∈ level (ℓ' + n)) :
    ∀ w : List ℕ, PosWord w → ∀ M' : ℕ, ℓ + w.sum = ℓ' + M' →
      ∀ y ∈ level (c := c) (h := h + ℓ') M',
        jv c h k (ℓ + w.sum) (j (neg w)) (j' y) = 0 := by
  have hχJ : χ ∈ jantzen c h k := by
    rw [← hjhw]
    exact hsub (hjr _)
  have hχl : χ ∈ level ℓ := mem_level_of_L_zero hχ.2.1
  intro w
  induction w with
  | nil =>
    intro _ M' hM y hy
    rw [List.sum_nil, add_zero] at hM ⊢
    rw [neg_nil, hjhw]
    obtain ⟨a, rfl⟩ := hy
    rw [pbwCoord_apply, map_sum]
    simp_rw [map_smul]
    have hmem : ∀ Y : Nat.Partition M', j' (neg Y.word) ∈ level ℓ := by
      intro Y
      have := hjl' _ _ (neg_word_mem_level (c := c) (h := h + ℓ') Y)
      rwa [← hM] at this
    rw [jv_sum_right _ _ _ hχJ hχl (fun Y _ => hsub' (hjr' _)) (fun Y _ => hmem Y)]
    refine Finset.sum_eq_zero fun Y _ => ?_
    have hpos := posWord_word Y
    have hsum := word_sum' Y
    rcases hYw : Y.word with _ | ⟨n, rest⟩
    · rw [hYw, List.sum_nil] at hsum
      omega
    · rw [hYw] at hpos hsum
      rw [List.sum_cons] at hsum
      have hrest : PosWord rest := fun e he => hpos e (List.mem_cons_of_mem _ he)
      have hz : neg (c := c) (h := h + ℓ') rest ∈ level rest.sum :=
        neg_mem_level _ rest hrest le_rfl
      have hY := hmem Y
      rw [hYw, neg_cons, hjL'] at hY
      have hYJ : L (-(n : ℤ)) (j' (neg rest)) ∈ jantzen c h k := by
        rw [← hjL', ← neg_cons]
        exact hsub' (hjr' _)
      rw [neg_cons, hjL', jv_symm hχJ hχl hYJ hY,
        jv_contra (M := ℓ' + rest.sum) (n := n) (by omega) (hsub' (hjr' _)) (hjl' _ _ hz)
          hχJ hχl,
        hχ.2.2 n (by exact_mod_cast hpos n (List.mem_cons_self ..)),
        jv_zero_right (hsub' (hjr' _)) (hjl' _ _ hz), mul_zero]
  | cons n w ih =>
    intro hw M' hM y hy
    have hw' : PosWord w := fun e he => hw e (List.mem_cons_of_mem _ he)
    rw [List.sum_cons] at hM ⊢
    have hneg : neg (c := c) (h := h + ℓ) w ∈ level w.sum := neg_mem_level _ w hw' le_rfl
    have hy' : j' y ∈ level (ℓ + (n + w.sum)) := by
      rw [hM]
      exact hjl' _ _ hy
    rw [neg_cons, hjL, jv_contra (M := ℓ + w.sum) (n := n) (by omega) (hsub (hjr _))
        (hjl _ _ hneg) (hsub' (hjr' _)) hy', ← hjL']
    by_cases hnM : n ≤ M'
    · refine ih hw' (M' - n) (by omega) _ (L_mem_level ?_ hy)
      push_cast [hnM]
      ring
    · rw [L_eq_zero_of_level (by exact_mod_cast not_le.1 hnM) hy, map_zero]
      exact jv_zero_right (hsub (hjr _)) (hjl _ _ hneg)

/-- The level-`N` part of a vector of `U(Vir_-)χ` is a combination of the vectors `L_{-w}χ` of
level `N`. -/
theorem pbwCoord_comp_negSpan_mem_span {χ : Verma ℂ c h} {ℓ : ℕ} (hχ : χ ∈ level ℓ) (N : ℕ)
    {b : Verma ℂ c h} (hb : b ∈ negSpan χ) :
    pbwCoord N (comp N b) ∈ Submodule.span ℂ
      {v : Verma ℂ c h | ∃ w : List ℕ, PosWord w ∧ ℓ + w.sum = N ∧ v = VirEnv.negOp c w • χ} := by
  unfold negSpan at hb
  refine Submodule.span_induction (p := fun b _ => pbwCoord N (comp N b) ∈ Submodule.span ℂ
    {v : Verma ℂ c h | ∃ w : List ℕ, PosWord w ∧ ℓ + w.sum = N ∧ v = VirEnv.negOp c w • χ})
    ?_ ?_ ?_ ?_ hb
  · rintro _ ⟨w, rfl⟩
    have hl := negOp_smul_mem_level hχ (w.map (fun x : ℕ+ => (x : ℕ)))
    by_cases hN : ℓ + (w.map (fun x : ℕ+ => (x : ℕ))).sum = N
    · rw [hN] at hl
      rw [pbwCoord_comp_of_mem_level hl]
      refine Submodule.subset_span ⟨_, ?_, hN, rfl⟩
      intro e he
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 he
      exact a.pos
    · rw [comp_of_mem_level_ne hN hl, map_zero]
      exact Submodule.zero_mem _
  · rw [map_zero, map_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [map_add, map_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [map_smul, map_smul]
    exact Submodule.smul_mem _ _ hx

end Virasoro
