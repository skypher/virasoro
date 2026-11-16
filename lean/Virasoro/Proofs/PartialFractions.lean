import Virasoro.Proofs.Sec4PF
import Virasoro.Proofs.TorusDegree

/-!
# Partial fractions over a field

A quotient `P / ∏_{λ ∈ S} (X - λ)^{m_λ}` with `deg P < ∑ m_λ` is a finite sum of simple
fractions `a / (X - λ)^k`, `λ ∈ S`, `k ≥ 1`; and a finite sum of simple fractions with poles in
`S` is the sum of its principal parts at the points of `S`.
-/

namespace Virasoro

open Polynomial

variable {K : Type*} [Field K]

/-- `f` is a finite sum of simple fractions `a / (X - λ)^k` with `λ ∈ S`, `k ≥ 1`. -/
def IsPoleSum (S : Finset K) (f : RatFunc K) : Prop :=
  ∃ (n : ℕ) (A : K → ℕ → K), f = ∑ lam ∈ S, ∑ k ∈ Finset.Icc 1 n,
    RatFunc.C (A lam k) / (RatFunc.X - RatFunc.C lam) ^ k

theorem isPoleSum_zero (S : Finset K) : IsPoleSum S 0 :=
  ⟨0, fun _ _ => 0, by simp⟩

theorem poleSum_extend (A : ℕ → K) (D : RatFunc K) {n n' : ℕ} (h : n ≤ n') :
    ∑ k ∈ Finset.Icc 1 n, RatFunc.C (A k) / D ^ k
      = ∑ k ∈ Finset.Icc 1 n', RatFunc.C (if k ≤ n then A k else 0) / D ^ k := by
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right h)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Icc.1 hk).2]
  · intro k hk hk'
    have : ¬ k ≤ n := fun hle => hk' (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hk).1, hle⟩)
    rw [if_neg this, map_zero, zero_div]

theorem IsPoleSum.add {S : Finset K} {f g : RatFunc K} (hf : IsPoleSum S f)
    (hg : IsPoleSum S g) : IsPoleSum S (f + g) := by
  obtain ⟨n, A, rfl⟩ := hf
  obtain ⟨n', A', rfl⟩ := hg
  refine ⟨max n n', fun lam k => (if k ≤ n then A lam k else 0)
    + (if k ≤ n' then A' lam k else 0), ?_⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [poleSum_extend (A lam) _ (le_max_left n n'), poleSum_extend (A' lam) _ (le_max_right n n'),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_add, add_div]

theorem IsPoleSum.const_mul {S : Finset K} {f : RatFunc K} (a : K) (hf : IsPoleSum S f) :
    IsPoleSum S (RatFunc.C a * f) := by
  obtain ⟨n, A, rfl⟩ := hf
  refine ⟨n, fun lam k => a * A lam k, ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, mul_div_assoc]

theorem isPoleSum_sum {ι : Type*} {S : Finset K} (s : Finset ι) (f : ι → RatFunc K)
    (h : ∀ i ∈ s, IsPoleSum S (f i)) : IsPoleSum S (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isPoleSum_zero S
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isPoleSum_term {S : Finset K} {lam₀ : K} (h₀ : lam₀ ∈ S) (c : K) {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) : IsPoleSum S (RatFunc.C c / (RatFunc.X - RatFunc.C lam₀) ^ k₀) := by
  classical
  refine ⟨k₀, fun lam k => if lam = lam₀ ∧ k = k₀ then c else 0, ?_⟩
  rw [Finset.sum_eq_single lam₀, Finset.sum_eq_single k₀]
  · dsimp only
    rw [if_pos ⟨rfl, rfl⟩]
  · intro k _ hk
    dsimp only
    rw [if_neg (fun h => hk h.2), map_zero, zero_div]
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨hk₀, le_rfl⟩) h
  · intro lam _ hlam
    refine Finset.sum_eq_zero fun k _ => ?_
    dsimp only
    rw [if_neg (fun h => hlam h.1), map_zero, zero_div]
  · intro h
    exact absurd h₀ h

theorem IsPoleSum.mono {S S' : Finset K} {f : RatFunc K} (hf : IsPoleSum S f) (h : S ⊆ S') :
    IsPoleSum S' f := by
  classical
  obtain ⟨n, A, rfl⟩ := hf
  refine ⟨n, fun lam k => if lam ∈ S then A lam k else 0, ?_⟩
  rw [← Finset.sum_subset h]
  · refine Finset.sum_congr rfl fun lam hlam => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only
    rw [if_pos hlam]
  · intro lam _ hlam
    refine Finset.sum_eq_zero fun k _ => ?_
    dsimp only
    rw [if_neg hlam, map_zero, zero_div]

/-- A finite sum of simple fractions with poles in `S` is the sum of its principal parts. -/
theorem IsPoleSum.eq_sum_PP {S : Finset K} {f : RatFunc K} (hf : IsPoleSum S f) :
    f = ∑ lam ∈ S, PP f lam := by
  classical
  obtain ⟨n, A, hfA⟩ := hf
  have hinj : Set.InjOn (fun lam : K => lam) (S : Set K) := fun x _ y _ hxy => hxy
  conv_lhs => rw [hfA]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  have hpo : poleOrder f lam ≤ n := by
    rw [hfA]
    exact poleOrder_sum_le S (fun lam : K => lam) hinj (fun _ => n) A hlam
  have hpp : ∀ k, 1 ≤ k → k ≤ n → ppCoeff f lam k = A lam k := by
    intro k hk hkn
    rw [hfA, ppCoeff_sum S (fun lam : K => lam) hinj (fun _ => n) A hlam hk, if_pos hkn]
  unfold PP
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hpo)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [hpp k (Finset.mem_Icc.1 hk).1 ((Finset.mem_Icc.1 hk).2.trans hpo)]
  · intro k hk hk'
    have hgt : poleOrder f lam < k := by
      simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
      exact hk' hk.1
    rw [← hpp k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2, ppCoeff_eq_zero_of_gt _ _ hgt,
      map_zero, zero_div]

theorem algebraMap_X_sub_C (a : K) :
    algebraMap K[X] (RatFunc K) (X - C a) = RatFunc.X - RatFunc.C a := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem ratFunc_X_sub_C_ne (a : K) : (RatFunc.X - RatFunc.C a : RatFunc K) ≠ 0 := by
  rw [← algebraMap_X_sub_C]
  exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 (X_sub_C_ne_zero a)

/-- Peeling the factors `(X - a)^j` from a quotient `P / ((X - a)^j G₁)` with `G₁(a) ≠ 0`. -/
theorem isPoleSum_peel [DecidableEq K] {S' : Finset K} {a : K} (G₁ : K[X]) (hG₁ : G₁.eval a ≠ 0) (n₁ : ℕ)
    (hn₁ : G₁.natDegree ≤ n₁)
    (H : ∀ P' : K[X], DLt P' n₁ →
      IsPoleSum S' (algebraMap K[X] (RatFunc K) P' / algebraMap K[X] (RatFunc K) G₁)) :
    ∀ (j : ℕ) (P : K[X]), DLt P (j + n₁) →
      IsPoleSum (insert a S') (algebraMap K[X] (RatFunc K) P
        / algebraMap K[X] (RatFunc K) ((X - C a) ^ j * G₁)) := by
  have hG₁0 : G₁ ≠ 0 := by
    rintro rfl
    simp at hG₁
  have hG₁r : algebraMap K[X] (RatFunc K) G₁ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).2 hG₁0
  intro j
  induction j with
  | zero =>
    intro P hP
    rw [pow_zero, one_mul]
    rw [zero_add] at hP
    exact (H P hP).mono (Finset.subset_insert a S')
  | succ j ih =>
    intro P hP
    set c := P.eval a / G₁.eval a with hc
    have hroot : (P - C c * G₁).IsRoot a := by
      rw [IsRoot, eval_sub, eval_mul, eval_C, hc, div_mul_cancel₀ _ hG₁, sub_self]
    obtain ⟨P₁, hP₁⟩ := dvd_iff_isRoot.2 hroot
    have hR : DLt (P - C c * G₁) (j + 1 + n₁) := by
      rw [sub_eq_add_neg]
      refine hP.add (dlt_of_natDegree_lt ?_)
      rw [natDegree_neg]
      exact lt_of_le_of_lt ((natDegree_C_mul_le c G₁).trans hn₁) (by omega)
    have hP₁d : DLt P₁ (j + n₁) := by
      by_cases h0 : P₁ = 0
      · rw [h0]; exact dlt_zero _
      · have hne : P - C c * G₁ ≠ 0 := by
          rw [hP₁]
          exact mul_ne_zero (X_sub_C_ne_zero a) h0
        have h1 := hR.natDegree_lt hne
        rw [hP₁, natDegree_mul (X_sub_C_ne_zero a) h0, natDegree_X_sub_C] at h1
        exact dlt_of_natDegree_lt (by omega)
    have hsplit : algebraMap K[X] (RatFunc K) P
        / algebraMap K[X] (RatFunc K) ((X - C a) ^ (j + 1) * G₁)
        = RatFunc.C c / (RatFunc.X - RatFunc.C a) ^ (j + 1)
          + algebraMap K[X] (RatFunc K) P₁
            / algebraMap K[X] (RatFunc K) ((X - C a) ^ j * G₁) := by
      have hP' : P = C c * G₁ + (X - C a) * P₁ := by rw [← hP₁]; ring
      have hXa := ratFunc_X_sub_C_ne a
      rw [hP']
      simp only [map_add, map_mul, map_pow, algebraMap_X_sub_C, RatFunc.algebraMap_C]
      field_simp
      ring
    rw [hsplit]
    exact (isPoleSum_term (Finset.mem_insert_self a S') c (by omega)).add (ih P₁ hP₁d)

/-- Partial fractions: `P / ∏_{λ ∈ S} (X - λ)^{m_λ}` with `deg P < ∑ m_λ` is a finite sum of
simple fractions with poles in `S`. -/
theorem isPoleSum_div (S : Finset K) : ∀ (m : K → ℕ) (P : K[X]), DLt P (∑ lam ∈ S, m lam) →
    IsPoleSum S (algebraMap K[X] (RatFunc K) P
      / algebraMap K[X] (RatFunc K) (∏ lam ∈ S, (X - C lam) ^ m lam)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro m P hP
    rw [Finset.sum_empty] at hP
    have hP0 : P = 0 := by
      by_contra hne
      exact absurd (hP.natDegree_lt hne) (by omega)
    rw [hP0, map_zero, zero_div]
    exact isPoleSum_zero _
  | insert a S' ha ih =>
    intro m P hP
    rw [Finset.sum_insert ha] at hP
    rw [Finset.prod_insert ha]
    refine isPoleSum_peel (∏ lam ∈ S', (X - C lam) ^ m lam) ?_ (∑ lam ∈ S', m lam) ?_
      (fun P' hP' => ih m P' hP') (m a) P hP
    · rw [eval_prod]
      refine Finset.prod_ne_zero_iff.2 fun lam hlam => ?_
      rw [eval_pow, eval_sub, eval_X, eval_C]
      exact pow_ne_zero _ (sub_ne_zero.2 fun h => ha (h ▸ hlam))
    · refine le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun lam _ => ?_)
      refine le_trans natDegree_pow_le ?_
      rw [natDegree_X_sub_C, mul_one]

end Virasoro
