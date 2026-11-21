import Virasoro.Sphere.Cited
import Virasoro.Proofs.VermaSpan

/-!
# The Fock form and the normal ordering of the Feigin–Fuchs operators

Toward sphere paper Lemma 3.2(i) (sphere/paper.tex l.446–451, proof l.471–482): with the two
cited facts for the operators (3.2), the vectors `l_{-Y}1` have the Shapovalov matrix elements:
`⟨l_{-Y}1, l_{-Y'}1⟩ = ⟨h|L_Y L_{-Y'}|h⟩` at `c = 1 + 24μ²`, `h = λ² + μ²`.
-/

namespace Virasoro.Sphere

open MvPolynomial

/-! ### Linearity of the form (3.1) -/

theorem fockForm_eq (f g : Fock) (s : Finset (ℕ+ →₀ ℕ)) (hs : g.support ⊆ s) :
    fockForm f g = ∑ α ∈ s, (starRingEnd ℂ) (coeff α f) * coeff α g * fockNorm α := by
  unfold fockForm
  apply Finset.sum_subset hs
  intro α _ hα
  rw [notMem_support_iff.mp hα]
  simp

theorem fockForm_add_right (f g g' : Fock) :
    fockForm f (g + g') = fockForm f g + fockForm f g' := by
  classical
  rw [fockForm_eq f (g + g') (g.support ∪ g'.support) (support_add),
    fockForm_eq f g _ Finset.subset_union_left, fockForm_eq f g' _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [coeff_add]
  ring

theorem fockForm_smul_right (a : ℂ) (f g : Fock) :
    fockForm f (a • g) = a * fockForm f g := by
  rw [fockForm_eq f (a • g) g.support support_smul, fockForm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [coeff_smul, smul_eq_mul]
  ring

@[simp] theorem fockForm_zero_right (f : Fock) : fockForm f 0 = 0 := by simp [fockForm]

@[simp] theorem fockForm_zero_left (g : Fock) : fockForm 0 g = 0 := by simp [fockForm]

theorem fockForm_add_left (f f' g : Fock) :
    fockForm (f + f') g = fockForm f g + fockForm f' g := by
  unfold fockForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [coeff_add, map_add]
  ring

theorem fockForm_smul_left (a : ℂ) (f g : Fock) :
    fockForm (a • f) g = (starRingEnd ℂ) a * fockForm f g := by
  unfold fockForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [coeff_smul, smul_eq_mul, map_mul]
  ring

theorem fockForm_sum_right {ι : Type*} (s : Finset ι) (f : Fock) (g : ι → Fock) :
    fockForm f (∑ i ∈ s, g i) = ∑ i ∈ s, fockForm f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fockForm_add_right, ih]

theorem fockForm_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fock) (g : Fock) :
    fockForm (∑ i ∈ s, f i) g = ∑ i ∈ s, fockForm (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, fockForm_add_left, ih]

theorem fockForm_one_one : fockForm 1 1 = 1 := by
  rw [fockForm_eq 1 1 {0} (by
    intro α hα
    rw [mem_support_iff, coeff_one] at hα
    by_contra h
    exact hα (if_neg fun h0 => h (by simp [← h0])))]
  simp [fockNorm]

/-! ### The operators on the vacuum -/

theorem ffOp_monomial (μ lam : ℂ) (k : ℤ) (α : ℕ+ →₀ ℕ) :
    ffOp μ lam k (monomial α 1) = ffOpMono μ lam k α := by
  have h := (basisMonomials ℕ+ ℂ).constr_basis ℂ (ffOpMono μ lam k) α
  rwa [coe_basisMonomials] at h

theorem ffOp_one_pos (μ lam : ℂ) {k : ℤ} (hk : 0 < k) : ffOp μ lam k 1 = 0 := by
  have h := ffOp_monomial μ lam k 0
  rw [show (monomial (0 : ℕ+ →₀ ℕ) (1 : ℂ)) = 1 from rfl] at h
  rw [h]
  simp [ffOpMono, hk.ne', hk, dVar]

theorem ffOp_one_zero (μ lam : ℂ) : ffOp μ lam 0 1 = (lam ^ 2 + μ ^ 2) • (1 : Fock) := by
  have h := ffOp_monomial μ lam 0 0
  rw [show (monomial (0 : ℕ+ →₀ ℕ) (1 : ℂ)) = 1 from rfl] at h
  rw [h]
  simp [ffOpMono, dVar, Algebra.smul_def]

/-! ### Normal ordering -/

/-- The Fock vector represented by a list of (word, coefficient) pairs: `∑ a • l_{-w}1`. -/
noncomputable def toFock (μ lam : ℂ) (s : St ℂ) : Fock :=
  (s.map fun t => t.2 • fockWord μ lam t.1).sum

theorem toFock_nil (μ lam : ℂ) : toFock μ lam [] = 0 := rfl

theorem toFock_cons (μ lam : ℂ) (t : List ℕ × ℂ) (s : St ℂ) :
    toFock μ lam (t :: s) = t.2 • fockWord μ lam t.1 + toFock μ lam s := by
  simp [toFock]

theorem toFock_append (μ lam : ℂ) (s s' : St ℂ) :
    toFock μ lam (s ++ s') = toFock μ lam s + toFock μ lam s' := by
  simp [toFock]

theorem toFock_single (μ lam : ℂ) (w : List ℕ) (a : ℂ) :
    toFock μ lam [(w, a)] = a • fockWord μ lam w := by
  rw [toFock_cons, toFock_nil, add_zero]

theorem fockWord_cons (μ lam : ℂ) (y : ℕ) (w : List ℕ) :
    fockWord μ lam (y :: w) = ffOp μ lam (-(y : ℤ)) (fockWord μ lam w) := rfl

theorem toFock_map_cons (μ lam : ℂ) (y : ℕ) (s : St ℂ) :
    toFock μ lam (s.map fun t => (y :: t.1, t.2)) = ffOp μ lam (-(y : ℤ)) (toFock μ lam s) := by
  induction s with
  | nil => rw [List.map_nil, toFock_nil, map_zero]
  | cons t s ih =>
    rw [List.map_cons, toFock_cons, toFock_cons, ih, map_add, map_smul, fockWord_cons]

theorem toFock_map_smul (μ lam : ℂ) (a : ℂ) (s : St ℂ) :
    toFock μ lam (s.map fun t => (t.1, a * t.2)) = a • toFock μ lam s := by
  induction s with
  | nil => rw [List.map_nil, toFock_nil, smul_zero]
  | cons t s ih =>
    rw [List.map_cons, toFock_cons, toFock_cons, ih, smul_add, smul_smul]

section Cited

variable (hF : Cited_FeiginFuchsOperators)
include hF

/-- The Virasoro relation for the operators (3.2), in the form of `Verma.L_L`. -/
theorem ffOp_ffOp (μ lam : ℂ) (m n : ℤ) (f : Fock) :
    ffOp μ lam m (ffOp μ lam n f) = ffOp μ lam n (ffOp μ lam m f) +
      ((m - n : ℤ) : ℂ) • ffOp μ lam (m + n) f +
      (if m + n = 0 then centralTerm (1 + 24 * μ ^ 2) m • f else 0) := by
  have h := hF.1 μ lam m n f
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  have hc : centralTerm (1 + 24 * μ ^ 2) m = (1 + 24 * μ ^ 2) / 12 * ((m : ℂ) ^ 3 - m) := by
    simp only [centralTerm, eq_ratCast]
    push_cast
    ring
  rw [hc]
  push_cast
  abel

theorem ffOp_zero_fockWord (μ lam : ℂ) (w : List ℕ) :
    ffOp μ lam 0 (fockWord μ lam w) =
      (lam ^ 2 + μ ^ 2 + ((w.sum : ℕ) : ℂ)) • fockWord μ lam w := by
  induction w with
  | nil =>
    rw [List.sum_nil, Nat.cast_zero, add_zero]
    exact ffOp_one_zero μ lam
  | cons y w ih =>
    rw [fockWord_cons, ffOp_ffOp hF, ih, map_smul, List.sum_cons]
    have e : (0 : ℤ) + -(y : ℤ) = -(y : ℤ) := by ring
    rw [e]
    by_cases hy : -(y : ℤ) = 0
    · rw [if_pos hy]
      have hy0 : (y : ℤ) = 0 := by omega
      simp only [centralTerm_zero, zero_smul, add_zero]
      push_cast
      rw [hy0]
      module
    · rw [if_neg hy, add_zero]
      push_cast
      module

/-- The normal-ordering procedure computes the action of the operators (3.2) on `l_{-w}1`. -/
theorem ffOp_fockWord_actWord (μ lam : ℂ) (w : List ℕ) : ∀ k : ℤ,
    ffOp μ lam k (fockWord μ lam w) =
      toFock μ lam (actWord (1 + 24 * μ ^ 2) (lam ^ 2 + μ ^ 2) k w) := by
  induction w with
  | nil =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk, toFock_single, one_smul, fockWord_cons]
      have : -((k.natAbs : ℕ) : ℤ) = k := by omega
      rw [this]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0, toFock_single, hk0]
        exact ffOp_one_zero μ lam
      · rw [if_neg hk0, toFock_nil]
        exact ffOp_one_pos μ lam (by omega)
  | cons y w ih =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk, toFock_single, one_smul, fockWord_cons μ lam (k.natAbs)]
      have : -((k.natAbs : ℕ) : ℤ) = k := by omega
      rw [this]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0, toFock_single, hk0, ffOp_zero_fockWord hF, List.sum_cons]
      · rw [if_neg hk0, toFock_append, toFock_append, toFock_map_cons,
          toFock_map_smul, ← ih k, ← ih (k - y), fockWord_cons, ffOp_ffOp hF]
        have e1 : k + -(y : ℤ) = k - y := by ring
        have e2 : k - -(y : ℤ) = k + y := by ring
        rw [e1, e2]
        congr 1
        by_cases hky : k = y
        · rw [if_pos hky, if_pos (by omega), toFock_single]
        · rw [if_neg hky, if_neg (by omega), toFock_nil]

theorem toFock_actSt (μ lam : ℂ) (k : ℤ) (s : St ℂ) :
    toFock μ lam (actSt (1 + 24 * μ ^ 2) (lam ^ 2 + μ ^ 2) k s) =
      ffOp μ lam k (toFock μ lam s) := by
  induction s with
  | nil => simp [actSt, toFock_nil]
  | cons t s ih =>
    have e : actSt (1 + 24 * μ ^ 2) (lam ^ 2 + μ ^ 2) k (t :: s)
        = ((actWord (1 + 24 * μ ^ 2) (lam ^ 2 + μ ^ 2) k t.1).map fun u => (u.1, t.2 * u.2)) ++
          actSt (1 + 24 * μ ^ 2) (lam ^ 2 + μ ^ 2) k s := by
      simp [actSt]
    rw [e, toFock_append, ih, toFock_map_smul, toFock_cons, map_add, map_smul,
      ffOp_fockWord_actWord hF]

/-- `⟨1, ∑ a • l_{-w}1⟩` is the coefficient of the empty word, for words of positive integers. -/
theorem fockForm_one_toFock (μ lam : ℝ) (s : St ℂ) (hs : PosSt s) :
    fockForm 1 (toFock (μ : ℂ) (lam : ℂ) s) = vac s := by
  induction s with
  | nil => simp [toFock_nil, vac]
  | cons t s ih =>
    have hs' : PosSt s := fun u hu => hs u (List.mem_cons_of_mem _ hu)
    have ht : PosWord t.1 := hs t List.mem_cons_self
    rw [toFock_cons, fockForm_add_right, fockForm_smul_right, ih hs']
    have hv : vac (t :: s) = (if t.1.isEmpty then t.2 else 0) + vac s := by simp [vac]
    rw [hv]
    congr 1
    obtain ⟨w, a⟩ := t
    cases w with
    | nil =>
      show a * fockForm 1 1 = _
      rw [fockForm_one_one]
      simp
    | cons y w =>
      have hy : 0 < y := ht y List.mem_cons_self
      have h1 := hF.2 μ lam (y : ℤ) 1 (fockWord (μ : ℂ) (lam : ℂ) w)
      rw [ffOp_one_pos _ _ (by exact_mod_cast hy), fockForm_zero_left] at h1
      show a * fockForm 1 (ffOp (μ : ℂ) (lam : ℂ) (-(y : ℤ)) (fockWord (μ : ℂ) (lam : ℂ) w)) = _
      rw [← h1]
      simp

theorem fockForm_fockWord_toFock (μ lam : ℝ) : ∀ (Y : List ℕ) (s : St ℂ),
    fockForm (fockWord (μ : ℂ) (lam : ℂ) Y) (toFock (μ : ℂ) (lam : ℂ) s) =
      fockForm 1 (toFock (μ : ℂ) (lam : ℂ)
        (Y.foldl (fun (s : St ℂ) (y : ℕ) =>
          actSt (1 + 24 * (μ : ℂ) ^ 2) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2) (y : ℤ) s) s)) := by
  intro Y
  induction Y with
  | nil => intro s; rfl
  | cons y Y ih =>
    intro s
    have h1 := hF.2 μ lam (-(y : ℤ)) (fockWord (μ : ℂ) (lam : ℂ) Y) (toFock (μ : ℂ) (lam : ℂ) s)
    rw [neg_neg] at h1
    rw [fockWord_cons, h1, ← toFock_actSt hF, ih, List.foldl_cons]

theorem posSt_foldl_actSt (c h : ℂ) : ∀ (Y : List ℕ) (s : St ℂ), PosSt s →
    PosSt (Y.foldl (fun (s : St ℂ) (y : ℕ) => actSt c h (y : ℤ) s) s) := by
  intro Y
  induction Y with
  | nil => intro s hs; exact hs
  | cons y Y ih => intro s hs; exact ih _ (posSt_actSt c h _ hs)

/-- The isometry of Lemma 3.2(i) on words: `⟨l_{-Y}1, l_{-Y'}1⟩ = ⟨h|L_Y L_{-Y'}|h⟩`. -/
theorem fockForm_fockWord (μ lam : ℝ) (Y Y' : List ℕ) (hY' : PosWord Y') :
    fockForm (fockWord (μ : ℂ) (lam : ℂ) Y) (fockWord (μ : ℂ) (lam : ℂ) Y') =
      gramWord (1 + 24 * (μ : ℂ) ^ 2) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2) Y Y' := by
  have h0 : fockWord (μ : ℂ) (lam : ℂ) Y' = toFock (μ : ℂ) (lam : ℂ) [(Y', 1)] := by
    rw [toFock_single, one_smul]
  have hp : PosSt ([(Y', 1)] : St ℂ) := by
    intro t ht
    rw [List.mem_singleton] at ht
    rw [ht]
    exact hY'
  rw [h0, fockForm_fockWord_toFock hF, fockForm_one_toFock hF μ lam _ (posSt_foldl_actSt hF _ _ Y _ hp)]
  rfl

end Cited

end Virasoro.Sphere
