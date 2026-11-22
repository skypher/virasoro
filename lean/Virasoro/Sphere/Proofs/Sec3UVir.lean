import Virasoro.NormalOrder
import Virasoro.Proofs.VermaSpan
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Unitary positive-energy representations of the Virasoro algebra (sphere paper, Lemma 3.7)

sphere/paper.tex l.1023–1027, l.1050–1055: the space `ℋ_λ` carries a Hermitian form, a grading
by the level and operators `L_k` with the Virasoro relations and `L_k† = L_{-k}`.  This file
states that structure for a complex vector space and proves the isometry of the proof of
Lemma 3.2(i) (l.473–483) for an arbitrary highest-weight vector `P`:
`⟨L_{-Y}Q, L_{-Y'}P⟩ = ⟨h|L_Y L_{-Y'}|h⟩ ⟨Q, P⟩`.
-/

namespace Virasoro.Sphere

/-- A graded complex vector space with a definite Hermitian form and operators `L_k`, `k ∈ ℤ`,
satisfying the Virasoro relations at central charge `c`, with `L_k† = L_{-k}`, `L_{±k}`
shifting the level by `∓k`, and `L_0 = h₀ + level`. -/
structure UVir (V : Type*) [AddCommGroup V] [Module ℂ V] where
  c : ℝ
  h0 : ℝ
  L : ℤ → V →ₗ[ℂ] V
  form : V → V → ℂ
  lev : ℕ → Submodule ℂ V
  form_add_right : ∀ f g g', form f (g + g') = form f g + form f g'
  form_smul_right : ∀ (a : ℂ) f g, form f (a • g) = a * form f g
  form_conj : ∀ f g, form g f = (starRingEnd ℂ) (form f g)
  form_def : ∀ f, form f f = 0 → f = 0
  comm : ∀ (m n : ℤ) f, L m (L n f) = L n (L m f) + ((m - n : ℤ) : ℂ) • L (m + n) f +
    (if m + n = 0 then centralTerm (c : ℂ) m • f else 0)
  adj : ∀ (k : ℤ) f g, form (L k f) g = form f (L (-k) g)
  lev_fin : ∀ m, Module.Finite ℂ (lev m)
  L_lower : ∀ (k m : ℕ) x, x ∈ lev (m + k) → L (k : ℤ) x ∈ lev m
  L_kill : ∀ (k m : ℕ) x, m < k → x ∈ lev m → L (k : ℤ) x = 0
  L_raise : ∀ (k m : ℕ) x, x ∈ lev m → L (-(k : ℤ)) x ∈ lev (m + k)
  L_zero : ∀ (m : ℕ) x, x ∈ lev m → L 0 x = ((h0 : ℂ) + (m : ℂ)) • x
  orth : ∀ (m n : ℕ) x y, m ≠ n → x ∈ lev m → y ∈ lev n → form x y = 0

namespace UVir

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (R : UVir V)

theorem form_add_left (f f' g : V) : R.form (f + f') g = R.form f g + R.form f' g := by
  rw [R.form_conj g, R.form_add_right, map_add, ← R.form_conj, ← R.form_conj]

theorem form_smul_left (a : ℂ) (f g : V) :
    R.form (a • f) g = (starRingEnd ℂ) a * R.form f g := by
  rw [R.form_conj g, R.form_smul_right, map_mul, ← R.form_conj]

theorem form_zero_right (f : V) : R.form f 0 = 0 := by
  have h := R.form_smul_right 0 f 0
  rwa [zero_smul, zero_mul] at h

theorem form_zero_left (f : V) : R.form 0 f = 0 := by
  rw [R.form_conj, form_zero_right, map_zero]

theorem form_neg_right (f g : V) : R.form f (-g) = -R.form f g := by
  have h := R.form_smul_right (-1) f g
  rwa [neg_one_smul, neg_one_mul] at h

theorem form_sub_right (f g g' : V) : R.form f (g - g') = R.form f g - R.form f g' := by
  rw [sub_eq_add_neg, R.form_add_right, form_neg_right, sub_eq_add_neg]

theorem form_sum_right {ι : Type*} (s : Finset ι) (f : V) (g : ι → V) :
    R.form f (∑ i ∈ s, g i) = ∑ i ∈ s, R.form f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form_zero_right]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, R.form_add_right, ih]

theorem form_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (g : V) :
    R.form (∑ i ∈ s, f i) g = ∑ i ∈ s, R.form (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form_zero_left]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, form_add_left, ih]

/-- `L_{-Y} = L_{-y₁} ⋯ L_{-y_r}` for a word `Y = [y₁, …, y_r]`. -/
noncomputable def wordOp : List ℕ → V →ₗ[ℂ] V
  | [] => LinearMap.id
  | y :: w => R.L (-(y : ℤ)) ∘ₗ wordOp w

theorem wordOp_nil (P : V) : R.wordOp [] P = P := rfl

theorem wordOp_cons (y : ℕ) (w : List ℕ) (P : V) :
    R.wordOp (y :: w) P = R.L (-(y : ℤ)) (R.wordOp w P) := rfl

/-- `∑ a • L_{-w}P` for a list of (word, coefficient) pairs. -/
noncomputable def toV (P : V) (s : St ℂ) : V := (s.map fun t => t.2 • R.wordOp t.1 P).sum

theorem toV_nil (P : V) : R.toV P [] = 0 := rfl

theorem toV_cons (P : V) (t : List ℕ × ℂ) (s : St ℂ) :
    R.toV P (t :: s) = t.2 • R.wordOp t.1 P + R.toV P s := by
  simp [toV]

theorem toV_append (P : V) (s s' : St ℂ) : R.toV P (s ++ s') = R.toV P s + R.toV P s' := by
  simp [toV]

theorem toV_single (P : V) (w : List ℕ) (a : ℂ) : R.toV P [(w, a)] = a • R.wordOp w P := by
  simp [toV]

theorem toV_map_cons (P : V) (y : ℕ) (s : St ℂ) :
    R.toV P (s.map fun t => (y :: t.1, t.2)) = R.L (-(y : ℤ)) (R.toV P s) := by
  induction s with
  | nil => rw [List.map_nil, toV_nil, map_zero]
  | cons t s ih => rw [List.map_cons, toV_cons, toV_cons, ih, map_add, map_smul, wordOp_cons]

theorem toV_map_smul (P : V) (a : ℂ) (s : St ℂ) :
    R.toV P (s.map fun t => (t.1, a * t.2)) = a • R.toV P s := by
  induction s with
  | nil => rw [List.map_nil, toV_nil, smul_zero]
  | cons t s ih => rw [List.map_cons, toV_cons, toV_cons, ih, smul_add, mul_smul]

/-- `P` is a highest-weight vector of weight `h`. -/
def IsHW (P : V) (h : ℂ) : Prop := (∀ k : ℤ, 0 < k → R.L k P = 0) ∧ R.L 0 P = h • P

variable {R} {P : V} {h : ℂ}

theorem L_zero_wordOp (hP : R.IsHW P h) (w : List ℕ) :
    R.L 0 (R.wordOp w P) = (h + ((w.sum : ℕ) : ℂ)) • R.wordOp w P := by
  induction w with
  | nil =>
    rw [List.sum_nil, Nat.cast_zero, add_zero]
    exact hP.2
  | cons y w ih =>
    rw [wordOp_cons, R.comm, ih, map_smul, List.sum_cons]
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

/-- The normal-ordering procedure computes the action of `L_k` on `L_{-w}P`. -/
theorem L_wordOp_actWord (hP : R.IsHW P h) (w : List ℕ) : ∀ k : ℤ,
    R.L k (R.wordOp w P) = R.toV P (actWord (R.c : ℂ) h k w) := by
  induction w with
  | nil =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk, toV_single, one_smul, wordOp_cons]
      have : -((k.natAbs : ℕ) : ℤ) = k := by omega
      rw [this]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0, toV_single, hk0]
        exact hP.2
      · rw [if_neg hk0, toV_nil]
        exact hP.1 k (by omega)
  | cons y w ih =>
    intro k
    rw [actWord]
    by_cases hk : k < 0
    · rw [if_pos hk, toV_single, one_smul, wordOp_cons R (k.natAbs)]
      have : -((k.natAbs : ℕ) : ℤ) = k := by omega
      rw [this]
    · rw [if_neg hk]
      by_cases hk0 : k = 0
      · rw [if_pos hk0, toV_single, hk0, L_zero_wordOp hP, List.sum_cons]
      · rw [if_neg hk0, toV_append, toV_append, toV_map_cons,
          toV_map_smul, ← ih k, ← ih (k - y), wordOp_cons, R.comm]
        have e1 : k + -(y : ℤ) = k - y := by ring
        have e2 : k - -(y : ℤ) = k + y := by ring
        rw [e1, e2]
        congr 1
        by_cases hky : k = y
        · rw [if_pos hky, if_pos (by omega), toV_single]
        · rw [if_neg hky, if_neg (by omega), toV_nil]

theorem toV_actSt (hP : R.IsHW P h) (k : ℤ) (s : St ℂ) :
    R.toV P (actSt (R.c : ℂ) h k s) = R.L k (R.toV P s) := by
  induction s with
  | nil => simp [actSt, toV_nil]
  | cons t s ih =>
    have e : actSt (R.c : ℂ) h k (t :: s)
        = ((actWord (R.c : ℂ) h k t.1).map fun u => (u.1, t.2 * u.2)) ++
          actSt (R.c : ℂ) h k s := by
      simp [actSt]
    rw [e, toV_append, ih, toV_map_smul, toV_cons, map_add, map_smul, L_wordOp_actWord hP]

/-- `⟨Q, ∑ a • L_{-w}P⟩` is the coefficient of the empty word times `⟨Q, P⟩`, for `Q` killed
by the `L_k`, `k > 0`. -/
theorem form_hw_toV {Q : V} (hQ : ∀ k : ℤ, 0 < k → R.L k Q = 0) (P : V) (s : St ℂ)
    (hs : PosSt s) : R.form Q (R.toV P s) = vac s * R.form Q P := by
  induction s with
  | nil => simp [toV_nil, vac, form_zero_right]
  | cons t s ih =>
    have hs' : PosSt s := fun u hu => hs u (List.mem_cons_of_mem _ hu)
    have ht : PosWord t.1 := hs t List.mem_cons_self
    rw [toV_cons, R.form_add_right, R.form_smul_right, ih hs']
    have hv : vac (t :: s) = (if t.1.isEmpty then t.2 else 0) + vac s := by simp [vac]
    rw [hv, add_mul]
    congr 1
    obtain ⟨w, a⟩ := t
    cases w with
    | nil =>
      show a * R.form Q P = _
      simp
    | cons y w =>
      have hy : 0 < y := ht y List.mem_cons_self
      have h1 := R.adj (y : ℤ) Q (R.wordOp w P)
      rw [hQ _ (by exact_mod_cast hy), form_zero_left] at h1
      show a * R.form Q (R.L (-(y : ℤ)) (R.wordOp w P)) = _
      rw [← h1]
      simp

theorem form_wordOp_toV (hP : R.IsHW P h) (Q : V) : ∀ (Y : List ℕ) (s : St ℂ),
    R.form (R.wordOp Y Q) (R.toV P s) =
      R.form Q (R.toV P (Y.foldl (fun (s : St ℂ) (y : ℕ) => actSt (R.c : ℂ) h (y : ℤ) s) s)) := by
  intro Y
  induction Y with
  | nil => intro s; rfl
  | cons y Y ih =>
    intro s
    have h1 := R.adj (-(y : ℤ)) (R.wordOp Y Q) (R.toV P s)
    rw [neg_neg] at h1
    rw [wordOp_cons, h1, ← toV_actSt hP, ih, List.foldl_cons]

theorem posSt_foldl_actSt' (c h : ℂ) : ∀ (Y : List ℕ) (s : St ℂ), PosSt s →
    PosSt (Y.foldl (fun (s : St ℂ) (y : ℕ) => actSt c h (y : ℤ) s) s) := by
  intro Y
  induction Y with
  | nil => intro s hs; exact hs
  | cons y Y ih => intro s hs; exact ih _ (posSt_actSt c h _ hs)

/-- `⟨L_{-Y}Q, L_{-Y'}P⟩ = ⟨h|L_Y L_{-Y'}|h⟩ ⟨Q, P⟩` for a highest-weight vector `P` of weight
`h` and `Q` killed by the `L_k`, `k > 0`. -/
theorem form_wordOp_wordOp (hP : R.IsHW P h) {Q : V} (hQ : ∀ k : ℤ, 0 < k → R.L k Q = 0)
    (Y Y' : List ℕ) (hY' : PosWord Y') :
    R.form (R.wordOp Y Q) (R.wordOp Y' P) = gramWord (R.c : ℂ) h Y Y' * R.form Q P := by
  have h0 : R.wordOp Y' P = R.toV P [(Y', 1)] := by rw [toV_single, one_smul]
  have hp : PosSt ([(Y', 1)] : St ℂ) := by
    intro t ht
    rw [List.mem_singleton] at ht
    rw [ht]
    exact hY'
  rw [h0, form_wordOp_toV hP, form_hw_toV hQ _ _ (posSt_foldl_actSt' _ _ Y _ hp)]
  rfl

end UVir

end Virasoro.Sphere
