import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Congruence diagonalization over `K⟦X⟧` (proof of Proposition 11.2(ii), paper.tex l.2461–2466)

"Over the discrete valuation ring `ℂ[[x]]` (of characteristic `0`), every nondegenerate symmetric
matrix is congruent over `GL(ℂ[[x]])` to a diagonal matrix": there is `U ∈ GL(K⟦X⟧)` with
`Uᵀ G U = diag(x^{e_a} u_a)`, `u_a(0) ≠ 0`.

The proof is the usual one: among the entries of the part not yet diagonalized choose one of
lowest order; if no diagonal entry has that order, add one basis vector to another (the new
diagonal entry is `g_aa + 2 g_ab + g_bb`, here characteristic `≠ 2` is used); then clear the row
and column of that diagonal entry, which divides all other entries.
-/

namespace Virasoro

set_option linter.unusedSectionVars false

open PowerSeries Matrix

variable {K : Type*} [Field K] [CharZero K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {G : Matrix ι ι K⟦X⟧}

/-- The bilinear form `uᵀ G v`. -/
noncomputable def bf (G : Matrix ι ι K⟦X⟧) (u v : ι → K⟦X⟧) : K⟦X⟧ := u ⬝ᵥ G *ᵥ v

theorem bf_add_left (u u' v : ι → K⟦X⟧) : bf G (u + u') v = bf G u v + bf G u' v :=
  add_dotProduct _ _ _

theorem bf_smul_left (t : K⟦X⟧) (u v : ι → K⟦X⟧) : bf G (t • u) v = t * bf G u v := by
  rw [bf, smul_dotProduct, smul_eq_mul]; rfl

theorem bf_add_right (u v v' : ι → K⟦X⟧) : bf G u (v + v') = bf G u v + bf G u v' := by
  rw [bf, mulVec_add, dotProduct_add]; rfl

theorem bf_smul_right (t : K⟦X⟧) (u v : ι → K⟦X⟧) : bf G u (t • v) = t * bf G u v := by
  rw [bf, mulVec_smul, dotProduct_smul, smul_eq_mul]; rfl

theorem bf_symm (hG : G.IsSymm) (u v : ι → K⟦X⟧) : bf G u v = bf G v u := by
  rw [bf, bf, dotProduct_mulVec, ← mulVec_transpose, hG.eq, dotProduct_comm]

theorem gram_entry (w : ι → ι → K⟦X⟧) (a b : ι) :
    (Matrix.of w * G * (Matrix.of w)ᵀ) a b = bf G (w a) (w b) := by
  rw [Matrix.mul_assoc]
  simp only [bf, Matrix.mul_apply, dotProduct, mulVec, Matrix.transpose_apply, Matrix.of_apply]

/-- Rows `w a` of a unimodular matrix that are `G`-orthogonal outside the set `S`. -/
structure PartDiag (G : Matrix ι ι K⟦X⟧) (S : Finset ι) (w : ι → ι → K⟦X⟧) : Prop where
  unit : IsUnit (Matrix.of w).det
  orth : ∀ a b, a ≠ b → (a ∉ S ∨ b ∉ S) → bf G (w a) (w b) = 0

theorem PartDiag.exists_ne_zero (hdet : G.det ≠ 0) {S : Finset ι} {w : ι → ι → K⟦X⟧}
    (h : PartDiag G S w) {a₀ : ι} (ha₀ : a₀ ∈ S) : ∃ b ∈ S, bf G (w a₀) (w b) ≠ 0 := by
  by_contra hall
  push_neg at hall
  have h0 : (Matrix.of w * G * (Matrix.of w)ᵀ).det = 0 := by
    refine det_eq_zero_of_row_eq_zero a₀ fun b => ?_
    rw [gram_entry]
    by_cases hb : b ∈ S
    · exact hall b hb
    · exact h.orth a₀ b (fun e => hb (e ▸ ha₀)) (Or.inr hb)
  rw [det_mul, det_mul, det_transpose] at h0
  rcases mul_eq_zero.1 h0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact h.unit.ne_zero h2
    · exact hdet h2
  · exact h.unit.ne_zero h1

/-- The lowest order `m` of the entries with indices in `S`. -/
theorem PartDiag.exists_min (hdet : G.det ≠ 0) {S : Finset ι} {w : ι → ι → K⟦X⟧}
    (h : PartDiag G S w) (hS : S.Nonempty) :
    ∃ m : ℕ, (∀ c ∈ S, ∀ d ∈ S, (X : K⟦X⟧) ^ m ∣ bf G (w c) (w d)) ∧
      ∃ a ∈ S, ∃ b ∈ S, coeff m (bf G (w a) (w b)) ≠ 0 := by
  classical
  have hex : ∃ m : ℕ, ∃ a ∈ S, ∃ b ∈ S, coeff m (bf G (w a) (w b)) ≠ 0 := by
    obtain ⟨a₀, ha₀⟩ := hS
    obtain ⟨b, hb, hne⟩ := h.exists_ne_zero hdet ha₀
    by_contra hc
    push_neg at hc
    exact hne (PowerSeries.ext fun m => by rw [hc m a₀ ha₀ b hb, map_zero])
  refine ⟨Nat.find hex, fun c hc d hd => ?_, Nat.find_spec hex⟩
  rw [X_pow_dvd_iff]
  intro m' hm'
  by_contra hne
  exact Nat.find_min hex hm' ⟨c, hc, d, hd, hne⟩

/-- A diagonal entry of lowest order, after adding one row to another if necessary. -/
theorem PartDiag.pivot (hG : G.IsSymm) {S : Finset ι} {w : ι → ι → K⟦X⟧}
    (h : PartDiag G S w) {m : ℕ}
    (hdvd : ∀ c ∈ S, ∀ d ∈ S, (X : K⟦X⟧) ^ m ∣ bf G (w c) (w d))
    (hmin : ∃ a ∈ S, ∃ b ∈ S, coeff m (bf G (w a) (w b)) ≠ 0) :
    ∃ (w' : ι → ι → K⟦X⟧) (k : ι), k ∈ S ∧ PartDiag G S w' ∧
      (∀ c ∈ S, ∀ d ∈ S, (X : K⟦X⟧) ^ m ∣ bf G (w' c) (w' d)) ∧
      coeff m (bf G (w' k) (w' k)) ≠ 0 := by
  obtain ⟨a, ha, b, hb, hab⟩ := hmin
  by_cases h1 : coeff m (bf G (w a) (w a)) ≠ 0
  · exact ⟨w, a, ha, h, hdvd, h1⟩
  by_cases h2 : coeff m (bf G (w b) (w b)) ≠ 0
  · exact ⟨w, b, hb, h, hdvd, h2⟩
  push_neg at h1 h2
  have hne : a ≠ b := by
    rintro rfl
    exact hab h1
  have hwa : Function.update w a (w a + w b) a = w a + w b := Function.update_self ..
  have hwc : ∀ c, c ≠ a → Function.update w a (w a + w b) c = w c :=
    fun c hc => Function.update_of_ne hc ..
  refine ⟨Function.update w a (w a + w b), a, ha, ⟨?_, ?_⟩, ?_, ?_⟩
  · have e : (Matrix.of (Function.update w a (w a + w b))).det = (Matrix.of w).det :=
      det_updateRow_add_self (Matrix.of w) hne
    rw [e]
    exact h.unit
  · intro c d hcd hS'
    by_cases hc : c = a
    · subst hc
      have hd : d ∉ S := hS'.resolve_left (fun hn => hn ha)
      rw [hwa, hwc d (Ne.symm hcd), bf_add_left, h.orth c d hcd (Or.inr hd),
        h.orth b d (fun e => hd (e ▸ hb)) (Or.inr hd), add_zero]
    · by_cases hd : d = a
      · subst hd
        have hc' : c ∉ S := hS'.resolve_right (fun hn => hn ha)
        rw [hwa, hwc c hc, bf_add_right, h.orth c d hcd (Or.inl hc'),
          h.orth c b (fun e => hc' (e ▸ hb)) (Or.inl hc'), add_zero]
      · rw [hwc c hc, hwc d hd]
        exact h.orth c d hcd hS'
  · intro c hc d hd
    by_cases hca : c = a
    · subst hca
      by_cases hda : d = c
      · subst hda
        rw [hwa, bf_add_left, bf_add_right, bf_add_right]
        exact dvd_add (dvd_add (hdvd _ ha _ ha) (hdvd _ ha _ hb))
          (dvd_add (hdvd _ hb _ ha) (hdvd _ hb _ hb))
      · rw [hwa, hwc d hda, bf_add_left]
        exact dvd_add (hdvd _ ha _ hd) (hdvd _ hb _ hd)
    · by_cases hda : d = a
      · subst hda
        rw [hwa, hwc c hca, bf_add_right]
        exact dvd_add (hdvd _ hc _ hd) (hdvd _ hc _ hb)
      · rw [hwc c hca, hwc d hda]
        exact hdvd _ hc _ hd
  · rw [hwa, bf_add_left, bf_add_right, bf_add_right, bf_symm hG (w b) (w a), map_add, map_add,
      map_add, h1, h2, zero_add, add_zero, ← two_mul]
    exact mul_ne_zero two_ne_zero hab

/-- Clearing the row and column of a diagonal entry of lowest order. -/
theorem PartDiag.eliminate (hG : G.IsSymm) {S : Finset ι} {w : ι → ι → K⟦X⟧}
    (h : PartDiag G S w) {m : ℕ} {k : ι} (hk : k ∈ S)
    (hdvd : ∀ c ∈ S, ∀ d ∈ S, (X : K⟦X⟧) ^ m ∣ bf G (w c) (w d))
    (hkk : coeff m (bf G (w k) (w k)) ≠ 0) : ∃ w' : ι → ι → K⟦X⟧, PartDiag G (S.erase k) w' := by
  classical
  obtain ⟨q, hq⟩ := hdvd k hk k hk
  have hqu : IsUnit q := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply]
    have e : coeff m (X ^ m * q) = coeff 0 q := by
      have := coeff_X_pow_mul q m 0
      rwa [zero_add] at this
    rw [hq, e] at hkk
    exact IsUnit.mk0 _ hkk
  obtain ⟨qi, hqi⟩ := hqu.exists_right_inv
  have ht : ∀ c, ∃ t : K⟦X⟧, c ∈ S → t * bf G (w k) (w k) = bf G (w k) (w c) := by
    intro c
    by_cases hc : c ∈ S
    · obtain ⟨qc, hqc⟩ := hdvd k hk c hc
      refine ⟨qc * qi, fun _ => ?_⟩
      rw [hq, hqc]
      linear_combination (X ^ m * qc) * hqi
    · exact ⟨0, fun hc' => absurd hc' hc⟩
  choose t ht using ht
  let cf : ι → K⟦X⟧ := fun c => if c ∈ S ∧ c ≠ k then -t c else 0
  have hcf0 : ∀ c, (c ∉ S ∨ c = k) → cf c = 0 := by
    intro c hc
    simp only [cf]
    rw [if_neg]
    rintro ⟨h1, h2⟩
    rcases hc with hc | hc
    · exact hc h1
    · exact h2 hc
  have key : ∀ a b, a ≠ b → (a ∉ S ∨ a = k) →
      bf G (w a + cf a • w k) (w b + cf b • w k) = 0 := by
    intro a b hab ha
    rw [hcf0 a ha, zero_smul, add_zero, bf_add_right, bf_smul_right]
    rcases ha with ha | rfl
    · rw [h.orth a b hab (Or.inl ha), h.orth a k (fun e => ha (e ▸ hk)) (Or.inl ha), mul_zero,
        add_zero]
    · by_cases hb : b ∈ S
      · have : cf b = -t b := by
          simp only [cf]
          rw [if_pos ⟨hb, Ne.symm hab⟩]
        rw [this, neg_mul, ht b hb, add_neg_cancel]
      · rw [h.orth a b hab (Or.inr hb), hcf0 b (Or.inl hb), zero_mul, add_zero]
  refine ⟨fun c => w c + cf c • w k, ⟨?_, ?_⟩⟩
  · have e : (Matrix.of fun c => w c + cf c • w k).det = (Matrix.of w).det :=
      det_eq_of_forall_row_eq_smul_add_const cf k (hcf0 k (Or.inr rfl)) fun i j => by
        simp only [Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact h.unit
  · intro a b hab hS'
    simp only [Finset.mem_erase, not_and_or, not_not] at hS'
    rcases hS' with (ha | ha) | (hb | hb)
    · exact key a b hab (Or.inr ha)
    · exact key a b hab (Or.inl ha)
    · rw [bf_symm hG]; exact key b a (Ne.symm hab) (Or.inr hb)
    · rw [bf_symm hG]; exact key b a (Ne.symm hab) (Or.inl hb)

/-- A unimodular matrix with pairwise `G`-orthogonal rows. -/
theorem exists_orth_rows (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    ∃ w : ι → ι → K⟦X⟧, IsUnit (Matrix.of w).det ∧ ∀ a b, a ≠ b → bf G (w a) (w b) = 0 := by
  have main : ∀ (n : ℕ) (S : Finset ι), S.card = n → ∀ w, PartDiag G S w →
      ∃ w', PartDiag G ∅ w' := by
    intro n
    induction n with
    | zero =>
      intro S hS w h
      rw [Finset.card_eq_zero] at hS
      subst hS
      exact ⟨w, h⟩
    | succ n ih =>
      intro S hS w h
      have hne : S.Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨m, hdvd, hmin⟩ := h.exists_min hdet hne
      obtain ⟨w', k, hk, h', hdvd', hkk⟩ := h.pivot hG hdvd hmin
      obtain ⟨w'', h''⟩ := h'.eliminate hG hk hdvd' hkk
      exact ih (S.erase k) (by rw [Finset.card_erase_of_mem hk, hS]; rfl) w'' h''
  have h0 : PartDiag G Finset.univ (fun a b => (1 : Matrix ι ι K⟦X⟧) a b) := by
    refine ⟨?_, fun a b _ hS => ?_⟩
    · have e : (Matrix.of fun a b => (1 : Matrix ι ι K⟦X⟧) a b) = 1 := rfl
      rw [e, det_one]
      exact isUnit_one
    · simp at hS
  obtain ⟨w, hw⟩ := main _ Finset.univ rfl _ h0
  exact ⟨w, hw.unit, fun a b hab => hw.orth a b hab (Or.inl (Finset.notMem_empty a))⟩

/-- Congruence diagonalization over `K⟦X⟧` (paper.tex l.2461–2466). -/
theorem exists_congruence_diag (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    ∃ (U : Matrix ι ι K⟦X⟧) (e : ι → ℕ) (u : ι → K⟦X⟧), IsUnit U.det ∧ (∀ a, IsUnit (u a)) ∧
      Uᵀ * G * U = Matrix.diagonal fun a => (X : K⟦X⟧) ^ e a * u a := by
  obtain ⟨w, hw, horth⟩ := exists_orth_rows hG hdet
  have hD : Matrix.of w * G * (Matrix.of w)ᵀ = Matrix.diagonal fun a => bf G (w a) (w a) := by
    refine Matrix.ext fun a b => ?_
    rw [gram_entry, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [hab]
    · exact horth a b hab
  have hne : ∀ a, bf G (w a) (w a) ≠ 0 := by
    have h1 : (Matrix.of w * G * (Matrix.of w)ᵀ).det ≠ 0 := by
      rw [det_mul, det_mul, det_transpose]
      exact mul_ne_zero (mul_ne_zero hw.ne_zero hdet) hw.ne_zero
    rw [hD, det_diagonal, Finset.prod_ne_zero_iff] at h1
    exact fun a => h1 a (Finset.mem_univ a)
  refine ⟨(Matrix.of w)ᵀ, fun a => (bf G (w a) (w a)).order.toNat,
    fun a => divXPowOrder (bf G (w a) (w a)), by rw [det_transpose]; exact hw, fun a => ?_, ?_⟩
  · rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero, Ne, constantCoeff_divXPowOrder_eq_zero_iff]
    exact hne a
  · rw [transpose_transpose, hD]
    congr 1
    funext a
    exact X_pow_order_mul_divXPowOrder.symm

/-- A unimodular matrix whose rows `w a` are pairwise `G`-orthogonal with
`w_aᵀ G w_a = x^{e_a} u_a`, `u_a` a unit (paper.tex l.2463–2466: the columns `v_a(x)` of `U(x)`
with `B_x(v_a(x),v_b(x)) = δ_{ab} x^{e_a} u_a(x)`). -/
theorem exists_orth_basis (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    ∃ (w : ι → ι → K⟦X⟧) (e : ι → ℕ) (u : ι → K⟦X⟧), IsUnit (Matrix.of w).det ∧
      (∀ a, IsUnit (u a)) ∧ (∀ a, bf G (w a) (w a) = (X : K⟦X⟧) ^ e a * u a) ∧
      ∀ a b, a ≠ b → bf G (w a) (w b) = 0 := by
  obtain ⟨w, hw, horth⟩ := exists_orth_rows hG hdet
  have hD : Matrix.of w * G * (Matrix.of w)ᵀ = Matrix.diagonal fun a => bf G (w a) (w a) := by
    refine Matrix.ext fun a b => ?_
    rw [gram_entry, Matrix.diagonal_apply]
    split_ifs with hab
    · rw [hab]
    · exact horth a b hab
  have hne : ∀ a, bf G (w a) (w a) ≠ 0 := by
    have h1 : (Matrix.of w * G * (Matrix.of w)ᵀ).det ≠ 0 := by
      rw [det_mul, det_mul, det_transpose]
      exact mul_ne_zero (mul_ne_zero hw.ne_zero hdet) hw.ne_zero
    rw [hD, det_diagonal, Finset.prod_ne_zero_iff] at h1
    exact fun a => h1 a (Finset.mem_univ a)
  refine ⟨w, fun a => (bf G (w a) (w a)).order.toNat, fun a => divXPowOrder (bf G (w a) (w a)),
    hw, fun a => ?_, fun a => X_pow_order_mul_divXPowOrder.symm, horth⟩
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero, Ne, constantCoeff_divXPowOrder_eq_zero_iff]
  exact hne a

end Virasoro
