import Virasoro.Proofs.Sec6Norm
import Virasoro.Proofs.KacField
import Virasoro.Proofs.Sec6Kac
import Virasoro.Proofs.ResidueCore4
import Virasoro.Proofs.Sec4Irr

/-!
# Generic values of `b` and the residues of `F_N`

A value `b` of a field of characteristic zero is generic at level `N` if `b ≠ 0`, no linear form
`m b² + n` with small integer coefficients vanishes, and the normalized singular vectors of the
labels of level at most `N` are regular at `b`.  For such `b` the Kac weights of level at most
`N` are distinct, no shifted weight is degenerate, and
`Res_{Δ=h_a(b)} F_{N'} = ℛ_a(b,d) F_{N'-ℓ_a}(c(b), h_a(b)+ℓ_a, d)` with a simple pole.
-/

namespace Virasoro

open Polynomial

/-- The coordinates over `ℚ(b)` of the normalized singular vector `χ_{r,s}(b)`. -/
noncomputable def normP (hN : NormalizationIdentities) (r s : ℕ) :
    Nat.Partition (r * s) → RatFunc ℚ :=
  if h : 0 < r ∧ 0 < s then Classical.choose (normalization_at hN r s h.1 h.2) else 0

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

theorem normP_spec (hN : NormalizationIdentities) {r s : ℕ} (hr : 0 < r) (hs : 0 < s) {b : 𝔽}
    (hb : b ≠ 0)
    (hreg : ∀ Y, Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.denom (normP hN r s Y)) ≠ 0) :
    Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b) (r * s)
        fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN r s Y)) (r * s) ∧
      crossScalar (kacC b) (kacH r s b)
          (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN r s Y)) =
        2 * ∏ pq ∈ genAIndex r s, ((pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹) ∧
      ∀ d : 𝔽, torusForm (kacC b) (kacH r s b) d (r * s)
        (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN r s Y))
        (fun Y => RatFunc.eval (algebraMap ℚ 𝔽) b (normP hN r s Y)) = genP r s b d := by
  have hdef : normP hN r s = Classical.choose (normalization_at hN r s hr hs) := by
    unfold normP
    rw [dif_pos ⟨hr, hs⟩]
  rw [hdef] at hreg ⊢
  obtain ⟨h1, -, h3, h4⟩ :=
    (Classical.choose_spec (normalization_at hN r s hr hs)).2.2.2.2 𝔽 b hb hreg
  exact ⟨h1, h3, h4⟩

/-- Genericity of `b` at level `N`. -/
structure GenericAt (hN : NormalizationIdentities) (N : ℕ) (b : 𝔽) : Prop where
  ne_zero : b ≠ 0
  lin : ∀ m n : ℤ, |m| ≤ 2 * (N : ℤ) → |n| ≤ 2 * (N : ℤ) → (m ≠ 0 ∨ n ≠ 0) →
    (m : 𝔽) * b ^ 2 + (n : 𝔽) ≠ 0
  reg : ∀ a ∈ labels N, ∀ Y,
    Polynomial.eval₂ (algebraMap ℚ 𝔽) b (RatFunc.denom (normP hN a.1 a.2 Y)) ≠ 0

theorem mem_labels {N : ℕ} {a : Label} :
    a ∈ labels N ↔ 1 ≤ a.1 ∧ 1 ≤ a.2 ∧ a.1 * a.2 ≤ N := by
  simp only [labels, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨h1, -⟩, ⟨h2, -⟩⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have h4 : a.1 ≤ a.1 * a.2 := Nat.le_mul_of_pos_right _ h2
    have h5 : a.2 ≤ a.1 * a.2 := Nat.le_mul_of_pos_left _ h1
    exact ⟨⟨⟨h1, by omega⟩, ⟨h2, by omega⟩⟩, h3⟩

theorem mem_labels_le {N : ℕ} {a : Label} (ha : a ∈ labels N) : a.1 ≤ N ∧ a.2 ≤ N := by
  obtain ⟨h1, h2, h3⟩ := mem_labels.1 ha
  have h4 : a.1 ≤ a.1 * a.2 := Nat.le_mul_of_pos_right _ h2
  have h5 : a.2 ≤ a.1 * a.2 := Nat.le_mul_of_pos_left _ h1
  exact ⟨by omega, by omega⟩

variable {hN : NormalizationIdentities} {N : ℕ} {b : 𝔽}

theorem labels_subset {M N : ℕ} (h : M ≤ N) {a : Label} (ha : a ∈ labels M) : a ∈ labels N := by
  rw [mem_labels] at ha ⊢
  omega

theorem GenericAt.mono {M : ℕ} (hgen : GenericAt hN N b) (hMN : M ≤ N) : GenericAt hN M b where
  ne_zero := hgen.ne_zero
  lin := fun m n hm hn h => hgen.lin m n (by omega) (by omega) h
  reg := fun a ha Y => hgen.reg a (labels_subset hMN ha) Y

/-- For generic `b` the Kac weights of level at most `N` are pairwise distinct. -/
theorem GenericAt.kacHL_inj (hgen : GenericAt hN N b) {a g : Label} (ha : a ∈ labels N)
    (hg : g ∈ labels N) (h : kacHL a b = kacHL g b) : a = g := by
  by_contra hne
  obtain ⟨ha1, ha2⟩ := mem_labels_le ha
  obtain ⟨hg1, hg2⟩ := mem_labels_le hg
  obtain ⟨ha3, ha4, -⟩ := mem_labels.1 ha
  obtain ⟨hg3, hg4, -⟩ := mem_labels.1 hg
  have h1 := kacH_sub hgen.ne_zero (a.1 : ℤ) (a.2 : ℤ) (g.1 : ℤ) (g.2 : ℤ)
  have h0 : kacH (a.1 : ℤ) (a.2 : ℤ) b - kacH (g.1 : ℤ) (g.2 : ℤ) b = 0 := sub_eq_zero.2 h
  rw [h0] at h1
  have h4 : (4 * b ^ 2 : 𝔽) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hgen.ne_zero)
  have h2 := (div_eq_zero_iff.1 h1.symm).resolve_right h4
  rcases mul_eq_zero.1 h2 with h3 | h3
  · refine hgen.lin _ _ (by rw [abs_le]; omega) (by rw [abs_le]; omega) ?_ h3
    by_contra hcon
    push Not at hcon
    apply hne
    exact Prod.ext (by omega) (by omega)
  · exact hgen.lin _ _ (by rw [abs_le]; omega) (by rw [abs_le]; omega) (Or.inl (by omega)) h3

/-- For generic `b` no shifted weight `h_a(b) + ℓ_a` is a Kac weight of level at most `N`. -/
theorem GenericAt.shift_ne (hgen : GenericAt hN N b) {a g : Label} (ha : a ∈ labels N)
    (hg : g ∈ labels N) : kacHL a b + (a.lvl : 𝔽) ≠ kacHL g b := by
  intro h
  obtain ⟨ha1, ha2⟩ := mem_labels_le ha
  obtain ⟨hg1, hg2⟩ := mem_labels_le hg
  obtain ⟨ha3, ha4, -⟩ := mem_labels.1 ha
  obtain ⟨hg3, hg4, -⟩ := mem_labels.1 hg
  have h1 := kacH_shift_sub hgen.ne_zero (a.1 : ℤ) (a.2 : ℤ) (g.1 : ℤ) (g.2 : ℤ)
  have h0 : kacH (a.1 : ℤ) (a.2 : ℤ) b + (((a.1 : ℤ) * (a.2 : ℤ) : ℤ) : 𝔽)
      - kacH (g.1 : ℤ) (g.2 : ℤ) b = 0 := by
    have : (((a.1 : ℤ) * (a.2 : ℤ) : ℤ) : 𝔽) = (a.lvl : 𝔽) := by
      unfold Label.lvl
      push_cast
      rfl
    rw [this]
    exact sub_eq_zero.2 h
  rw [h0] at h1
  have h4 : (4 * b ^ 2 : 𝔽) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hgen.ne_zero)
  have h2 := (div_eq_zero_iff.1 h1.symm).resolve_right h4
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact hgen.lin _ _ (by rw [abs_le]; omega) (by rw [abs_le]; omega) (Or.inr (by omega)) h3
  · exact hgen.lin _ _ (by rw [abs_le]; omega) (by rw [abs_le]; omega) (Or.inl (by omega)) h3

/-- For generic `b` the crossing scalars `2 ∏ (p b + q b⁻¹)` do not vanish. -/
theorem GenericAt.cross_ne (hgen : GenericAt hN N b) {a : Label} (ha : a ∈ labels N) :
    (2 * ∏ pq ∈ genAIndex a.1 a.2, ((pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹)) ≠ 0 := by
  obtain ⟨ha1, ha2⟩ := mem_labels_le ha
  refine mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.2 fun pq hpq => ?_)
  have hb := hgen.ne_zero
  have e : (pq.1 : 𝔽) * b + (pq.2 : 𝔽) * b⁻¹ = ((pq.1 : 𝔽) * b ^ 2 + (pq.2 : 𝔽)) / b := by
    field_simp
  rw [e]
  refine div_ne_zero (hgen.lin _ _ ?_ ?_ (mem_genAIndex hpq)) hb
  · simp only [genAIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq
    rw [abs_le]
    omega
  · simp only [genAIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpq
    rw [abs_le]
    omega

end Virasoro
