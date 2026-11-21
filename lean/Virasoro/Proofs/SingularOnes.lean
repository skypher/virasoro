import Virasoro.Proofs.SingularSymbol
import Virasoro.Proofs.SingularDegree
import Virasoro.Proofs.PBWBasis

/-!
# Lemma 5.7 of `paper.tex` at 70bac53, first assertion and the full lemma

The coefficient of `L_{-1}^ℓ|h⟩` in a singular vector of level `ℓ ≥ 1` is nonzero
(paper.tex l.719–738).  Let `K` be the largest length occurring in `w` and `σ` the polynomial
encoding its length-`K` part.  If a variable `x_m`, `m ≥ 2`, occurs in `σ`, take the largest
such `m` and `j = m - 1`: the length-`K` part of `L_j w` is encoded by
`D_j σ = (2m - 1) x_1 ∂σ/∂x_m ≠ 0`, against `L_j w = 0`.  So `σ` is a multiple of `x_1^K`, and
comparing levels gives `K = ℓ`.
-/

namespace Virasoro

open MvPolynomial

theorem sum_eq_length_of_ones : ∀ w : List ℕ, (∀ y ∈ w, y = 1) → w.sum = w.length
  | [], _ => rfl
  | y :: w, h => by
    rw [List.sum_cons, List.length_cons,
      sum_eq_length_of_ones w fun z hz => h z (List.mem_cons_of_mem _ hz),
      h y List.mem_cons_self]
    omega

theorem le_sum_of_mem' : ∀ (w : List ℕ) (y : ℕ), y ∈ w → y ≤ w.sum
  | [], y, h => by simp at h
  | z :: w, y, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := le_sum_of_mem' w y h
      omega

/-- The first assertion of Lemma 5.7: `a_w ≠ 0` for a singular vector `w` of level `ℓ ≥ 1`. -/
theorem sub_singular_ones_coeff : Stmt_sub_singular_ones_coeff := by
  classical
  intro c h ℓ hℓ p hsing hones
  obtain ⟨hne, -, hpos⟩ := hsing
  have hex : ∃ Y, p Y ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hne
    have hp0 : p = 0 := funext hall
    rw [hp0, map_zero]
  -- `K`: the largest length occurring in `w`
  obtain ⟨S, hS⟩ : ∃ S : Finset (Nat.Partition ℓ), ∀ Y, Y ∈ S ↔ p Y ≠ 0 :=
    ⟨Finset.univ.filter fun Y => p Y ≠ 0, fun Y => by simp⟩
  have hSne : S.Nonempty := let ⟨Y, hY⟩ := hex; ⟨Y, (hS Y).2 hY⟩
  obtain ⟨Y₀, hY₀, hmax⟩ := Finset.exists_max_image S (fun Y => Y.word.length) hSne
  obtain ⟨K, hK⟩ : ∃ K, K = Y₀.word.length := ⟨_, rfl⟩
  rw [← hK] at hmax
  -- `m`: the largest variable occurring in the length-`K` part
  obtain ⟨U, hU⟩ : ∃ U : Finset (Nat.Partition ℓ × ℕ), ∀ t, t ∈ U ↔
      (t.1 ∈ S ∧ t.2 ∈ Finset.range (ℓ + 1)) ∧ t.1.word.length = K ∧ t.2 ∈ t.1.word :=
    ⟨(S ×ˢ Finset.range (ℓ + 1)).filter fun t => t.1.word.length = K ∧ t.2 ∈ t.1.word,
      fun t => by rw [Finset.mem_filter, Finset.mem_product]⟩
  have hle : ∀ (Y : Nat.Partition ℓ) (y : ℕ), y ∈ Y.word → y ≤ ℓ := by
    intro Y y hy
    have := le_sum_of_mem' Y.word y hy
    rwa [word_sum_eq] at this
  have hUne : U.Nonempty := by
    have hnil : Y₀.word ≠ [] := by
      intro h0
      have := word_sum_eq Y₀
      rw [h0, List.sum_nil] at this
      omega
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hnil
    refine ⟨(Y₀, y), (hU _).2 ⟨⟨hY₀, ?_⟩, hK.symm, hy⟩⟩
    have := hle Y₀ y hy
    exact Finset.mem_range.2 (by omega)
  obtain ⟨⟨Y₁, m⟩, hU1, hUmax⟩ := Finset.exists_max_image U (fun t => t.2) hUne
  obtain ⟨⟨hY₁S, -⟩, hlen₁, hm₁⟩ := (hU _).1 hU1
  have hpY₁ : p Y₁ ≠ 0 := (hS Y₁).1 hY₁S
  have hbound : ∀ Y : Nat.Partition ℓ, p Y ≠ 0 → Y.word.length = K → ∀ y ∈ Y.word, y ≤ m := by
    intro Y hpY hlen y hy
    have hyl := hle Y y hy
    exact hUmax (Y, y) ((hU _).2 ⟨⟨(hS Y).2 hpY, Finset.mem_range.2 (by omega)⟩, hlen, hy⟩)
  have hm2 : 2 ≤ m := by
    by_contra hlt
    have hall : ∀ y ∈ Y₁.word, y = 1 := fun y hy => by
      have h1 := hbound Y₁ hpY₁ hlen₁ y hy
      have h2 : 0 < y := Verma.posWord_word Y₁ y hy
      omega
    have hsl := sum_eq_length_of_ones _ hall
    rw [word_sum_eq] at hsl
    have hY₁ : Y₁ = onesPartition ℓ := by
      by_contra hne1
      have := word_length_lt Y₁ hne1
      omega
    exact hpY₁ (by rw [hY₁]; exact hones)
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hj : 0 < j := by omega
  have hsupp : ∀ Y : Nat.Partition ℓ, p Y ≠ 0 → Y.word.length = K →
      ∀ i, wordExp Y.word i ≠ 0 → i ≤ j + 1 := by
    intro Y hpY hlen i hi
    rw [wordExp_apply] at hi
    exact hbound Y hpY hlen i (List.count_pos_iff.1 (Nat.pos_of_ne_zero hi))
  -- the image of `L_j w = 0` in the polynomial realization
  choose q hq hlow using fun Y : Nat.Partition ℓ =>
    Verma.polyMap_L_pos_neg (c := c) (h := h) Y.word (Verma.posWord_word Y) j hj
  have hzero := hpos (j : ℤ) (by exact_mod_cast hj)
  have hpoly : ∑ Y : Nat.Partition ℓ,
      p Y • (symD j (monomial (wordExp Y.word) (1 : ℂ)) + q Y) = 0 := by
    have := congrArg (Verma.polyMap c h) hzero
    rw [Verma.pbwCoord_apply, map_sum, map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun Y _ => by rw [map_smul, map_smul, hq]
  -- the monomial `x_1 x^{e₁} / x_{j+1}` of `D_j σ`
  have he₁m : wordExp Y₁.word (j + 1) ≠ 0 := by
    rw [wordExp_apply]
    exact (List.count_pos_iff.2 hm₁).ne'
  have hle₁ : Finsupp.single (j + 1) 1 ≤ wordExp Y₁.word := by
    rw [Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.2 he₁m
  obtain ⟨d, hd0⟩ : ∃ d : ℕ →₀ ℕ,
      d = wordExp Y₁.word - Finsupp.single (j + 1) 1 + Finsupp.single 1 1 := ⟨_, rfl⟩
  have hdd : d.degree = K := by
    have h1 : (wordExp Y₁.word - Finsupp.single (j + 1) 1).degree + 1
        = (wordExp Y₁.word).degree := by
      conv_rhs => rw [← tsub_add_cancel_of_le hle₁, map_add, Finsupp.degree_single]
    rw [hd0, map_add, Finsupp.degree_single, h1, wordExp_degree, hlen₁]
  have hqz : ∀ Y : Nat.Partition ℓ, p Y ≠ 0 → coeff d (q Y) = 0 := by
    intro Y hpY
    by_contra hc
    have h1 := hlow Y d hc
    have h2 := hmax Y ((hS Y).2 hpY)
    omega
  have hterm : ∀ Y : Nat.Partition ℓ, Y ≠ Y₁ →
      coeff d (p Y • (symD j (monomial (wordExp Y.word) (1 : ℂ)) + q Y)) = 0 := by
    intro Y hYne
    by_cases hpY : p Y = 0
    · rw [hpY, zero_smul, coeff_zero]
    have hlenY : Y.word.length ≤ K := hmax Y ((hS Y).2 hpY)
    rw [coeff_smul, coeff_add, hqz Y hpY, add_zero, smul_eq_mul]
    rcases hlenY.lt_or_eq with hlt | heq
    · rw [(isHomogeneous_symD_monomial j (wordExp Y.word) (1 : ℂ)).coeff_eq_zero
        (by rw [hdd, wordExp_degree]; omega), mul_zero]
    · rw [symD_monomial_top j _ (hsupp Y hpY heq), coeff_monomial]
      split_ifs with hd
      · by_cases hem : wordExp Y.word (j + 1) = 0
        · rw [hem]
          simp
        · exfalso
          apply hYne
          have hleY : Finsupp.single (j + 1) 1 ≤ wordExp Y.word := by
            rw [Finsupp.single_le_iff]
            exact Nat.one_le_iff_ne_zero.2 hem
          rw [hd0] at hd
          have h1 : wordExp Y.word - Finsupp.single (j + 1) 1
              = wordExp Y₁.word - Finsupp.single (j + 1) 1 := add_right_cancel hd
          have h2 : wordExp Y.word = wordExp Y₁.word := by
            rw [← tsub_add_cancel_of_le hleY, h1, tsub_add_cancel_of_le hle₁]
          have h3 := Verma.sigma_eq_of_word_perm (Y := ⟨ℓ, Y⟩) (Y' := ⟨ℓ, Y₁⟩) (wordExp_perm h2)
          simpa using h3
      · rw [mul_zero]
  have hcoeff := congrArg (coeff d) hpoly
  rw [coeff_sum, coeff_zero,
    Finset.sum_eq_single Y₁ (fun Y _ hY => hterm Y hY)
      (fun hn => absurd (Finset.mem_univ _) hn),
    coeff_smul, coeff_add, hqz Y₁ hpY₁, add_zero,
    symD_monomial_top j _ (hsupp Y₁ hpY₁ hlen₁), coeff_monomial, if_pos hd0.symm,
    smul_eq_mul] at hcoeff
  have h2j : ((2 * j + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h3 : ((wordExp Y₁.word (j + 1) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 he₁m
  exact mul_ne_zero hpY₁ (mul_ne_zero h3 h2j) hcoeff

example : Stmt_sub_singular_ones_coeff := sub_singular_ones_coeff

/-- Paper label: lem:singular-degree -/
theorem lem_singular_degree : Stmt_lem_singular_degree :=
  lem_singular_degree_of_sub sub_singular_ones_coeff

example : Stmt_lem_singular_degree := lem_singular_degree

end Virasoro
