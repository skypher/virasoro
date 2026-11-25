import Virasoro.Statements.AppA20261125
import Virasoro.Proofs.Sec6H13Reg
import Virasoro.Proofs.Sec6H13Comb
import Mathlib.Data.ZMod.Basic

/-!
# Lemma A.1 of `paper.tex` (`lem:mode-count`, l.2915–2927)

With the rescaled modes `L̃_k = t L_k` (`k ≠ 0`), `L̃_0 = t² L_0`, the matrix elements
`G̃ = t^{ℓ(Z)+ℓ(Z')} G_M` and `ρ̃ = t^{ℓ(Z)+ℓ(Z')} ρ_M` are computed by the rescaled commutation
procedure (`gramT`, `torusWordT`, `gramT_eq`, `torusWordT_eq`), which involves only `t`,
`c̃ = t c(b) = 6 + 13t + 6t²`, `Y = t²Δ` and `d̃ = t d = −2 + tζ`.  Every coefficient it produces
is an integer, `(k³ − k)/12 ∈ ½ℤ` or one of these, so `G̃` and `ρ̃` have coefficients in `ℤ[1/2]`
(`gramT_mem`, `torusWordT_mem`).  At `t = 0` the procedure only contracts opposite modes, which
gives `G̃(0,Y) = diag(K_Z Y^{ℓ(Z)})` (`gramT_zero`, `topNat_word_eq_appKZ`); and `d̃ = −2` there,
so `ρ̃(0,Y;ζ)` does not depend on `ζ`.
-/

namespace Virasoro

/-! ### `ℤ[1/2]` -/

/-- `ℤ[1/2] ⊂ ℚ`. -/
def halfIntSub : Subring ℚ where
  carrier := {q | ∃ (z : ℤ) (n : ℕ), q = z / 2 ^ n}
  mul_mem' := by
    rintro _ _ ⟨a, m, rfl⟩ ⟨b, n, rfl⟩
    exact ⟨a * b, m + n, by rw [pow_add]; push_cast; ring⟩
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, m, rfl⟩ ⟨b, n, rfl⟩
    refine ⟨a * 2 ^ n + 2 ^ m * b, m + n, ?_⟩
    rw [div_add_div _ _ (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ two_ne_zero), pow_add]
    push_cast
    ring
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨a, m, rfl⟩
    exact ⟨-a, m, by push_cast; ring⟩

/-- The polynomials with coefficients in `ℤ[1/2]`. -/
def halfIntPoly (σ : Type*) : Subring (MvPolynomial σ ℚ) where
  carrier := {p | ∀ e, p.coeff e ∈ halfIntSub}
  mul_mem' := by
    intro p q hp hq e
    classical
    rw [MvPolynomial.coeff_mul]
    exact Subring.sum_mem _ fun x _ => Subring.mul_mem _ (hp _) (hq _)
  one_mem' := by
    intro e
    classical
    rw [MvPolynomial.coeff_one]
    split_ifs
    · exact halfIntSub.one_mem
    · exact halfIntSub.zero_mem
  add_mem' := by
    intro p q hp hq e
    rw [MvPolynomial.coeff_add]
    exact halfIntSub.add_mem (hp e) (hq e)
  zero_mem' := by
    intro e
    rw [MvPolynomial.coeff_zero]
    exact halfIntSub.zero_mem
  neg_mem' := by
    intro p hp e
    rw [MvPolynomial.coeff_neg]
    exact halfIntSub.neg_mem (hp e)

theorem halfIntCoeffs_of_mem {σ : Type*} {p : MvPolynomial σ ℚ} (h : p ∈ halfIntPoly σ) :
    HalfIntCoeffs p := fun e => h e

theorem C_mem_halfIntPoly {σ : Type*} {q : ℚ} (hq : q ∈ halfIntSub) :
    MvPolynomial.C q ∈ halfIntPoly σ := by
  intro e
  classical
  rw [MvPolynomial.coeff_C]
  split_ifs
  · exact hq
  · exact halfIntSub.zero_mem

theorem X_mem_halfIntPoly {σ : Type*} (i : σ) : MvPolynomial.X i ∈ halfIntPoly σ := by
  intro e
  classical
  rw [MvPolynomial.X, MvPolynomial.coeff_monomial]
  split_ifs
  · exact halfIntSub.one_mem
  · exact halfIntSub.zero_mem

/-- `(k³ − k)/12 ∈ ℤ[1/2]`, since `6 ∣ k³ − k`. -/
theorem twelfth_mem (k : ℤ) : (((k ^ 3 - k : ℤ) : ℚ) / 12) ∈ halfIntSub := by
  have h6 : ((6 : ℕ) : ℤ) ∣ k ^ 3 - k := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    generalize (k : ZMod 6) = a
    revert a
    decide
  obtain ⟨m, hm⟩ := h6
  exact ⟨m, 1, by rw [hm]; push_cast; ring⟩

theorem twelfth_mem_halfIntPoly {σ : Type*} (k : ℤ) :
    algebraMap ℚ (MvPolynomial σ ℚ) (((k ^ 3 - k : ℤ) : ℚ) / 12) ∈ halfIntPoly σ := by
  rw [MvPolynomial.algebraMap_eq]
  exact C_mem_halfIntPoly (twelfth_mem k)

/-- If the coefficients of `t · p` lie in `ℤ[1/2]`, so do those of `p`. -/
theorem mem_halfIntPoly_of_X_mul {σ : Type*} {p : MvPolynomial σ ℚ} (i : σ)
    (h : MvPolynomial.X i * p ∈ halfIntPoly σ) : p ∈ halfIntPoly σ := by
  intro e
  have h1 := h (e + Finsupp.single i 1)
  rwa [mul_comm, MvPolynomial.coeff_mul_X] at h1

/-! ### The rescaled procedure keeps coefficients in a subring -/

section Mem

variable {R : Type*} [CommRing R] [Algebra ℚ R] (T : Subring R)

theorem wsum_mem_sub {s : St R} {φ : List ℕ → R} (hs : ∀ t ∈ s, t.2 ∈ T)
    (hφ : ∀ u, φ u ∈ T) : wsum s φ ∈ T := by
  unfold wsum
  refine list_sum_mem fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact T.mul_mem (hs t ht) (hφ _)

variable {T} {τ ct Yv : R}

theorem dAct_mem (hτ : τ ∈ T) (hc : ct ∈ T) (hY : Yv ∈ T)
    (h12 : ∀ k : ℤ, algebraMap ℚ R (((k ^ 3 - k : ℤ) : ℚ) / 12) ∈ T) :
    ∀ (w : List ℕ) (k : ℤ), ∀ t ∈ dAct τ ct Yv k w, t.2 ∈ T
  | [], k => by
    unfold dAct
    split_ifs
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact T.one_mem
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact hY
    · intro t ht
      simp at ht
  | y :: w, k => by
    unfold dAct
    split_ifs with h1 h2 h3
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact T.one_mem
    · intro t ht
      rw [List.mem_singleton] at ht
      subst ht
      exact T.add_mem hY (T.mul_mem (T.pow_mem hτ 2) (natCast_mem T _))
    · intro t ht
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at ht
      rcases ht with (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) | rfl
      · exact dAct_mem hτ hc hY h12 w k u hu
      · exact T.mul_mem (T.mul_mem (intCast_mem T _) T.one_mem) (dAct_mem hτ hc hY h12 w (k - y) u hu)
      · exact T.mul_mem hτ (T.mul_mem (h12 k) hc)
    · intro t ht
      simp only [List.mem_append, List.mem_map, List.not_mem_nil, or_false] at ht
      rcases ht with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
      · exact dAct_mem hτ hc hY h12 w k u hu
      · exact T.mul_mem (T.mul_mem (intCast_mem T _) hτ) (dAct_mem hτ hc hY h12 w (k - y) u hu)

theorem gramT_mem (hτ : τ ∈ T) (hc : ct ∈ T) (hY : Yv ∈ T)
    (h12 : ∀ k : ℤ, algebraMap ℚ R (((k ^ 3 - k : ℤ) : ℚ) / 12) ∈ T) :
    ∀ (Y w : List ℕ), gramT τ ct Yv Y w ∈ T
  | [], w => by
    simp only [gramT]
    split_ifs
    · exact T.one_mem
    · exact T.zero_mem
  | y :: Y, w => by
    simp only [gramT]
    exact wsum_mem_sub T (dAct_mem hτ hc hY h12 w y) (gramT_mem hτ hc hY h12 Y)

theorem phiT_mem (hτ : τ ∈ T) {dt : R} (hd : dt ∈ T) : ∀ w : List ℕ, phiT τ dt w ∈ T
  | [] => by
    simp only [phiT]
    exact T.one_mem
  | m :: w => by
    simp only [phiT]
    exact T.mul_mem (T.add_mem (T.mul_mem hτ (natCast_mem T _)) (T.mul_mem (natCast_mem T _) hd))
      (phiT_mem hτ hd w)

theorem torusWordT_mem (hτ : τ ∈ T) (hc : ct ∈ T) (hY : Yv ∈ T) {dt : R} (hd : dt ∈ T)
    (h12 : ∀ k : ℤ, algebraMap ℚ R (((k ^ 3 - k : ℤ) : ℚ) / 12) ∈ T) :
    ∀ (Y w : List ℕ), torusWordT τ ct Yv dt Y w ∈ T
  | [], w => by
    simp only [torusWordT]
    exact phiT_mem hτ hd w
  | y :: Y, w => by
    simp only [torusWordT]
    exact T.add_mem (wsum_mem_sub T (dAct_mem hτ hc hY h12 w y) (torusWordT_mem hτ hc hY hd h12 Y))
      (T.mul_mem (T.add_mem (T.mul_mem hτ (T.sub_mem (natCast_mem T _) (natCast_mem T _)))
        (T.mul_mem (natCast_mem T _) hd)) (torusWordT_mem hτ hc hY hd h12 Y w))

end Mem

/-! ### `t = 0` -/

/-- `t ∣ p(t,Y) − p(0,Y)`. -/
theorem X0_dvd_sub_aeval (p : MvPolynomial (Fin 2) ℚ) :
    MvPolynomial.X 0 ∣ p - MvPolynomial.aeval
      (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p n hp =>
    rw [map_mul, MvPolynomial.aeval_X]
    fin_cases n
    · simpa using dvd_mul_left (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) p
    · have e : p * MvPolynomial.X 1 - MvPolynomial.aeval
            (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) p *
            (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) 1 =
          (p - MvPolynomial.aeval
            (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) p) * MvPolynomial.X 1 := by
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
        ring
      simpa using e ▸ Dvd.dvd.mul_right hp _

theorem word_length_eq_card {M : ℕ} (Z : Nat.Partition M) : Z.word.length = Z.parts.card := by
  rw [Nat.Partition.word, Multiset.length_sort]

/-- `K_Z = topNat Z Z = ∏_n m_n! (2n)^{m_n}`. -/
theorem topNat_word_eq_appKZ {M : ℕ} (Z : Nat.Partition M) : topNat Z.word Z.word = appKZ Z := by
  classical
  rw [H13C.topNat_perm Z.word Z.word (List.Perm.refl _)]
  have hw : ((Z.word : List ℕ) : Multiset ℕ) = Z.parts := by
    rw [Nat.Partition.word, Multiset.sort_eq]
  have hp : Z.word.prod = Z.parts.prod := by rw [← Multiset.prod_coe, hw]
  rw [hw, word_length_eq_card, hp, appKZ, H13C.facs, Finset.prod_mul_distrib]
  have h1 : ∏ n ∈ Z.parts.toFinset, (2 * n) ^ Z.parts.count n =
      2 ^ Z.parts.card * Z.parts.prod := by
    rw [Finset.prod_congr rfl fun n _ => mul_pow 2 n (Z.parts.count n), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Multiset.toFinset_sum_count_eq, ← Finset.prod_multiset_count]
  rw [h1]
  ring

/-! ### The matrices -/

/-- `c̃ = t c(b) = 6 + 13t + 6t²`. -/
noncomputable def ct2 : MvPolynomial (Fin 2) ℚ :=
  6 + 13 * MvPolynomial.X 0 + 6 * MvPolynomial.X 0 ^ 2

/-- `c̃` in `ℚ[t,Y,ζ]`. -/
noncomputable def ct3 : MvPolynomial (Fin 3) ℚ :=
  6 + 13 * MvPolynomial.X 0 + 6 * MvPolynomial.X 0 ^ 2

/-- `d̃ = t d = −2 + tζ`. -/
noncomputable def dt3 : MvPolynomial (Fin 3) ℚ := -2 + MvPolynomial.X 0 * MvPolynomial.X 2

/-- `G̃ ∈ Mat(ℚ[t,Y])`. -/
noncomputable def Gt2 (M : ℕ) (Z Z' : Nat.Partition M) : MvPolynomial (Fin 2) ℚ :=
  gramT (MvPolynomial.X 0) ct2 (MvPolynomial.X 1) Z.word Z'.word

/-- `ρ̃ ∈ Mat(ℚ[t,Y,ζ])`. -/
noncomputable def rhot3 (M : ℕ) (Z Z' : Nat.Partition M) : MvPolynomial (Fin 3) ℚ :=
  torusWordT (MvPolynomial.X 0) ct3 (MvPolynomial.X 1) dt3 Z.word Z'.word

/-- `D₀(Y) = diag(K_Z Y^{ℓ(Z)})`. -/
noncomputable def D0t {M : ℕ} (Z Z' : Nat.Partition M) : MvPolynomial (Fin 2) ℚ :=
  if Z = Z' then MvPolynomial.C (appKZ Z : ℚ) * MvPolynomial.X 1 ^ Z.parts.card else 0

theorem ct2_mem : ct2 ∈ halfIntPoly (Fin 2) := by
  unfold ct2
  have h6 : (6 : MvPolynomial (Fin 2) ℚ) ∈ halfIntPoly (Fin 2) := by
    simpa using natCast_mem (halfIntPoly (Fin 2)) 6
  have h13 : (13 : MvPolynomial (Fin 2) ℚ) ∈ halfIntPoly (Fin 2) := by
    simpa using natCast_mem (halfIntPoly (Fin 2)) 13
  exact Subring.add_mem _ (Subring.add_mem _ h6 (Subring.mul_mem _ h13 (X_mem_halfIntPoly 0)))
    (Subring.mul_mem _ h6 (Subring.pow_mem _ (X_mem_halfIntPoly 0) 2))

theorem ct3_mem : ct3 ∈ halfIntPoly (Fin 3) := by
  unfold ct3
  have h6 : (6 : MvPolynomial (Fin 3) ℚ) ∈ halfIntPoly (Fin 3) := by
    simpa using natCast_mem (halfIntPoly (Fin 3)) 6
  have h13 : (13 : MvPolynomial (Fin 3) ℚ) ∈ halfIntPoly (Fin 3) := by
    simpa using natCast_mem (halfIntPoly (Fin 3)) 13
  exact Subring.add_mem _ (Subring.add_mem _ h6 (Subring.mul_mem _ h13 (X_mem_halfIntPoly 0)))
    (Subring.mul_mem _ h6 (Subring.pow_mem _ (X_mem_halfIntPoly 0) 2))

theorem dt3_mem : dt3 ∈ halfIntPoly (Fin 3) := by
  unfold dt3
  have h2 : (2 : MvPolynomial (Fin 3) ℚ) ∈ halfIntPoly (Fin 3) := by
    simpa using natCast_mem (halfIntPoly (Fin 3)) 2
  exact Subring.add_mem _ (Subring.neg_mem _ h2)
    (Subring.mul_mem _ (X_mem_halfIntPoly 0) (X_mem_halfIntPoly 2))

theorem Gt2_mem (M : ℕ) (Z Z' : Nat.Partition M) : Gt2 M Z Z' ∈ halfIntPoly (Fin 2) :=
  gramT_mem (X_mem_halfIntPoly 0) ct2_mem (X_mem_halfIntPoly 1) twelfth_mem_halfIntPoly _ _

theorem rhot3_mem (M : ℕ) (Z Z' : Nat.Partition M) : rhot3 M Z Z' ∈ halfIntPoly (Fin 3) :=
  torusWordT_mem (X_mem_halfIntPoly 0) ct3_mem (X_mem_halfIntPoly 1) dt3_mem
    twelfth_mem_halfIntPoly _ _

theorem D0t_mem {M : ℕ} (Z Z' : Nat.Partition M) : D0t Z Z' ∈ halfIntPoly (Fin 2) := by
  unfold D0t
  split_ifs
  · refine Subring.mul_mem _ ?_ (Subring.pow_mem _ (X_mem_halfIntPoly 1) _)
    rw [map_natCast]
    exact natCast_mem _ _
  · exact Subring.zero_mem _

/-- `G̃(0,Y) = D₀(Y)`. -/
theorem aeval0_Gt2 (M : ℕ) (Z Z' : Nat.Partition M) :
    MvPolynomial.aeval (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) (Gt2 M Z Z') =
      D0t Z Z' := by
  let π : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ :=
    (MvPolynomial.aeval (R := ℚ) (σ := Fin 2)
      (![0, MvPolynomial.X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)).toRingHom
  have hπ0 : π (MvPolynomial.X 0) = 0 := by simp [π]
  have hπ1 : π (MvPolynomial.X 1) = MvPolynomial.X 1 := by simp [π]
  change π (Gt2 M Z Z') = D0t Z Z'
  rw [Gt2, ← gramT_map π, hπ0, hπ1, gramT_zero _ _ _ _ (word_pos Z), D0t]
  by_cases hZZ : Z = Z'
  · subst hZZ
    rw [if_pos rfl, if_pos rfl, topNat_word_eq_appKZ, word_length_eq_card, map_natCast]
  · rw [if_neg hZZ]
    split_ifs with hlen
    · rw [topNat_eq_zero_of_not_perm hlen.symm fun hperm => hZZ (word_injective hperm).symm,
        Nat.cast_zero, zero_mul]
    · rfl

/-! ### The identities in `ℚ(t,Y,ζ)` -/

theorem evtYz_X_ne_zero (i : Fin 3) : evtYz (MvPolynomial.X i) ≠ 0 := by
  rw [Ne, evtYz, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
  exact MvPolynomial.X_ne_zero i

theorem evtYz_ct3 : evtYz ct3 = evtYz (MvPolynomial.X 0) * cT (evtYz (MvPolynomial.X 0)) := by
  have ht := evtYz_X_ne_zero 0
  simp only [ct3, map_add, map_mul, map_pow, map_ofNat, cT]
  field_simp
  ring

theorem evtYz_dt3 : evtYz dt3 =
    evtYz (MvPolynomial.X 0) * (-2 / evtYz (MvPolynomial.X 0) + evtYz (MvPolynomial.X 2)) := by
  have ht := evtYz_X_ne_zero 0
  simp only [dt3, map_add, map_mul, map_neg, map_ofNat]
  field_simp

theorem evtYz_Y : evtYz (MvPolynomial.X 0) ^ 2 *
    (evtYz (MvPolynomial.X 1) / evtYz (MvPolynomial.X 0) ^ 2) = evtYz (MvPolynomial.X 1) := by
  have ht := evtYz_X_ne_zero 0
  field_simp

theorem rename_ct2 : MvPolynomial.rename Fin.castSucc ct2 = ct3 := by
  simp only [ct2, ct3, map_add, map_mul, map_pow, MvPolynomial.rename_X]
  rw [map_ofNat (MvPolynomial.rename Fin.castSucc) 6, map_ofNat (MvPolynomial.rename Fin.castSucc) 13]
  rfl

/-- `G̃ = t^{ℓ(Z)+ℓ(Z')} G_M(c(b), Y/t²)` in `ℚ(t,Y,ζ)`. -/
theorem evtYz_Gt2 (M : ℕ) (Z Z' : Nat.Partition M) :
    evtYz (MvPolynomial.rename Fin.castSucc (Gt2 M Z Z')) =
      evtYz (MvPolynomial.X 0) ^ (Z.parts.card + Z'.parts.card) *
        gram (cT (evtYz (MvPolynomial.X 0)))
          (evtYz (MvPolynomial.X 1) / evtYz (MvPolynomial.X 0) ^ 2) M Z Z' := by
  let f : MvPolynomial (Fin 2) ℚ →+* KtYz :=
    evtYz.comp (MvPolynomial.rename Fin.castSucc : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] _).toRingHom
  have hf0 : f (MvPolynomial.X 0) = evtYz (MvPolynomial.X 0) := by
    simp [f, MvPolynomial.rename_X]
  have hf1 : f (MvPolynomial.X 1) = evtYz (MvPolynomial.X 1) := by
    simp [f, MvPolynomial.rename_X]
  have hfc : f ct2 = evtYz ct3 := by
    change evtYz (MvPolynomial.rename Fin.castSucc ct2) = evtYz ct3
    rw [rename_ct2]
  have he := gramT_eq (evtYz (MvPolynomial.X 0)) (cT (evtYz (MvPolynomial.X 0)))
    (evtYz (MvPolynomial.X 1) / evtYz (MvPolynomial.X 0) ^ 2) Z.word Z'.word (word_pos Z)
  rw [evtYz_Y] at he
  change f (Gt2 M Z Z') = _
  rw [Gt2, ← gramT_map f, hf0, hf1, hfc, evtYz_ct3, he, word_length_eq_card,
    word_length_eq_card]
  rfl

/-- `ρ̃ = t^{ℓ(Z)+ℓ(Z')} ρ_M(c(b), Y/t², −2/t + ζ)` in `ℚ(t,Y,ζ)`. -/
theorem evtYz_rhot3 (M : ℕ) (Z Z' : Nat.Partition M) :
    evtYz (rhot3 M Z Z') =
      evtYz (MvPolynomial.X 0) ^ (Z.parts.card + Z'.parts.card) *
        torus (cT (evtYz (MvPolynomial.X 0)))
          (evtYz (MvPolynomial.X 1) / evtYz (MvPolynomial.X 0) ^ 2)
          (-2 / evtYz (MvPolynomial.X 0) + evtYz (MvPolynomial.X 2)) M Z Z' := by
  have he := torusWordT_eq (evtYz (MvPolynomial.X 0)) (cT (evtYz (MvPolynomial.X 0)))
    (evtYz (MvPolynomial.X 1) / evtYz (MvPolynomial.X 0) ^ 2)
    (-2 / evtYz (MvPolynomial.X 0) + evtYz (MvPolynomial.X 2)) Z.word Z'.word (word_pos Z)
  rw [evtYz_Y] at he
  rw [rhot3, ← torusWordT_map evtYz, evtYz_ct3, evtYz_dt3, he, word_length_eq_card,
    word_length_eq_card]
  rfl

/-- `ρ̃(0,Y;ζ) = ρ̃(0,Y;0)`. -/
theorem rhot3_t0 (M : ℕ) (Z Z' : Nat.Partition M) :
    MvPolynomial.aeval (![0, MvPolynomial.X 1, MvPolynomial.X 2] :
        Fin 3 → MvPolynomial (Fin 3) ℚ) (rhot3 M Z Z') =
      MvPolynomial.aeval (![0, MvPolynomial.X 1, 0] : Fin 3 → MvPolynomial (Fin 3) ℚ)
        (rhot3 M Z Z') := by
  let f : MvPolynomial (Fin 3) ℚ →+* MvPolynomial (Fin 3) ℚ :=
    (MvPolynomial.aeval (R := ℚ) (σ := Fin 3)
      (![0, MvPolynomial.X 1, MvPolynomial.X 2] : Fin 3 → MvPolynomial (Fin 3) ℚ)).toRingHom
  let g : MvPolynomial (Fin 3) ℚ →+* MvPolynomial (Fin 3) ℚ :=
    (MvPolynomial.aeval (R := ℚ) (σ := Fin 3)
      (![0, MvPolynomial.X 1, 0] : Fin 3 → MvPolynomial (Fin 3) ℚ)).toRingHom
  have h0 : f (MvPolynomial.X 0) = g (MvPolynomial.X 0) := by simp [f, g]
  have h1 : f (MvPolynomial.X 1) = g (MvPolynomial.X 1) := by simp [f, g]
  have hc : f ct3 = g ct3 := by
    simp only [ct3, map_add, map_mul, map_pow, h0]
    rw [map_ofNat f 6, map_ofNat g 6, map_ofNat f 13, map_ofNat g 13]
  have hd : f dt3 = g dt3 := by
    simp only [dt3, map_add, map_mul, map_neg]
    rw [map_ofNat f 2, map_ofNat g 2]
    simp [f, g]
  change f (rhot3 M Z Z') = g (rhot3 M Z Z')
  rw [rhot3, ← torusWordT_map f, ← torusWordT_map g, h0, h1, hc, hd]

/-- Lemma A.1 (paper.tex l.2915–2927).
Paper label: lem:mode-count -/
theorem lem_mode_count : Stmt_lem_mode_count := by
  intro M
  have hdiv : ∀ Z Z' : Nat.Partition M, MvPolynomial.X 0 ∣ Gt2 M Z Z' - D0t Z Z' := by
    intro Z Z'
    have h := X0_dvd_sub_aeval (Gt2 M Z Z')
    rwa [aeval0_Gt2] at h
  choose G1 hG1 using hdiv
  refine ⟨G1, rhot3 M, ?_⟩
  intro t Y ζ
  refine ⟨fun Z Z' => ?_, fun Z Z' => halfIntCoeffs_of_mem (rhot3_mem M Z Z'), fun Z Z' => ?_,
    fun Z Z' => evtYz_rhot3 M Z Z', fun Z Z' => rhot3_t0 M Z Z'⟩
  · refine halfIntCoeffs_of_mem (mem_halfIntPoly_of_X_mul 0 ?_)
    rw [← hG1]
    exact Subring.sub_mem _ (Gt2_mem M Z Z') (D0t_mem Z Z')
  · have e : (if Z = Z' then MvPolynomial.C (appKZ Z : ℚ) * MvPolynomial.X 1 ^ Z.parts.card
        else 0) + MvPolynomial.X 0 * G1 Z Z' = Gt2 M Z Z' := by
      rw [← hG1 Z Z']
      unfold D0t
      ring
    rw [e]
    exact evtYz_Gt2 M Z Z'

end Virasoro
