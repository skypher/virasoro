import Virasoro.Proofs.Sec6H13Scale
import Virasoro.Proofs.Sec6H13Poles
import Virasoro.Proofs.GramDet
import Virasoro.Proofs.Sec4Core2

/-!
# Proposition 6.8(i) of `paper.tex` at 70bac53: regularity at `t = 0` (l.1232–1252)

`G̃(t,Y) = D₀(Y) + t G₁(t,Y)` with `D₀(Y) = diag(K_λ Y^{ℓ(λ)})` (l.1239–1244): at `t = 0` only the
direct opposite-mode contractions survive.  `ρ̃` is polynomial in `(t,Y)` (l.1245–1248).  Hence
`F_M = Tr(G̃⁻¹ ρ̃)`, `H_M` and `P_M^{(ν)}` are quotients of polynomials in `(t,Y)` whose
denominator does not vanish at `t = 0` (l.1248–1252).

The ring `ℚ[t][Y]` is `PS`; `psi` sends `t ↦ t`, `Y ↦ t² Δ` into `ℚ(t)(Δ)`.
-/

namespace Virasoro

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-! ### The value at `τ = 0` -/

/-- At `τ = 0` the rescaled mode `L̃_k` (`k > 0`) only contracts with an opposite mode:
`L̃_k w = ∑ 2k Y · (w with one letter k deleted)`. -/
theorem dAct_tau_zero (ct Yv : R) : ∀ (w : List ℕ) (k : ℕ), 0 < k → ∀ φ : List ℕ → R,
    wsum (dAct 0 ct Yv (k : ℤ) w) φ = ((delOne k w).map fun u => 2 * (k : R) * Yv * φ u).sum
  | [], k, hk, φ => by
    have h1 : ¬ ((k : ℤ) < 0) := by omega
    have h2 : ¬ ((k : ℤ) = 0) := by omega
    have h0 : k ≠ 0 := hk.ne'
    simp [dAct, delOne, h1, h0, wsum_nil]
  | y :: w, k, hk, φ => by
    have h1 : ¬ ((k : ℤ) < 0) := by omega
    have h2 : ¬ ((k : ℤ) = 0) := by omega
    have ih := dAct_tau_zero ct Yv w k hk (fun u => φ (y :: u))
    unfold dAct
    rw [if_neg h1, if_neg h2]
    by_cases h3 : (k : ℤ) = y
    · have hyk : y = k := by omega
      have h0 : (k : ℤ) - (y : ℤ) = 0 := by omega
      rw [if_pos h3, if_pos h3, wsum_append, wsum_append, wsum_map_cons, wsum_map_mul,
        wsum_singleton, ih, h0, dAct_zero_mode]
      simp only [delOne, if_pos hyk, List.singleton_append, List.map_cons, List.sum_cons,
        List.map_map, Function.comp_def]
      subst hyk
      push_cast
      ring
    · have hyk : ¬ (y = k) := by omega
      rw [if_neg h3, if_neg h3, wsum_append, wsum_append, wsum_map_cons, wsum_map_mul, wsum_nil,
        ih]
      simp only [delOne, if_neg hyk, List.nil_append, List.map_map, Function.comp_def]
      ring

theorem delOne_length {k : ℕ} {w u : List ℕ} (h : u ∈ delOne k w) : w.length = u.length + 1 := by
  have := (delOne_perm h).length_eq
  simpa using this

/-- `G̃(0,Y)`: the rescaled matrix element at `τ = 0` is the weighted matching count times
`Y^{ℓ}` for words of equal length, and vanishes otherwise (paper.tex l.1239–1244). -/
theorem gramT_zero (ct Yv : R) : ∀ (Y w : List ℕ), (∀ y ∈ Y, 0 < y) →
    gramT 0 ct Yv Y w = if w.length = Y.length then (topNat Y w : R) * Yv ^ Y.length else 0
  | [], w, _ => by
    unfold gramT
    cases w <;> simp [topNat]
  | y :: Y, w, hY => by
    have hy : 0 < y := hY y (List.mem_cons_self ..)
    have ih : gramT 0 ct Yv Y =
        fun u => if u.length = Y.length then (topNat Y u : R) * Yv ^ Y.length else 0 := by
      funext u
      exact gramT_zero ct Yv Y u fun z hz => hY z (List.mem_cons_of_mem _ hz)
    unfold gramT
    rw [ih, dAct_tau_zero ct Yv w y hy]
    by_cases hl : w.length = (y :: Y).length
    · rw [if_pos hl]
      have e : ((delOne y w).map fun u => 2 * (y : R) * Yv *
            (if u.length = Y.length then (topNat Y u : R) * Yv ^ Y.length else 0)) =
          (delOne y w).map fun u => ((2 * y * topNat Y u : ℕ) : R) * Yv ^ (y :: Y).length := by
        apply List.map_congr_left
        intro u hu
        have := delOne_length hu
        rw [List.length_cons] at hl
        rw [if_pos (by omega), List.length_cons]
        push_cast
        ring
      rw [e, List.sum_map_mul_right, topNat, Nat.cast_list_sum, List.map_map]
      rfl
    · rw [if_neg hl]
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
      have := delOne_length hu
      rw [List.length_cons] at hl
      rw [if_neg (by omega), mul_zero]

/-! ### The rings `ℚ[t][Y]` and `ℚ(t)(Δ)` -/

/-- `ℚ[t][Y]`: the inner variable is `t`, the outer variable is `Y`. -/
abbrev PS : Type := Polynomial (Polynomial ℚ)

/-- `t ∈ ℚ[t][Y]`. -/
noncomputable def tS : PS := C X

/-- `c̃ = t c(b) = 6 + 13t + 6t²`. -/
noncomputable def cS : PS := C (6 + 13 * X + 6 * X ^ 2)

/-- `d̃_ν = t d_ν`: `-2 - t` for `d₁ = h_{1,3}` and `-2 + 2t` for `d₂ = h_{1,-3}`. -/
noncomputable def dS (ν : Fin 2) : PS := C (if ν = 0 then -2 - X else -2 + 2 * X)

/-- `d₁ = h_{1,3}(b) = -1 - 2/t` (`ν = 0`) and `d₂ = h_{1,-3}(b) = 2 - 2/t` (`ν = 1`). -/
noncomputable def d13 (ν : Fin 2) : RatFunc ℚ :=
  if ν = 0 then -1 - 2 / (RatFunc.X : RatFunc ℚ) else 2 - 2 / (RatFunc.X : RatFunc ℚ)

/-- `ℚ[t][Y] → ℚ(t)[Δ]`, `t ↦ t`, `Y ↦ t² Δ`. -/
noncomputable def psi1 : PS →+* (RatFunc ℚ)[X] :=
  eval₂RingHom ((C : RatFunc ℚ →+* (RatFunc ℚ)[X]).comp (algebraMap ℚ[X] (RatFunc ℚ)))
    (C (RatFunc.X : RatFunc ℚ) ^ 2 * X)

/-- `ℚ[t][Y] → ℚ(t)(Δ)`, `t ↦ t`, `Y ↦ t² Δ`. -/
noncomputable def psi : PS →+* RatFunc (RatFunc ℚ) :=
  (algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))).comp psi1

theorem psi1_C (p : ℚ[X]) : psi1 (C p) = C (algebraMap ℚ[X] (RatFunc ℚ) p) := by
  simp [psi1]

theorem psi1_X : psi1 X = C (RatFunc.X : RatFunc ℚ) ^ 2 * X := by
  simp [psi1]

theorem psi1_tS : psi1 tS = C (RatFunc.X : RatFunc ℚ) := by
  rw [tS, psi1_C, RatFunc.algebraMap_X]

theorem psi1_cS : psi1 cS = C (RatFunc.X : RatFunc ℚ) * C (cT (RatFunc.X : RatFunc ℚ)) := by
  rw [cS, psi1_C, ← C_mul]
  congr 1
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  simp only [map_add, map_mul, map_pow, RatFunc.algebraMap_X, map_ofNat, cT]
  field_simp
  ring

theorem psi1_dS (ν : Fin 2) : psi1 (dS ν) = C (RatFunc.X : RatFunc ℚ) * C (d13 ν) := by
  rw [dS, psi1_C, ← C_mul]
  congr 1
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  unfold d13
  split_ifs
  · simp only [map_sub, map_neg, map_ofNat, RatFunc.algebraMap_X]
    field_simp
    ring
  · simp only [map_add, map_mul, map_neg, map_ofNat, RatFunc.algebraMap_X]
    field_simp
    ring

theorem psi1_injective : Function.Injective psi1 := by
  rw [injective_iff_map_eq_zero]
  intro P hP
  refine Polynomial.ext fun j => ?_
  have h1 : (psi1 P).coeff j =
      algebraMap ℚ[X] (RatFunc ℚ) (P.coeff j) * (RatFunc.X : RatFunc ℚ) ^ (2 * j) := by
    have h2 : psi1 P = (P.map (algebraMap ℚ[X] (RatFunc ℚ))).comp
        (C ((RatFunc.X : RatFunc ℚ) ^ 2) * X) := by
      rw [psi1, coe_eval₂RingHom, comp, eval₂_map, C_pow]
    rw [h2, comp_C_mul_X_coeff, coeff_map, ← pow_mul]
  rw [hP, coeff_zero] at h1
  have h3 := (mul_eq_zero.1 h1.symm).resolve_right (pow_ne_zero _ RatFunc.X_ne_zero)
  rw [coeff_zero]
  exact (map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).1 h3

theorem psi_injective : Function.Injective psi := by
  intro a b hab
  exact psi1_injective (IsFractionRing.injective (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)) hab)

/-! ### The rescaled matrices -/

/-- `G̃_N ∈ Mat(ℚ[t][Y])` (paper.tex l.1236, l.1242). -/
noncomputable def GsM (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) PS :=
  Matrix.of fun Y Y' => gramT tS cS X Y.word Y'.word

/-- `ρ̃_N ∈ Mat(ℚ[t][Y])` at `d = d_ν` (paper.tex l.1237, l.1247). -/
noncomputable def RsM (ν : Fin 2) (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) PS :=
  Matrix.of fun Y Y' => torusWordT tS cS X (dS ν) Y.word Y'.word

/-- The Cramer numerator of `Tr(G̃⁻¹ ρ̃)`. -/
noncomputable def numS (ν : Fin 2) (N : ℕ) : PS :=
  ∑ Y, ∑ Y', (GsM N).adjugate Y Y' * RsM ν N Y Y'

/-- The diagonal matrix `diag(t^{ℓ(λ)})`. -/
noncomputable def Tm (N : ℕ) : Matrix (Nat.Partition N) (Nat.Partition N) (RatFunc ℚ)[X] :=
  Matrix.diagonal fun Y => C (RatFunc.X : RatFunc ℚ) ^ Y.word.length

theorem GsM_map (N : ℕ) :
    (GsM N).map psi1 = Tm N * gramPoly (cT (RatFunc.X : RatFunc ℚ)) N * Tm N := by
  ext Y Y'
  rw [Matrix.map_apply, Tm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [GsM, Matrix.of_apply]
  rw [← gramT_map, psi1_tS, psi1_cS, psi1_X, gramT_eq _ _ _ _ _ (word_pos Y)]
  simp only [gramPoly, gram, Matrix.of_apply]
  ring

theorem RsM_map (ν : Fin 2) (N : ℕ) :
    (RsM ν N).map psi1 = Tm N * torusPoly (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) N * Tm N := by
  ext Y Y'
  rw [Matrix.map_apply, Tm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [RsM, Matrix.of_apply]
  rw [← torusWordT_map, psi1_tS, psi1_cS, psi1_X, psi1_dS,
    torusWordT_eq _ _ _ _ _ _ (word_pos Y)]
  simp only [torusPoly, torus, Matrix.of_apply]
  ring

/-- Conjugation by a diagonal matrix multiplies the Cramer numerator by `(∏ v)²`. -/
theorem adj_scale {n A : Type*} [Fintype n] [DecidableEq n] [CommRing A] (v : n → A)
    (G ρ : Matrix n n A) :
    ∑ i, ∑ j, (Matrix.diagonal v * G * Matrix.diagonal v).adjugate i j *
        (Matrix.diagonal v * ρ * Matrix.diagonal v) i j =
      (∏ i, v i) ^ 2 * ∑ i, ∑ j, G.adjugate i j * ρ i j := by
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.adjugate_diagonal,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hi := Finset.mul_prod_erase Finset.univ v (Finset.mem_univ i)
  have hj := Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)
  linear_combination
    (G.adjugate i j * ρ i j * ((∏ x ∈ Finset.univ.erase j, v x) * v j)) * hi +
      (G.adjugate i j * ρ i j * ∏ x, v x) * hj

/-- `t^{L_N}` with `L_N = ∑_{λ ⊢ N} ℓ(λ)`. -/
noncomputable def tauL (N : ℕ) : (RatFunc ℚ)[X] :=
  ∏ Y : Nat.Partition N, C (RatFunc.X : RatFunc ℚ) ^ Y.word.length

theorem tauL_ne_zero (N : ℕ) : tauL N ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => pow_ne_zero _ (C_ne_zero.2 RatFunc.X_ne_zero)

theorem psi1_det (N : ℕ) :
    psi1 (GsM N).det = tauL N ^ 2 * (gramPoly (cT (RatFunc.X : RatFunc ℚ)) N).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, GsM_map, Matrix.det_mul, Matrix.det_mul, Tm,
    Matrix.det_diagonal, tauL]
  ring

theorem psi1_numS (ν : Fin 2) (N : ℕ) :
    psi1 (numS ν N) = tauL N ^ 2 * Fnum (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) N := by
  have h1 : psi1 (numS ν N) =
      ∑ Y, ∑ Y', ((GsM N).map psi1).adjugate Y Y' * (RsM ν N).map psi1 Y Y' := by
    rw [numS, map_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun Y' _ => ?_
    rw [map_mul, ← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    rfl
  rw [h1, GsM_map, RsM_map, Tm, adj_scale]
  rfl

/-- The evaluation `t ↦ 0`, `ℚ[t][Y] → ℚ[Y]`. -/
noncomputable def ev0 : PS →+* ℚ[X] := mapRingHom (evalRingHom (0 : ℚ))

theorem ev0_tS : ev0 tS = 0 := by simp [ev0, tS]

theorem ev0_X : ev0 X = X := by simp [ev0]

/-- `G̃_N(0,Y) = D₀(Y) = diag(K_λ Y^{ℓ(λ)})` (paper.tex l.1241–1244). -/
theorem GsM_ev0 (N : ℕ) :
    (GsM N).map ev0 = Matrix.diagonal fun Y : Nat.Partition N =>
      ((topNat Y.word Y.word : ℕ) : ℚ[X]) * X ^ Y.word.length := by
  ext Y Y'
  rw [Matrix.map_apply]
  simp only [GsM, Matrix.of_apply]
  rw [← gramT_map, ev0_tS, ev0_X, gramT_zero _ _ _ _ (word_pos Y)]
  by_cases hYY : Y = Y'
  · subst hYY
    rw [Matrix.diagonal_apply_eq, if_pos rfl]
  · rw [Matrix.diagonal_apply_ne _ hYY]
    split_ifs with hlen
    · rw [topNat_eq_zero_of_not_perm hlen.symm fun hperm => hYY (word_injective hperm).symm,
        Nat.cast_zero, zero_mul]
    · rfl

theorem prime_tS : Prime tS := prime_C_iff.2 prime_X

/-- `det G̃_N` does not vanish at `t = 0`. -/
theorem not_tS_dvd_det (N : ℕ) : ¬ tS ∣ (GsM N).det := by
  rintro ⟨q, hq⟩
  have h1 : ev0 (GsM N).det = 0 := by rw [hq, map_mul, ev0_tS, zero_mul]
  rw [RingHom.map_det, RingHom.mapMatrix_apply, GsM_ev0, Matrix.det_diagonal,
    Finset.prod_eq_zero_iff] at h1
  obtain ⟨Y, -, hY⟩ := h1
  rcases mul_eq_zero.1 hY with h | h
  · exact (topNat_self_pos Y.word (word_pos Y)).ne' (Nat.cast_eq_zero.1 h)
  · exact pow_ne_zero _ X_ne_zero h

/-! ### Quotients regular at `t = 0` -/

/-- `x ∈ ℚ(t)(Δ)` is a quotient of polynomials in `(t, Y)`, `Y = t²Δ`, whose denominator does
not vanish at `t = 0`. -/
def RegT (x : RatFunc (RatFunc ℚ)) : Prop :=
  ∃ A B : PS, ¬ tS ∣ B ∧ x * psi B = psi A

theorem RegT.psi (a : PS) : RegT (psi a) :=
  ⟨a, 1, prime_tS.not_dvd_one, by rw [map_one, mul_one]⟩

theorem RegT.add {x y : RatFunc (RatFunc ℚ)} (hx : RegT x) (hy : RegT y) : RegT (x + y) := by
  obtain ⟨A, B, hB, h1⟩ := hx
  obtain ⟨A', B', hB', h2⟩ := hy
  refine ⟨A * B' + A' * B, B * B', fun h => ?_, ?_⟩
  · rcases prime_tS.dvd_or_dvd h with h | h
    · exact hB h
    · exact hB' h
  · rw [map_mul, map_add, map_mul, map_mul, ← h1, ← h2]
    ring

theorem RegT.mul {x y : RatFunc (RatFunc ℚ)} (hx : RegT x) (hy : RegT y) : RegT (x * y) := by
  obtain ⟨A, B, hB, h1⟩ := hx
  obtain ⟨A', B', hB', h2⟩ := hy
  refine ⟨A * A', B * B', fun h => ?_, ?_⟩
  · rcases prime_tS.dvd_or_dvd h with h | h
    · exact hB h
    · exact hB' h
  · rw [map_mul, map_mul, ← h1, ← h2]
    ring

/-- `F_N(c(b),Δ,d_ν) = Tr(G̃⁻¹ρ̃)` is regular at `t = 0` (paper.tex l.1248–1249). -/
theorem regT_Frat (ν : Fin 2) (N : ℕ) : RegT (Frat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) N) := by
  refine ⟨numS ν N, (GsM N).det, not_tS_dvd_det N, ?_⟩
  have hdet : algebraMap (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ))
      (gramPoly (cT (RatFunc.X : RatFunc ℚ)) N).det ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (RatFunc ℚ)[X] (RatFunc (RatFunc ℚ)))]
    exact gramPoly_det_ne_zero _ N
  simp only [psi, RingHom.comp_apply]
  rw [psi1_det, psi1_numS, map_mul, map_mul, Frat]
  field_simp

theorem regT_Hrat (ν : Fin 2) (N : ℕ) : RegT (Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) N) := by
  unfold Hrat
  refine Finset.sum_induction _ RegT (fun _ _ => RegT.add) ?_ fun j _ => ?_
  · simpa using RegT.psi 0
  · refine RegT.mul ?_ (regT_Frat ν (N - j))
    have : ((eta j : ℤ) : RatFunc (RatFunc ℚ)) = psi ((eta j : ℤ) : PS) := by
      rw [map_intCast]
    rw [this]
    exact RegT.psi _

/-- `2t² h_{u,1}(b) = t((t+1)² - (ut+1)²)/2`. -/
noncomputable def polH (u : ℕ) : ℚ[X] := C (1 / 2) * X * ((X + 1) ^ 2 - (C (u : ℚ) * X + 1) ^ 2)

theorem psi_pref (u : ℕ) :
    RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 *
        (2 * RatFunc.X - 2 * RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ))) =
      psi (2 * X - C (polH u)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have h1 : algebraMap ℚ[X] (RatFunc ℚ) (polH u) =
      2 * (RatFunc.X : RatFunc ℚ) ^ 2 * hT (u : ℤ) 1 RatFunc.X := by
    simp only [polH, map_mul, map_sub, map_add, map_pow, map_one, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, hT, map_div₀, map_ofNat, map_natCast]
    push_cast
    field_simp
    ring
  simp only [psi, RingHom.comp_apply]
  rw [map_sub, map_mul, psi1_X, psi1_C, h1, map_ofNat, map_sub, map_mul, map_mul, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_C, RatFunc.algebraMap_X, map_ofNat, map_mul, map_mul,
    map_pow, map_ofNat]
  ring

/-- `P_M^{(ν)}` is regular at `t = 0` (paper.tex l.1250–1252). -/
theorem regT_clearedH (ν : Fin 2) (M : ℕ) : RegT (clearedH ν M) := by
  have h1 : clearedH ν M =
      (M.factorial : RatFunc (RatFunc ℚ)) *
        (∏ u ∈ Finset.Icc 1 M, (RatFunc.C (RatFunc.X : RatFunc ℚ) ^ 2 *
          (2 * RatFunc.X - 2 * RatFunc.C (hT (u : ℤ) 1 (RatFunc.X : RatFunc ℚ))))) *
        Hrat (cT (RatFunc.X : RatFunc ℚ)) (d13 ν) M := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Icc, clearedH, ← pow_mul]
    simp only [Nat.add_sub_cancel]
    rw [d13]
    ring
  rw [h1]
  refine RegT.mul (RegT.mul ?_ ?_) (regT_Hrat ν M)
  · have : (M.factorial : RatFunc (RatFunc ℚ)) = psi (M.factorial : PS) := by rw [map_natCast]
    rw [this]
    exact RegT.psi _
  · refine Finset.prod_induction _ RegT (fun _ _ => RegT.mul) ?_ fun u _ => ?_
    · simpa using RegT.psi 1
    · rw [psi_pref]
      exact RegT.psi _

end Virasoro
