import Virasoro.Proofs.Sec8RegGen2
import Virasoro.Proofs.Sec6Norm

/-!
# Lemma 8.4: one row of the table

`regularCase_of` proves `RegularCase r s h D` from the finite data of the level `m = r s`
(`LevelData`) and the determinant of `B_m(1/2,h)` over `ℚ`, which is certified by a permuted
LU factorization (`det_of_PLU`).  The regularity part follows the paper: Cramer's rule at
`b₀` (`regular_of_B`), the specialized vector is singular, it is the unique normalized one
(`unique_of_B`), and the two identities of Proposition 6.2 specialize (`normalization_at`).
-/

namespace Virasoro

open Verma Module

/-! ### Determinants from permuted LU factorizations -/

theorem det_of_PLU {n : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] {B L U : Matrix n n ℚ}
    (σ : Equiv.Perm n) (hLU : B.submatrix σ id = L * U) (hL : L.IsLowerTriangular)
    (hL1 : ∀ i, L i i = 1) (hU : U.IsUpperTriangular) :
    B.det = ((Equiv.Perm.sign σ : ℤ) : ℚ) * ∏ i, U i i := by
  have h1 := Matrix.det_permute σ B
  rw [hLU, Matrix.det_mul, Matrix.det_of_isLowerTriangular L hL,
    Matrix.det_of_isUpperTriangular hU] at h1
  simp only [hL1, Finset.prod_const_one, one_mul] at h1
  have hs : ((Equiv.Perm.sign σ : ℤ) : ℚ) * ((Equiv.Perm.sign σ : ℤ) : ℚ) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [h1, ← mul_assoc, hs, one_mul]

theorem sign_swaps {n : Type*} [DecidableEq n] [Fintype n] (l : List (n × n))
    (h : ∀ p ∈ l, p.1 ≠ p.2) :
    Equiv.Perm.sign (l.map fun p => Equiv.swap p.1 p.2).prod = (-1) ^ l.length := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.prod_cons, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (h p List.mem_cons_self),
      ih fun q hq => h q (List.mem_cons_of_mem _ hq), List.length_cons, pow_succ, mul_comm]

/-- `a mod n` as an element of `Fin n`. -/
def finOf (n : ℕ) (hn : 0 < n) (a : ℕ) : Fin n := ⟨a % n, Nat.mod_lt a hn⟩

/-- The permutation given by a list of transpositions. -/
def swapPerm (n : ℕ) (hn : 0 < n) (l : List (ℕ × ℕ)) : Equiv.Perm (Fin n) :=
  (l.map fun p => Equiv.swap (finOf n hn p.1) (finOf n hn p.2)).prod

theorem sign_swapPerm (n : ℕ) (hn : 0 < n) (l : List (ℕ × ℕ))
    (h : ∀ p ∈ l, finOf n hn p.1 ≠ finOf n hn p.2) :
    ((Equiv.Perm.sign (swapPerm n hn l) : ℤ) : ℚ) = (-1) ^ l.length := by
  unfold swapPerm
  have := sign_swaps (l.map fun p => (finOf n hn p.1, finOf n hn p.2)) (by
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact h p hp)
  rw [List.map_map] at this
  rw [show (fun p : ℕ × ℕ => Equiv.swap (finOf n hn p.1) (finOf n hn p.2)) =
    (fun p : Fin n × Fin n => Equiv.swap p.1 p.2) ∘ fun p => (finOf n hn p.1, finOf n hn p.2)
    from rfl, this, List.length_map]
  push_cast
  rfl

/-- A matrix from a list of rows. -/
def matOfRows (n : ℕ) (rows : List (List ℚ)) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => (rows.getD i []).getD j 0

/-! ### Enumerations by `lexWords` -/

theorem isEnum_lexWords (n : ℕ) (hnd : (lexWords n).Nodup)
    (hp : ∀ w ∈ lexWords n, PosWord w ∧ w.sum = n ∧ w.Pairwise (· ≥ ·))
    (hc : ∀ w ∈ decWords n, w ∈ lexWords n) : IsEnum n (lexWords n) where
  nodup := hnd
  pos := fun w hw => (hp w hw).1
  sum := fun w hw => (hp w hw).2.1
  sorted := fun w hw => (hp w hw).2.2
  complete := fun w hw hs hpw => hc w (mem_decWordsAux (n + 1) n n w (by omega) hw hs hpw
    fun y hy => by have := List.le_sum_of_mem hy; omega)

/-! ### Naturality of `B_m` -/

theorem Bmat_map {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    (φ : R →+* S) (m : ℕ) (c h : R) : Bmat m (φ c) (φ h) = (Bmat m c h).map φ := by
  rw [Bmat_eq, Bmat_eq]
  ext i j
  simp only [Matrix.of_apply, Matrix.map_apply, evalAff_map]

/-! ### One row of the table -/

theorem isSingular_of_rows {m : ℕ} (hD : LevelData m) {cv hv : ℂ} (pv : Nat.Partition m → ℂ)
    (h1 : pv (onesPartition m) = 1) (hL1 : L 1 (pbwCoord (c := cv) (h := hv) m pv) = 0)
    (hL2 : L 2 (pbwCoord (c := cv) (h := hv) m pv) = 0) :
    IsSingular (pbwCoord (c := cv) (h := hv) m pv) m := by
  refine ⟨fun h0 => ?_, L_zero_of_mem_level ⟨pv, rfl⟩, L_pos_zero_of_L12 hL1 hL2⟩
  have := congrFun (pbwCoord_injective m (h0.trans (map_zero _).symm)) (onesPartition m)
  rw [h1] at this
  exact one_ne_zero this

theorem regularCase_of (hH : Cited_HJSNormalizations) (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hq Dq : ℚ) (h D : ℂ) (hh : kacH r s b0 = h) (hhq : qC hq = h) (hDq : qC Dq = D)
    (hD0 : Dq ≠ 0) (hLD : LevelData (r * s)) (hdet : (Bmat (r * s) (1 / 2 : ℚ) hq).det = Dq) :
    RegularCase r s h D := by
  have hc : kacC b0 = 1 / 2 := kacC_b0'
  have hBC : Bmat (r * s) (1 / 2 : ℂ) h = (Bmat (r * s) (1 / 2 : ℚ) hq).map qC := by
    rw [← Bmat_map, ← hhq]
    congr 1
    simp [map_div₀]
  have hdetC : (Bmat (r * s) (1 / 2 : ℂ) h).det = D := by
    rw [hBC, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, hDq]
  have hdetne : (Bmat (r * s) (1 / 2 : ℂ) h).det ≠ 0 := by
    rw [hdetC, ← hDq]
    exact (map_ne_zero qC).2 hD0
  refine ⟨hh, ⟨Sfun 1 (1 / 2 : ℂ) h, Sfun 2 (1 / 2 : ℂ) h, fun Y hY => ?_, fun Y hY => ?_, ?_⟩, ?_⟩
  · exact L_neg_expand 1 Y hLD.e1.nodup (hLD.t1 Y hY)
  · exact L_neg_expand 2 Y hLD.e2.nodup (hLD.t2 Y hY)
  · exact hdetC
  · intro p hp1 hsing
    have hcX : EvToK b0 (kacC (RatFunc.X : RatFunc ℂ)) (1 / 2 : ℂ) := hc ▸ evToK_kacC b0_ne_zero
    have hhX : EvToK b0 (kacH r s (RatFunc.X : RatFunc ℂ)) h := hh ▸ evToK_kacH b0_ne_zero r s
    obtain ⟨pv, hpv, -⟩ := regular_of_B hLD hcX hhX hdetne p hp1 (hsing.2.2 1 (by norm_num))
      (hsing.2.2 2 (by norm_num))
    have hpv1 : pv (onesPartition (r * s)) = 1 := by
      have := hpv (onesPartition (r * s))
      rw [hp1] at this
      exact this.uniq (evToK_one (K := ℂ) (b := b0))
    have hsv : IsSingular (pbwCoord (c := (1 / 2 : ℂ)) (h := h) (r * s) pv) (r * s) :=
      isSingular_of_rows hLD pv hpv1
        (rows_specialize 1 hLD.em hLD.e1 hLD.t1 hcX hhX p pv hpv (hsing.2.2 1 (by norm_num)))
        (rows_specialize 2 hLD.em hLD.e2 hLD.t2 hcX hhX p pv hpv (hsing.2.2 2 (by norm_num)))
    have hp0 : (fun Y => RatFunc.eval (RingHom.id ℂ) b0 (p Y)) = pv := by
      funext Y
      have := (hpv Y).2
      rwa [Algebra.algebraMap_self] at this
    refine ⟨fun Y => ?_, ?_⟩
    · have := (hpv Y).1
      rwa [Algebra.algebraMap_self, Polynomial.eval₂_id] at this
    have hp0' : ∀ Y, RatFunc.eval (RingHom.id ℂ) b0 (p Y) = pv Y := fun Y => congrFun hp0 Y
    simp only [hp0']
    refine ⟨hpv1, hsv, fun p' hp1' hs' => unique_of_B hLD hdetne p' pv hp1' hpv1 hs' hsv, ?_⟩
    -- the identities of Proposition 6.2 at `b₀`
    obtain ⟨pq, ⟨hpq1, hpqs⟩, -, -, -, hcont⟩ := normalization_at hH r s hr hs
    have hcQ : EvToK b0 (kacC (RatFunc.X : RatFunc ℚ)) (1 / 2 : ℂ) := hc ▸ evToK_kacC b0_ne_zero
    have hhQ : EvToK b0 (kacH r s (RatFunc.X : RatFunc ℚ)) h := hh ▸ evToK_kacH b0_ne_zero r s
    obtain ⟨pv', hpv', -⟩ := regular_of_B hLD hcQ hhQ hdetne pq hpq1 (hpqs.2.2 1 (by norm_num))
      (hpqs.2.2 2 (by norm_num))
    obtain ⟨hs1, hone1, hcross, htor⟩ := hcont ℂ b0 b0_ne_zero fun Y => (hpv' Y).1
    rw [hc, hh] at hs1 hcross htor
    have hpeq : (fun Y => RatFunc.eval (algebraMap ℚ ℂ) b0 (pq Y)) = pv :=
      unique_of_B hLD hdetne _ pv hone1 hpv1 hs1 hsv
    rw [hpeq] at hcross htor
    exact ⟨by rw [genA_inv]; exact hcross, htor⟩

end Virasoro
