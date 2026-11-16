import Virasoro.Statements.Sec2
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.Ring

/-!
# Naturality of the Shapovalov and torus matrices, and Lemma 2.4

The normal-ordering evaluation commutes with every ring homomorphism between commutative
`ℚ`-algebras.  Applied to the evaluation of polynomials this gives Lemma 2.4.
-/

namespace Virasoro

variable {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] (f : R →+* S)

theorem map_centralTerm (c : R) (m : ℤ) : f (centralTerm c m) = centralTerm (f c) m := by
  unfold centralTerm
  rw [map_mul, RingHom.map_rat_algebraMap]

/-- Applying `f` to the coefficients of a list of (word, coefficient) pairs. -/
def mapSt (s : St R) : St S := s.map fun t => (t.1, f t.2)

theorem mapSt_append (s t : St R) : mapSt f (s ++ t) = mapSt f s ++ mapSt f t := by
  simp [mapSt]

theorem actWord_map (c h : R) : ∀ (w : List ℕ) (k : ℤ),
    actWord (f c) (f h) k w = mapSt f (actWord c h k w)
  | [], k => by
    unfold actWord
    split_ifs <;> simp [mapSt]
  | y :: w, k => by
    unfold actWord
    split_ifs with h1 h2 h3
    · simp [mapSt]
    · simp only [mapSt, List.map_cons, List.map_nil, map_add, map_natCast]
    · rw [actWord_map c h w k, actWord_map c h w (k - y)]
      simp [mapSt, map_centralTerm, List.map_map, Function.comp_def]
    · rw [actWord_map c h w k, actWord_map c h w (k - y)]
      simp [mapSt, List.map_map, Function.comp_def]

theorem actSt_map (c h : R) (k : ℤ) (s : St R) :
    actSt (f c) (f h) k (mapSt f s) = mapSt f (actSt c h k s) := by
  unfold actSt
  induction s with
  | nil => simp [mapSt]
  | cons t s ih =>
    simp only [mapSt, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih, actWord_map]
    simp [mapSt, List.map_map, Function.comp_def]

theorem vac_map (s : St R) : vac (mapSt f s) = f (vac s) := by
  unfold vac
  induction s with
  | nil => simp [mapSt]
  | cons t s ih =>
    simp only [mapSt, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, map_add]
    congr 1
    split_ifs
    · rfl
    · exact (map_zero f).symm

theorem foldl_actSt_map (c h : R) (Y : List ℕ) (s : St R) :
    Y.foldl (fun (s : St S) (y : ℕ) => actSt (f c) (f h) (y : ℤ) s) (mapSt f s) =
      mapSt f (Y.foldl (fun (s : St R) (y : ℕ) => actSt c h (y : ℤ) s) s) := by
  induction Y generalizing s with
  | nil => rfl
  | cons y Y ih =>
    rw [List.foldl_cons, List.foldl_cons, actSt_map, ih]

theorem gramWord_map (c h : R) (Y Y' : List ℕ) :
    gramWord (f c) (f h) Y Y' = f (gramWord c h Y Y') := by
  unfold gramWord
  have : ([(Y', (1 : S))] : St S) = mapSt f [(Y', (1 : R))] := by simp [mapSt]
  rw [this, foldl_actSt_map, vac_map]

theorem phi_map (d : R) (w : List ℕ) : phi (f d) w = f (phi d w) := by
  induction w with
  | nil => simp [phi]
  | cons m w ih => simp only [phi, ih, map_mul, map_add, map_natCast]

theorem torusWord_map (c h d : R) : ∀ (Y w : List ℕ),
    torusWord (f c) (f h) (f d) Y w = f (torusWord c h d Y w)
  | [], w => by simp [torusWord, phi_map]
  | y :: Y, w => by
    unfold torusWord
    rw [actWord_map, torusWord_map c h d Y w]
    simp only [map_add, map_mul, map_sub, map_natCast, mapSt, List.map_map]
    congr 1
    rw [map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro t _
    simp [torusWord_map c h d Y t.1]

theorem gram_map (c h : R) (N : ℕ) : gram (f c) (f h) N = (gram c h N).map f := by
  ext Y Y'
  simp [gram, gramWord_map]

theorem torus_map (c h d : R) (N : ℕ) : torus (f c) (f h) (f d) N = (torus c h d N).map f := by
  ext Y Y'
  simp [torus, torusWord_map]

/-- Paper label: lem:polynomial-entries -/
theorem lem_polynomial_entries : Stmt_lem_polynomial_entries := by
  intro N
  refine ⟨⟨gram (MvPolynomial.X 0) (MvPolynomial.X 1) N, fun c Δ => ?_⟩,
    ⟨torus (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) N, fun c Δ d => ?_⟩⟩
  · have := gram_map (MvPolynomial.aeval ![c, Δ] : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] ℂ).toRingHom
      (MvPolynomial.X 0) (MvPolynomial.X 1) N
    simpa using this
  · have := torus_map (MvPolynomial.aeval ![c, Δ, d] : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] ℂ).toRingHom
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) N
    simpa using this

example : Stmt_lem_polynomial_entries := lem_polynomial_entries

end Virasoro
