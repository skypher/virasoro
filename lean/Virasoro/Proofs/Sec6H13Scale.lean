import Virasoro.Proofs.Naturality
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Proposition 6.8(i) of `paper.tex` at 70bac53: the mode count (l.1232–1248)

Paper.tex l.1232–1248 puts `c(b) = 6/t + 13 + 6t`, `Δ = Y/t²`, `d = -2/t + ζ` and
`G̃_{λ,μ} = t^{ℓ(λ)+ℓ(μ)} G_{M,λ,μ}`, `ρ̃_{λ,μ} = t^{ℓ(λ)+ℓ(μ)} ρ_{M,λ,μ}`.  In the normal ordering
every `Δ` or `c` consumes at least two modes and every `d` at least one, so `G̃` and `ρ̃` are
polynomial in `(t, Y)`.

Here the count is carried by the commutation procedure itself.  With the rescaled modes
`L̃_k = τ L_k` (`k ≠ 0`), `L̃_0 = τ² L_0` and the rescaled words `τ^{ℓ(w)} L_{-w}|h⟩`, the
commutation rules read
`L̃_k L̃_{-y} = L̃_{-y} L̃_k + (k+y) τ L̃_{k-y}` (`k ≠ y`),
`L̃_k L̃_{-k} = L̃_{-k} L̃_k + 2k L̃_0 + τ · (τc)/12 · (k³-k)`,
and `L̃_0` acts on a word of level `n` by `τ²h + τ² n`.  They involve only `τ`, `c̃ = τ c`,
`Y = τ² h` (`dAct`), and the rescaled matrix elements are `gramT`, `torusWordT`.
-/

namespace Virasoro

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The pairing of a list of (word, coefficient) pairs with a function on words. -/
def wsum (s : St R) (φ : List ℕ → R) : R := (s.map fun t => t.2 * φ t.1).sum

omit [Algebra ℚ R] in
theorem wsum_nil (φ : List ℕ → R) : wsum ([] : St R) φ = 0 := by simp [wsum]

omit [Algebra ℚ R] in
theorem wsum_append (s t : St R) (φ : List ℕ → R) :
    wsum (s ++ t) φ = wsum s φ + wsum t φ := by simp [wsum]

omit [Algebra ℚ R] in
theorem wsum_singleton (w : List ℕ) (a : R) (φ : List ℕ → R) : wsum [(w, a)] φ = a * φ w := by
  simp [wsum]

omit [Algebra ℚ R] in
theorem wsum_map_cons (y : ℕ) (s : St R) (φ : List ℕ → R) :
    wsum (s.map fun t => (y :: t.1, t.2)) φ = wsum s fun u => φ (y :: u) := by
  simp [wsum, List.map_map, Function.comp_def]

omit [Algebra ℚ R] in
theorem wsum_map_mul (a : R) (s : St R) (φ : List ℕ → R) :
    wsum (s.map fun t => (t.1, a * t.2)) φ = a * wsum s φ := by
  unfold wsum
  rw [List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  ring

omit [Algebra ℚ R] in
theorem wsum_mul_left (a : R) (s : St R) (φ : List ℕ → R) :
    (wsum s fun u => a * φ u) = a * wsum s φ := by
  unfold wsum
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro t _
  ring

omit [Algebra ℚ R] in
theorem wsum_flatMap (s : St R) (g : List ℕ → St R) (φ : List ℕ → R) :
    wsum (s.flatMap fun t => (g t.1).map fun u => (u.1, t.2 * u.2)) φ =
      wsum s fun w => wsum (g w) φ := by
  induction s with
  | nil => simp [wsum]
  | cons t s ih =>
    rw [List.flatMap_cons, wsum_append, ih, wsum_map_mul]
    simp [wsum]

/-- The rescaled commutation procedure: `L̃_k` applied to the rescaled word `w`, with
`τ`, `c̃ = τ c` and `Y = τ² h` as parameters. -/
def dAct (τ ct Yv : R) : ℤ → List ℕ → St R
  | k, [] => if k < 0 then [([k.natAbs], 1)] else if k = 0 then [([], Yv)] else []
  | k, y :: w =>
      if k < 0 then [(k.natAbs :: y :: w, 1)]
      else if k = 0 then [(y :: w, Yv + τ ^ 2 * ((y + w.sum : ℕ) : R))]
      else
        ((dAct τ ct Yv k w).map fun t => (y :: t.1, t.2)) ++
        ((dAct τ ct Yv (k - y) w).map fun t =>
          (t.1, (((k + y : ℤ) : R) * (if k = y then 1 else τ)) * t.2)) ++
        (if k = y then [(w, τ * centralTerm ct k)] else [])

theorem centralTerm_mul (τ c : R) (k : ℤ) : centralTerm (τ * c) k = τ * centralTerm c k := by
  unfold centralTerm
  ring

/-- The power of `τ` carried by the rescaled mode `L̃_k`: `2` for `k = 0`, `1` otherwise. -/
def epsK (k : ℤ) : ℕ := if k = 0 then 2 else 1

theorem epsK_zero : epsK 0 = 2 := rfl

theorem epsK_ne {k : ℤ} (hk : k ≠ 0) : epsK k = 1 := if_neg hk

/-- The rescaled procedure computes the rescaled coefficients: for every test function `φ`,
`∑ q τ^{ℓ(u)} φ(u)` over `L̃_k w` equals `τ^{ε(k)+ℓ(w)} ∑ p φ(u)` over `L_k w`, with `ε(0) = 2`
and `ε(k) = 1` otherwise. -/
theorem dAct_rel (τ c h : R) : ∀ (w : List ℕ) (k : ℤ) (φ : List ℕ → R),
    wsum (dAct τ (τ * c) (τ ^ 2 * h) k w) (fun u => τ ^ u.length * φ u) =
      τ ^ (epsK k + w.length) * wsum (actWord c h k w) φ
  | [], k, φ => by
    unfold dAct actWord
    split_ifs with h1 h2
    · rw [epsK_ne (by omega)]
      simp [wsum_singleton]
    · rw [h2, epsK_zero]
      simp [wsum_singleton]
      ring
    · simp [wsum_nil]
  | y :: w, k, φ => by
    unfold dAct actWord
    split_ifs with h1 h2 h3
    · rw [epsK_ne (by omega)]
      simp only [wsum_singleton, List.length_cons]
      ring
    · rw [h2, epsK_zero]
      simp only [wsum_singleton, List.length_cons]
      ring
    · have ih1 := dAct_rel τ c h w k (fun u => τ * φ (y :: u))
      have ih2 := dAct_rel τ c h w (k - y) φ
      have hky : k - (y : ℤ) = 0 := by omega
      rw [hky, epsK_zero] at ih2
      rw [epsK_ne h2] at ih1 ⊢
      have e1 : (fun u : List ℕ => τ ^ (y :: u).length * φ (y :: u)) =
          fun u => τ ^ u.length * (τ * φ (y :: u)) := by
        funext u
        rw [List.length_cons]
        ring
      rw [hky]
      simp only [wsum_append, wsum_map_cons, wsum_map_mul, wsum_singleton]
      rw [e1, ih1, ih2, wsum_mul_left, centralTerm_mul]
      simp only [List.length_cons]
      ring
    · have ih1 := dAct_rel τ c h w k (fun u => τ * φ (y :: u))
      have ih2 := dAct_rel τ c h w (k - y) φ
      have hky : k - (y : ℤ) ≠ 0 := by omega
      rw [epsK_ne hky] at ih2
      rw [epsK_ne h2] at ih1 ⊢
      have e1 : (fun u : List ℕ => τ ^ (y :: u).length * φ (y :: u)) =
          fun u => τ ^ u.length * (τ * φ (y :: u)) := by
        funext u
        rw [List.length_cons]
        ring
      simp only [wsum_append, wsum_map_cons, wsum_map_mul, wsum_nil]
      rw [e1, ih1, ih2, wsum_mul_left]
      simp only [List.length_cons]
      ring

/-- `L̃_0` acts on a rescaled word of level `n` by `Y + τ² n`. -/
theorem dAct_zero_mode (τ ct Yv : R) (w : List ℕ) (φ : List ℕ → R) :
    wsum (dAct τ ct Yv 0 w) φ = (Yv + τ ^ 2 * ((w.sum : ℕ) : R)) * φ w := by
  cases w with
  | nil => simp [dAct, wsum_singleton]
  | cons y w => simp [dAct, wsum_singleton]

/-- `⟨h| L_{y_ℓ} ⋯ L_{y₁} L_{-w} |h⟩` by recursion on the positive modes. -/
def gT (c h : R) : List ℕ → List ℕ → R
  | [], w => if w.isEmpty then 1 else 0
  | y :: Y, w => wsum (actWord c h (y : ℤ) w) (gT c h Y)

/-- The rescaled Shapovalov matrix element `τ^{ℓ(Y)+ℓ(w)} ⟨h| L_Y L_{-w} |h⟩`. -/
def gramT (τ ct Yv : R) : List ℕ → List ℕ → R
  | [], w => if w.isEmpty then 1 else 0
  | y :: Y, w => wsum (dAct τ ct Yv (y : ℤ) w) (gramT τ ct Yv Y)

theorem wsum_actSt (c h : R) (k : ℤ) (s : St R) (φ : List ℕ → R) :
    wsum (actSt c h k s) φ = wsum s fun w => wsum (actWord c h k w) φ :=
  wsum_flatMap s _ φ

omit [Algebra ℚ R] in
theorem vac_eq_wsum (s : St R) : vac s = wsum s fun w => if w.isEmpty then 1 else 0 := by
  unfold vac wsum
  congr 1
  apply List.map_congr_left
  intro t _
  show (if t.1.isEmpty then t.2 else 0) = t.2 * (if t.1.isEmpty then 1 else 0)
  by_cases ht : t.1.isEmpty
  · rw [if_pos ht, if_pos ht, mul_one]
  · rw [if_neg ht, if_neg ht, mul_zero]

theorem vac_foldl (c h : R) : ∀ (Y : List ℕ) (s : St R),
    vac (Y.foldl (fun (s : St R) (y : ℕ) => actSt c h (y : ℤ) s) s) = wsum s (gT c h Y)
  | [], s => by rw [List.foldl_nil, vac_eq_wsum]; rfl
  | y :: Y, s => by
    rw [List.foldl_cons, vac_foldl c h Y, wsum_actSt]
    rfl

theorem gramWord_eq_gT (c h : R) (Y Y' : List ℕ) : gramWord c h Y Y' = gT c h Y Y' := by
  unfold gramWord
  rw [vac_foldl, wsum_singleton, one_mul]

/-- `G̃ = t^{ℓ(λ)+ℓ(μ)} G` (paper.tex l.1236–1237), with `c̃ = τ c`, `Y = τ² h`. -/
theorem gramT_eq (τ c h : R) : ∀ (Y w : List ℕ), (∀ y ∈ Y, 0 < y) →
    gramT τ (τ * c) (τ ^ 2 * h) Y w = τ ^ (Y.length + w.length) * gramWord c h Y w
  | [], w, _ => by
    rw [gramWord_eq_gT]
    unfold gramT gT
    cases w <;> simp
  | y :: Y, w, hY => by
    have hy : ¬ ((y : ℤ) = 0) := by
      have := hY y (List.mem_cons_self ..)
      omega
    have ih : gramT τ (τ * c) (τ ^ 2 * h) Y =
        fun u => τ ^ u.length * (τ ^ Y.length * gramWord c h Y u) := by
      funext u
      rw [gramT_eq τ c h Y u fun z hz => hY z (List.mem_cons_of_mem _ hz)]
      ring
    rw [gramWord_eq_gT]
    unfold gramT gT
    have e : gramWord c h Y = gT c h Y := funext (gramWord_eq_gT c h Y)
    rw [ih, dAct_rel, epsK_ne hy, wsum_mul_left, e]
    simp only [List.length_cons]
    ring

/-- The rescaled vacuum expectation `τ^{ℓ(w)} ⟨h| V_d(1) L_{-w} |h⟩`, with `d̃ = τ d`. -/
def phiT (τ dt : R) : List ℕ → R
  | [] => 1
  | m :: w => (τ * ((w.sum : ℕ) : R) + (m : R) * dt) * phiT τ dt w

omit [Algebra ℚ R] in
theorem phiT_eq (τ d : R) : ∀ w : List ℕ, phiT τ (τ * d) w = τ ^ w.length * phi d w
  | [] => by simp [phiT, phi]
  | m :: w => by
    simp only [phiT, phi, phiT_eq τ d w, List.length_cons]
    ring

/-- The rescaled torus matrix element `τ^{ℓ(Y)+ℓ(w)} ⟨h| L_Y V_d(1) L_{-w} |h⟩`. -/
def torusWordT (τ ct Yv dt : R) : List ℕ → List ℕ → R
  | [], w => phiT τ dt w
  | y :: Y, w =>
      wsum (dAct τ ct Yv (y : ℤ) w) (torusWordT τ ct Yv dt Y)
        + (τ * (((Y.sum : ℕ) : R) - ((w.sum : ℕ) : R)) + (y : R) * dt) * torusWordT τ ct Yv dt Y w

/-- `ρ̃ = t^{ℓ(λ)+ℓ(μ)} ρ` (paper.tex l.1237–1238), with `c̃ = τ c`, `Y = τ² h`, `d̃ = τ d`. -/
theorem torusWordT_eq (τ c h d : R) : ∀ (Y w : List ℕ), (∀ y ∈ Y, 0 < y) →
    torusWordT τ (τ * c) (τ ^ 2 * h) (τ * d) Y w =
      τ ^ (Y.length + w.length) * torusWord c h d Y w
  | [], w, _ => by
    unfold torusWordT torusWord
    rw [phiT_eq]
    simp
  | y :: Y, w, hY => by
    have hy : ¬ ((y : ℤ) = 0) := by
      have := hY y (List.mem_cons_self ..)
      omega
    have hY' : ∀ z ∈ Y, 0 < z := fun z hz => hY z (List.mem_cons_of_mem _ hz)
    have ih : torusWordT τ (τ * c) (τ ^ 2 * h) (τ * d) Y =
        fun u => τ ^ u.length * (τ ^ Y.length * torusWord c h d Y u) := by
      funext u
      rw [torusWordT_eq τ c h d Y u hY']
      ring
    unfold torusWordT torusWord
    rw [torusWordT_eq τ c h d Y w hY', ih, dAct_rel, epsK_ne hy, wsum_mul_left]
    simp only [List.length_cons]
    have e : wsum (actWord c h (y : ℤ) w) (fun u => torusWord c h d Y u) =
        ((actWord c h (y : ℤ) w).map fun t => t.2 * torusWord c h d Y t.1).sum := rfl
    rw [e]
    ring

/-! ### Naturality -/

section Nat

variable {S : Type*} [CommRing S] [Algebra ℚ S] (f : R →+* S)

theorem dAct_map (τ ct Yv : R) : ∀ (w : List ℕ) (k : ℤ),
    dAct (f τ) (f ct) (f Yv) k w = mapSt f (dAct τ ct Yv k w)
  | [], k => by
    unfold dAct
    split_ifs <;> simp [mapSt]
  | y :: w, k => by
    unfold dAct
    split_ifs with h1 h2 h3
    · simp [mapSt]
    · simp only [mapSt, List.map_cons, List.map_nil, map_add, map_mul, map_pow, map_natCast]
    · rw [dAct_map τ ct Yv w k, dAct_map τ ct Yv w (k - y)]
      simp [mapSt, map_centralTerm, List.map_map, Function.comp_def]
    · rw [dAct_map τ ct Yv w k, dAct_map τ ct Yv w (k - y)]
      simp [mapSt, List.map_map, Function.comp_def]

omit [Algebra ℚ R] [Algebra ℚ S] in
theorem wsum_mapSt (s : St R) (φ : List ℕ → R) :
    wsum (mapSt f s) (fun u => f (φ u)) = f (wsum s φ) := by
  unfold wsum mapSt
  rw [map_list_sum, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp

theorem gramT_map (τ ct Yv : R) : ∀ (Y w : List ℕ),
    gramT (f τ) (f ct) (f Yv) Y w = f (gramT τ ct Yv Y w)
  | [], w => by
    unfold gramT
    split_ifs <;> simp
  | y :: Y, w => by
    have ih : gramT (f τ) (f ct) (f Yv) Y = fun u => f (gramT τ ct Yv Y u) := by
      funext u
      exact gramT_map τ ct Yv Y u
    unfold gramT
    rw [ih, dAct_map, wsum_mapSt]

omit [Algebra ℚ R] [Algebra ℚ S] in
theorem phiT_map (τ dt : R) : ∀ w : List ℕ, phiT (f τ) (f dt) w = f (phiT τ dt w)
  | [] => by simp [phiT]
  | m :: w => by simp only [phiT, phiT_map τ dt w, map_mul, map_add, map_natCast]

theorem torusWordT_map (τ ct Yv dt : R) : ∀ (Y w : List ℕ),
    torusWordT (f τ) (f ct) (f Yv) (f dt) Y w = f (torusWordT τ ct Yv dt Y w)
  | [], w => by simp [torusWordT, phiT_map]
  | y :: Y, w => by
    have ih : torusWordT (f τ) (f ct) (f Yv) (f dt) Y =
        fun u => f (torusWordT τ ct Yv dt Y u) := by
      funext u
      exact torusWordT_map τ ct Yv dt Y u
    unfold torusWordT
    rw [ih, dAct_map, wsum_mapSt]
    simp only [map_add, map_mul, map_sub, map_natCast]

end Nat

end Virasoro
