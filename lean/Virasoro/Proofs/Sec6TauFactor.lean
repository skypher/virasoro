import Virasoro.Proofs.Sec6Regular
import Virasoro.Proofs.Sec6TwoTerm
import Virasoro.Proofs.Singular
import Virasoro.Proofs.Family
import Virasoro.Proofs.PairingConstr
import Virasoro.Proofs.CoordTools
import Virasoro.Proofs.Specialize
import Virasoro.Proofs.Sec3
import Virasoro.Proofs.JantzenLevel
import Virasoro.Proofs.Levels

/-!
# Proposition 6.9 of `paper.tex` at 70bac53: the factorization of `τ^±_k` (l.1433–1446)

Normalize each `w^±_k` to `L_{-1}^{ℓ^±_k}`-coefficient `1`.  By Lemma 6.6 (regular normalized
singular vectors), Lemma 5.5 (singular factorization) and the uniqueness of singular vectors
(Iohara–Koga, Proposition 5.1), at `b = b⋆`:
`τ⁺_{2j+1} = 𝒫_{r+jp, s+jp'}`, `τ⁻_{2j+1} = 𝒫_{(j+1)p-r, (j+1)p'-s}`, and for `k = 2j`,
`τ⁺_{2j} = 𝒫_{r+(j-1)p, s+(j-1)p'} 𝒫_{(2j-1)p+r, p'-s}`,
`τ⁻_{2j} = 𝒫_{r+(j-1)p, s+(j-1)p'} 𝒫_{p-r, (2j-1)p'+s}`.
-/

namespace Virasoro

open Polynomial Verma

/-- Frozen sub-statement of Proposition 6.9 (paper.tex l.1433–1446): the factorization of
`τ^±_k(d) = ⟨w^±_k|V_d(1)|w^±_k⟩` into the polynomials `𝒫_{R,S}(b⋆,d)`.

Demand sheet.
- `MinimalSetting`; every `k ≥ 1`; both signs (`ε = true` is `+`);
- `w^±_k`: every singular vector of level `ℓ^±_k` with `L_{-1}^{ℓ^±_k}`-coefficient `1`, in
  coordinates `x` (l.1433–1434; singular vectors of a given level are unique up to a scalar);
- identities of polynomials in `d`: `τ` is `torusPolyForm`, `𝒫_{R,S}(b⋆,·)` is `genPpoly`;
- odd `k = 2j+1`: `(R,S) = (r+jp, s+jp')` for `+`, `((j+1)p-r, (j+1)p'-s)` for `-` (l.1437–1438);
- even `k = 2j`: the common factor `𝒫_{r+(j-1)p, s+(j-1)p'}` times `𝒫_{(2j-1)p+r, p'-s}` for `+`,
  `𝒫_{p-r, (2j-1)p'+s}` for `-` (l.1439–1440); `j = k/2`, `2j - 1 = k - 1`. -/
def Stmt_sub_tau_factorization : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b → ∀ (k : ℕ) (ε : Bool), 1 ≤ k →
    ∀ x : Nat.Partition (ellOrb p p' r s ε k) → ℂ, x (onesPartition _) = 1 →
      Verma.IsSingular
        (Verma.pbwCoord (c := kacC b) (h := kacH r s b) (ellOrb p p' r s ε k) x)
        (ellOrb p p' r s ε k) →
      (k % 2 = 1 → torusPolyForm (kacC b) (kacH r s b) x =
        (if ε then genPpoly (r + k / 2 * p) (s + k / 2 * p') b
          else genPpoly ((k / 2 + 1) * p - r) ((k / 2 + 1) * p' - s) b)) ∧
      (k % 2 = 0 → torusPolyForm (kacC b) (kacH r s b) x =
        genPpoly (r + (k / 2 - 1) * p) (s + (k / 2 - 1) * p') b *
          (if ε then genPpoly ((k - 1) * p + r) (p' - s) b
            else genPpoly (p - r) ((k - 1) * p' + s) b))

theorem torusPolyForm_eval (c h : ℂ) {N : ℕ} (v : Nat.Partition N → ℂ) (d : ℂ) :
    (torusPolyForm c h v).eval d = torusForm c h d N v v := by
  have := map_torusForm (Polynomial.evalRingHom d) (C c) (C h) (X : ℂ[X]) N
    (fun Y => C (v Y)) (fun Y => C (v Y))
  simp only [coe_evalRingHom, eval_C, eval_X] at this
  exact this

theorem torusForm_smul (c h d : ℂ) {N : ℕ} (a : ℂ) (y : Nat.Partition N → ℂ) :
    torusForm c h d N (a • y) (a • y) = a ^ 2 * torusForm c h d N y y := by
  unfold torusForm
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The value `χ_{R,S}(b⋆)` of the normalized singular vector (Lemma 6.6). -/
theorem exists_chiT (hH : Cited_HJSNormalizations) {b : ℂ} (hb : b ≠ 0) (R S : ℕ) (hR : 0 < R)
    (hS : 0 < S) :
    ∃ y : Nat.Partition (R * S) → ℂ, y (onesPartition (R * S)) = 1 ∧
      IsSingular (pbwCoord (c := kacC b) (h := kacH R S b) (R * S) y) (R * S) ∧
      ∀ d : ℂ, torusForm (kacC b) (kacH R S b) d (R * S) y y = (genPpoly R S b).eval d := by
  obtain ⟨q, ⟨hq1, hqs⟩, -, -, -⟩ := hH R S hR hS
  obtain ⟨-, h1, h2, h3, -⟩ := lem_regular_everywhere_of_cited hH R S hR hS q hq1 hqs b hb
  exact ⟨_, h1, h2, fun d => by rw [genPpoly_eval]; exact h3 d⟩

/-- A normalized singular vector of level `n` in `M(c,h)` has the torus norm of any other
singular vector of that level whose `L_{-1}^n`-coefficient has square `1`. -/
theorem tau_eq_of_singular (hU : Cited_SingularUnique) {c h h' : ℂ} {n n' : ℕ}
    (hh : h' = h) (hn : n' = n) (y : Nat.Partition n' → ℂ)
    (hy1 : y (onesPartition n') ^ 2 = 1)
    (hy : IsSingular (pbwCoord (c := c) (h := h') n' y) n')
    (x : Nat.Partition n → ℂ) (hx1 : x (onesPartition n) = 1)
    (hx : IsSingular (pbwCoord (c := c) (h := h) n x) n) :
    torusPolyForm c h x = torusPolyForm c h' y := by
  subst hh hn
  obtain ⟨a, ha⟩ := hU c h' n' _ _ hy hx
  rw [← map_smul] at ha
  have hxy := pbwCoord_injective n' ha
  have ha2 : a ^ 2 = 1 := by
    have h1 := congrFun hxy (onesPartition n')
    rw [Pi.smul_apply, hx1, smul_eq_mul] at h1
    have h2 : (a * y (onesPartition n')) ^ 2 = 1 := by rw [← h1, one_pow]
    rw [mul_pow, hy1, mul_one] at h2
    exact h2
  refine Polynomial.funext fun d => ?_
  rw [torusPolyForm_eval, torusPolyForm_eval, hxy, torusForm_smul, ha2, one_mul]

theorem torusPolyForm_of_eval {c h : ℂ} {n : ℕ} {y : Nat.Partition n → ℂ} {Q : ℂ[X]}
    (hQ : ∀ d : ℂ, torusForm c h d n y y = Q.eval d) : torusPolyForm c h y = Q :=
  torusForm_poly_eq hQ

theorem kacH_min' {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) (R S : ℤ) :
    kacH R S b = (((p' : ℂ) * R - p * S) ^ 2 - ((p' : ℂ) - p) ^ 2) / (4 * p * p') := by
  obtain ⟨hp, hp', -, -, -, -, -, -, hb⟩ := hset
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  exact kacH_minimal (p : ℂ) (p' : ℂ) hp0 hp'0 b hb (R : ℂ) (S : ℂ)

theorem minimal_b_ne {p p' r s : ℕ} {b : ℂ} (hset : MinimalSetting p p' r s b) : b ≠ 0 := by
  obtain ⟨hp, hp', -, -, -, -, -, -, hb⟩ := hset
  intro h0
  rw [h0] at hb
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have : (0 : ℂ) = -(p' : ℂ) / p := by simpa using hb
  field_simp at this
  exact hp'0 (by linear_combination this)

/-- The factorization for odd `k` (paper.tex l.1437–1438). -/
theorem tau_odd (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) {p p' r s : ℕ}
    {b : ℂ} (hset : MinimalSetting p p' r s b) {k : ℕ} (ε : Bool) (hk : k % 2 = 1)
    (x : Nat.Partition (ellOrb p p' r s ε k) → ℂ) (hx1 : x (onesPartition _) = 1)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellOrb p p' r s ε k) x)
      (ellOrb p p' r s ε k)) :
    torusPolyForm (kacC b) (kacH r s b) x =
      (if ε then genPpoly (r + k / 2 * p) (s + k / 2 * p') b
        else genPpoly ((k / 2 + 1) * p - r) ((k / 2 + 1) * p' - s) b) := by
  have hb0 := minimal_b_ne hset
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  have hk0 : k ≠ 0 := by omega
  have hk2 : ¬ k % 2 = 0 := by omega
  cases ε with
  | true =>
    obtain ⟨y, hy1, hys, hyv⟩ := exists_chiT hH hb0 (r + k / 2 * p) (s + k / 2 * p')
      (by omega) (by omega)
    have hh : kacH ((r + k / 2 * p : ℕ) : ℤ) ((s + k / 2 * p' : ℕ) : ℤ) b = kacH r s b := by
      rw [kacH_min' hset', kacH_min' hset']
      push_cast
      ring
    have hn : (r + k / 2 * p) * (s + k / 2 * p') = ellOrb p p' r s true k := by
      simp [ellOrb, ellPlus, hk0, hk2]
    rw [if_pos rfl, tau_eq_of_singular hU hh hn y (by rw [hy1, one_pow]) hys x hx1 hx]
    exact torusPolyForm_of_eval hyv
  | false =>
    have h1 : r ≤ (k / 2 + 1) * p := by
      have : p ≤ (k / 2 + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have h2 : s ≤ (k / 2 + 1) * p' := by
      have : p' ≤ (k / 2 + 1) * p' := Nat.le_mul_of_pos_left _ (by omega)
      omega
    obtain ⟨y, hy1, hys, hyv⟩ := exists_chiT hH hb0 ((k / 2 + 1) * p - r)
      ((k / 2 + 1) * p' - s)
      (by have : p ≤ (k / 2 + 1) * p := Nat.le_mul_of_pos_left _ (by omega)
          omega)
      (by have : p' ≤ (k / 2 + 1) * p' := Nat.le_mul_of_pos_left _ (by omega)
          omega)
    have hh : kacH (((k / 2 + 1) * p - r : ℕ) : ℤ) (((k / 2 + 1) * p' - s : ℕ) : ℤ) b =
        kacH r s b := by
      rw [kacH_min' hset', kacH_min' hset']
      push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
      ring
    have hn : ((k / 2 + 1) * p - r) * ((k / 2 + 1) * p' - s) = ellOrb p p' r s false k := by
      simp [ellOrb, ellMinus, hk0, hk2]
    rw [if_neg (by simp), tau_eq_of_singular hU hh hn y (by rw [hy1, one_pow]) hys x hx1 hx]
    exact torusPolyForm_of_eval hyv

/-- The push-forward of a normalized singular vector of `M(c,h+ℓ)` along the homomorphism
defined by a normalized singular vector of level `ℓ` of `M(c,h)`: torus norms multiply
(Lemma 5.5). -/
theorem tau_push (hU : Cited_SingularUnique) {c h h0 : ℂ} {ℓ m : ℕ} (hh0 : h0 = h)
    (y0 : Nat.Partition ℓ → ℂ) (hy01 : y0 (onesPartition ℓ) = 1)
    (hy0 : IsSingular (pbwCoord (c := c) (h := h0) ℓ y0) ℓ) {P0 P1 : ℂ[X]}
    (hP0 : ∀ d : ℂ, torusForm c h0 d ℓ y0 y0 = P0.eval d)
    {h' : ℂ} (hh : h' = h + (ℓ : ℂ)) (y1 : Nat.Partition m → ℂ)
    (hy11 : y1 (onesPartition m) = 1)
    (hy1 : IsSingular (pbwCoord (c := c) (h := h') m y1) m)
    (hP1 : ∀ d : ℂ, torusForm c h' d m y1 y1 = P1.eval d)
    {n : ℕ} (hn : ℓ + m = n) (x : Nat.Partition n → ℂ) (hx1 : x (onesPartition n) = 1)
    (hx : IsSingular (pbwCoord (c := c) (h := h) n x) n) :
    torusPolyForm c h x = P0 * P1 := by
  subst hh0 hh hn
  obtain ⟨j, hjhw, hjL, hjneg⟩ := exists_singularHom hy0.2.1 hy0.2.2
  have hw : j (pbwCoord (c := c) (h := h0 + (ℓ : ℂ)) m y1) =
      ∑ Z : Nat.Partition m, y1 Z • (VirEnv.negOp c Z.word • pbwCoord (c := c) (h := h0) ℓ y0) := by
    rw [pbwCoord_apply, map_sum]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [map_smul, hjneg]
  have hmem : j (pbwCoord (c := c) (h := h0 + (ℓ : ℂ)) m y1) ∈
      level (c := c) (h := h0) (ℓ + m) := by
    rw [hw]
    refine Submodule.sum_mem _ fun Z _ => Submodule.smul_mem _ _ ?_
    have := negOp_smul_mem_level (c := c) (h := h0) (ℓ := ℓ) (v := pbwCoord ℓ y0) ⟨y0, rfl⟩ Z.word
    rwa [word_sum'] at this
  obtain ⟨z, hz⟩ := hmem
  have hstar : ∀ d : ℂ, torusForm c h0 d (ℓ + m) z z = P0.eval d * P1.eval d := by
    intro d
    have hT := isPrimaryPairing_pairing (c := c) (h := h0) d
    have hL : pairing c h0 d (j (pbwCoord (c := c) (h := h0 + (ℓ : ℂ)) m y1))
        (j (pbwCoord (c := c) (h := h0 + (ℓ : ℂ)) m y1)) =
        ∑ Z : Nat.Partition m, ∑ Z' : Nat.Partition m, y1 Z * (y1 Z' *
          (pairing c h0 d (pbwCoord ℓ y0) (pbwCoord ℓ y0) * torus c (h0 + (ℓ : ℂ)) d m Z Z')) := by
      have h1 : ∀ u : Verma ℂ c h0, pairing c h0 d
          (∑ Z : Nat.Partition m, y1 Z • (VirEnv.negOp c Z.word • pbwCoord (c := c) (h := h0) ℓ y0))
          u = ∑ Z : Nat.Partition m, y1 Z *
            pairing c h0 d (VirEnv.negOp c Z.word • pbwCoord (c := c) (h := h0) ℓ y0) u := by
        intro u
        rw [map_sum, LinearMap.sum_apply]
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
      have h2 : ∀ v : Verma ℂ c h0, pairing c h0 d v
          (∑ Z : Nat.Partition m, y1 Z • (VirEnv.negOp c Z.word • pbwCoord (c := c) (h := h0) ℓ y0))
          = ∑ Z : Nat.Partition m, y1 Z *
            pairing c h0 d v (VirEnv.negOp c Z.word • pbwCoord (c := c) (h := h0) ℓ y0) := by
        intro v
        rw [map_sum]
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [map_smul, smul_eq_mul]
      rw [hw, h1]
      refine Finset.sum_congr rfl fun Z _ => ?_
      rw [h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Z' _ => ?_
      rw [lem_singular_factorization c h0 d _ hT _ ℓ hy0 m Z Z']
    have hR : P0.eval d * P1.eval d =
        ∑ Z : Nat.Partition m, ∑ Z' : Nat.Partition m, y1 Z * (y1 Z' *
          (pairing c h0 d (pbwCoord ℓ y0) (pbwCoord ℓ y0) * torus c (h0 + (ℓ : ℂ)) d m Z Z')) := by
      rw [← hP1 d, ← hP0 d, ← primary_pbwCoord hT ℓ]
      show _ * (y1 ⬝ᵥ (torus c (h0 + (ℓ : ℂ)) d m).mulVec y1) = _
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Z _ => ?_
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun Z' _ => ?_
      ring
    rw [← primary_pbwCoord hT (ℓ + m), hz, hL, hR]
  have hpoly : torusPolyForm c h0 z = P0 * P1 :=
    torusPolyForm_of_eval fun d => by rw [hstar d, eval_mul]
  have hP0' : torusPolyForm c h0 y0 = P0 := torusPolyForm_of_eval hP0
  have hP1' : torusPolyForm c (h0 + (ℓ : ℂ)) y1 = P1 := torusPolyForm_of_eval hP1
  have hz1 : z (onesPartition (ℓ + m)) ^ 2 = 1 := by
    have ht0 := torusPolyForm_top c h0 ℓ y0
    have ht1 := torusPolyForm_top c (h0 + (ℓ : ℂ)) m y1
    rw [hP0'] at ht0
    rw [hP1'] at ht1
    rw [← (torusPolyForm_top c h0 (ℓ + m) z).2, hpoly, Nat.mul_add,
      coeff_mul_add_eq_of_natDegree_le ht0.1 ht1.1, ht0.2, ht1.2, hy01, hy11]
    norm_num
  have hz0 : z (onesPartition (ℓ + m)) ≠ 0 := by
    intro h0'
    rw [h0'] at hz1
    norm_num at hz1
  have hzs : IsSingular (pbwCoord (c := c) (h := h0) (ℓ + m) z) (ℓ + m) := by
    refine ⟨fun h0' => ?_, ?_, fun k hk => ?_⟩
    · have := congrFun (pbwCoord_injective (ℓ + m) (h0'.trans (map_zero _).symm))
        (onesPartition (ℓ + m))
      exact hz0 this
    · rw [hz, ← hjL, hy1.2.1, map_smul]
      congr 1
      push_cast
      ring
    · rw [hz, ← hjL, hy1.2.2 k hk, map_zero]
  rw [tau_eq_of_singular hU rfl rfl z hz1 hzs x hx1 hx, hpoly]

/-- The factorization for even `k` (paper.tex l.1439–1440). -/
theorem tau_even (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) {p p' r s : ℕ}
    {b : ℂ} (hset : MinimalSetting p p' r s b) {k : ℕ} (ε : Bool) (hk1 : 1 ≤ k)
    (hk : k % 2 = 0)
    (x : Nat.Partition (ellOrb p p' r s ε k) → ℂ) (hx1 : x (onesPartition _) = 1)
    (hx : IsSingular (pbwCoord (c := kacC b) (h := kacH r s b) (ellOrb p p' r s ε k) x)
      (ellOrb p p' r s ε k)) :
    torusPolyForm (kacC b) (kacH r s b) x =
      genPpoly (r + (k / 2 - 1) * p) (s + (k / 2 - 1) * p') b *
        (if ε then genPpoly ((k - 1) * p + r) (p' - s) b
          else genPpoly (p - r) ((k - 1) * p' + s) b) := by
  have hb0 := minimal_b_ne hset
  have hset' := hset
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := hset
  obtain ⟨j, hj1, rfl⟩ : ∃ j, 1 ≤ j ∧ k = 2 * j := ⟨k / 2, by omega, by omega⟩
  have hkj : 2 * j / 2 = j := by omega
  have hk0 : 2 * j ≠ 0 := by omega
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hp'0 : (p' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [hkj]
  obtain ⟨y0, hy01, hy0s, hy0v⟩ := exists_chiT hH hb0 (r + (j - 1) * p) (s + (j - 1) * p')
    (by omega) (by omega)
  have hh0 : kacH ((r + (j - 1) * p : ℕ) : ℤ) ((s + (j - 1) * p' : ℕ) : ℤ) b = kacH r s b := by
    rw [kacH_min' hset', kacH_min' hset']
    push_cast [Nat.cast_sub hj1]
    ring
  cases ε with
  | true =>
    obtain ⟨y1, hy11, hy1s, hy1v⟩ := exists_chiT hH hb0 ((2 * j - 1) * p + r) (p' - s)
      (by omega) (by omega)
    have hh : kacH (((2 * j - 1) * p + r : ℕ) : ℤ) ((p' - s : ℕ) : ℤ) b =
        kacH r s b + (((r + (j - 1) * p) * (s + (j - 1) * p') : ℕ) : ℂ) := by
      rw [kacH_min' hset', kacH_min' hset']
      push_cast [Nat.cast_sub hj1, Nat.cast_sub hsp.le, Nat.cast_sub (show 1 ≤ 2 * j by omega)]
      field_simp
      ring
    have hn : (r + (j - 1) * p) * (s + (j - 1) * p') + ((2 * j - 1) * p + r) * (p' - s) =
        ellOrb p p' r s true (2 * j) := by
      have e : (((r + (j - 1) * p) * (s + (j - 1) * p') + ((2 * j - 1) * p + r) * (p' - s) : ℕ) :
          ℤ) = (j : ℤ) * ((j : ℤ) * p * p' + ((p' : ℤ) * r - (p : ℤ) * s)) := by
        push_cast [Nat.cast_sub hj1, Nat.cast_sub hsp.le, Nat.cast_sub (show 1 ≤ 2 * j by omega)]
        ring
      simp only [ellOrb, ellPlus, if_neg hk0, Nat.mul_mod_right, if_true, hkj]
      rw [← e, Int.toNat_natCast]
    rw [if_pos rfl]
    exact tau_push hU hh0 y0 hy01 hy0s hy0v hh y1 hy11 hy1s hy1v hn x hx1 hx
  | false =>
    obtain ⟨y1, hy11, hy1s, hy1v⟩ := exists_chiT hH hb0 (p - r) ((2 * j - 1) * p' + s)
      (by omega) (by omega)
    have hh : kacH ((p - r : ℕ) : ℤ) (((2 * j - 1) * p' + s : ℕ) : ℤ) b =
        kacH r s b + (((r + (j - 1) * p) * (s + (j - 1) * p') : ℕ) : ℂ) := by
      rw [kacH_min' hset', kacH_min' hset']
      push_cast [Nat.cast_sub hj1, Nat.cast_sub hrp.le, Nat.cast_sub (show 1 ≤ 2 * j by omega)]
      field_simp
      ring
    have hn : (r + (j - 1) * p) * (s + (j - 1) * p') + (p - r) * ((2 * j - 1) * p' + s) =
        ellOrb p p' r s false (2 * j) := by
      have e : (((r + (j - 1) * p) * (s + (j - 1) * p') + (p - r) * ((2 * j - 1) * p' + s) : ℕ) :
          ℤ) = (j : ℤ) * ((j : ℤ) * p * p' - ((p' : ℤ) * r - (p : ℤ) * s)) := by
        push_cast [Nat.cast_sub hj1, Nat.cast_sub hrp.le, Nat.cast_sub (show 1 ≤ 2 * j by omega)]
        ring
      simp only [ellOrb, ellMinus, if_neg hk0, Nat.mul_mod_right, if_true, hkj]
      rw [← e, Int.toNat_natCast]
      simp
    rw [if_neg (by simp)]
    exact tau_push hU hh0 y0 hy01 hy0s hy0v hh y1 hy11 hy1s hy1v hn x hx1 hx

/-- The factorization of `τ^±_k` (paper.tex l.1433–1446), from the normalization identities
behind Lemma 6.6 and the uniqueness of singular vectors. -/
theorem sub_tau_factorization (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) :
    Stmt_sub_tau_factorization := by
  intro p p' r s b hset k ε hk x hx1 hx
  exact ⟨fun hodd => tau_odd hH hU hset ε hodd x hx1 hx,
    fun heven => tau_even hH hU hset ε hk heven x hx1 hx⟩

example (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique) :
    Stmt_sub_tau_factorization := sub_tau_factorization hH hU

end Virasoro
