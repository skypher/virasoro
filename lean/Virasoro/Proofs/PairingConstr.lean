import Virasoro.Proofs.PairingVac

/-!
# Construction of the primary pairing

The matrix elements `T(u, v) = ⟨u| V_d(1) |v⟩` of a primary field of weight `d` are constructed
from the freeness of the Verma module over `U(Vir_-)`.  The bilinear maps
`(p, v) ↦ T(p(L_0) u, v)` form a representation of `Vir_-`, with `L_{-n}` acting by
`(𝔅_n β)(p, v) = β(p(X + n), (L_n - L_0 + n d) v) + β(X p(X + n), v)`,
which is the Ward identity
`T(L_{-n} u, v) = T(u, (L_n - L_0 + n d) v) + T(L_0 u, v)`.
-/

namespace Virasoro

open Polynomial

variable {R : Type*} [CommRing R] [Algebra ℚ R] {c h : R} (d : R)

namespace Verma

/-- The operator `𝔯_n = L_n - L_0 + n d`. -/
noncomputable def rr (n : ℤ) : Verma R c h →ₗ[R] Verma R c h :=
  L n - L 0 + ((n : R) * d) • LinearMap.id

theorem rr_apply (n : ℤ) (v : Verma R c h) :
    rr d n v = L n v - L 0 v + ((n : R) * d) • v := rfl

theorem rr_zero (v : Verma R c h) : rr d 0 v = 0 := by
  rw [rr_apply, sub_self, Int.cast_zero, zero_mul, zero_smul, add_zero]

/-- `[𝔯_b, 𝔯_a] = (b - a) 𝔯_{a+b} - b 𝔯_b + a 𝔯_a + c/12 (b^3 - b) δ_{a+b,0}`. -/
theorem rr_comm (a b : ℤ) (v : Verma R c h) :
    rr d b (rr d a v) = rr d a (rr d b v) + ((b - a : ℤ) : R) • rr d (a + b) v
      - (b : R) • rr d b v + (a : R) • rr d a v + ct c b (-a) • v := by
  have e1 := L_L_ct (c := c) (h := h) a b v
  have e2 := L_L_zero (c := c) (h := h) b v
  have e3 := L_L_zero (c := c) (h := h) a v
  simp only [rr_apply, map_add, map_sub, map_smul]
  push_cast at e1 ⊢
  linear_combination (norm := module) e1 - e2 + e3

/-- The operator `𝔅_n` on bilinear maps `β(p, v)`. -/
noncomputable def Bop (n : ℤ) : Module.End R (R[X] →ₗ[R] Verma R c h →ₗ[R] R) where
  toFun β := (β ∘ₗ taylor (n : R)).compl₂ (rr d n)
    + β ∘ₗ ((LinearMap.mulLeft R (X : R[X])) ∘ₗ taylor (n : R))
  map_add' β β' := by
    refine LinearMap.ext fun p => LinearMap.ext fun v => ?_
    simp only [LinearMap.add_apply, LinearMap.compl₂_apply, LinearMap.comp_apply]
    ring
  map_smul' r β := by
    refine LinearMap.ext fun p => LinearMap.ext fun v => ?_
    simp only [LinearMap.add_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem Bop_apply (n : ℤ) (β : R[X] →ₗ[R] Verma R c h →ₗ[R] R) (p : R[X]) (v : Verma R c h) :
    Bop d n β p v = β (taylor (n : R) p) (rr d n v) + β (X * taylor (n : R) p) v := rfl

theorem Bop_comm_aux (a b : ℤ) (β : R[X] →ₗ[R] Verma R c h →ₗ[R] R) (p : R[X])
    (v : Verma R c h) :
    Bop d a (Bop d b β) p v = Bop d b (Bop d a β) p v
      + ((b - a : ℤ) : R) * Bop d (a + b) β p v
      + ct c b (-a) * β (taylor ((a : R) + b) p) v := by
  simp only [Bop_apply, taylor_mul, taylor_X, taylor_taylor]
  rw [add_comm (b : R) (a : R), show ((a + b : ℤ) : R) = (a : R) + b by push_cast; rfl]
  generalize taylor ((a : R) + b) p = q
  have e1 : (X + C (b : R)) * q = X * q + (b : R) • q := by rw [smul_eq_C_mul]; ring
  have e2 : (X + C (a : R)) * q = X * q + (a : R) • q := by rw [smul_eq_C_mul]; ring
  rw [e1, e2, rr_comm d a b v]
  simp only [mul_add, mul_smul_comm, map_add, map_sub, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- `𝔅_a 𝔅_b = 𝔅_b 𝔅_a + (b - a) 𝔅_{a+b} + c/12 (b^3 - b) δ_{a+b,0}`. -/
theorem Bop_comm (a b : ℤ) (β : R[X] →ₗ[R] Verma R c h →ₗ[R] R) :
    Bop d a (Bop d b β) = Bop d b (Bop d a β) + ((b - a : ℤ) : R) • Bop d (a + b) β
      + ct c b (-a) • β := by
  refine LinearMap.ext fun p => LinearMap.ext fun v => ?_
  rw [Bop_comm_aux]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  by_cases hab : b = -a
  · subst hab
    rw [show (a : R) + ((-a : ℤ) : R) = 0 by push_cast; ring, taylor_zero]
  · rw [ct, if_neg hab, zero_mul, zero_mul]

theorem Bop_rep (m n : ℤ) (hm : 0 < m) (hn : 0 < n) :
    (Bop d m : Module.End R (R[X] →ₗ[R] Verma R c h →ₗ[R] R)) * Bop d n
      = Bop d n * Bop d m + ((n - m : ℤ) : R) • Bop d (m + n) := by
  refine LinearMap.ext fun β => ?_
  rw [Module.End.mul_apply, Bop_comm, ct, if_neg (by omega), zero_smul, add_zero]
  rfl

variable (c h)

/-- The bilinear map `(p, v) ↦ p(h) ⟨h|V_d(1)|v⟩`. -/
noncomputable def beta0 : R[X] →ₗ[R] Verma R c h →ₗ[R] R :=
  (leval h).smulRight (phiVac c h d)

/-- The map `u ↦ ((p, v) ↦ ⟨p(L_0) u| V_d(1) |v⟩)`. -/
noncomputable def PsiMap : Verma R c h →ₗ[R] (R[X] →ₗ[R] Verma R c h →ₗ[R] R) :=
  Classical.choose (exists_negHom (c := c) (h := h) (Bop (c := c) (h := h) d)
    (fun m n hm hn => Bop_rep d m n hm hn) (beta0 c h d))

variable {c h}

theorem beta0_apply (p : R[X]) (v : Verma R c h) :
    beta0 c h d p v = p.eval h * phiVac c h d v := rfl

theorem PsiMap_hw : PsiMap c h d hw = beta0 c h d :=
  (Classical.choose_spec (exists_negHom (c := c) (h := h) (Bop (c := c) (h := h) d)
    (fun m n hm hn => Bop_rep d m n hm hn) (beta0 c h d))).1

theorem PsiMap_neg {m : ℤ} (hm : 0 < m) (u : Verma R c h) :
    PsiMap c h d (L (-m) u) = Bop d m (PsiMap c h d u) :=
  (Classical.choose_spec (exists_negHom (c := c) (h := h) (Bop (c := c) (h := h) d)
    (fun m n hm hn => Bop_rep d m n hm hn) (beta0 c h d))).2 m hm u

theorem Bop_beta0 (n : ℤ) (hn : n ≤ 0) :
    Bop d n (beta0 c h d) = (if n = 0 then h else 0) • beta0 c h d := by
  refine LinearMap.ext fun p => LinearMap.ext fun v => ?_
  rw [Bop_apply, beta0_apply, beta0_apply, eval_mul, eval_X, LinearMap.smul_apply,
    LinearMap.smul_apply, beta0_apply, smul_eq_mul]
  by_cases h0 : n = 0
  · subst h0
    rw [rr_zero, map_zero, if_pos rfl, Int.cast_zero, taylor_zero]
    ring
  · rw [if_neg h0, rr_apply, map_add, map_sub, map_smul, smul_eq_mul]
    have e := phiVac_neg d (show 0 < -n by omega) v
    rw [neg_neg] at e
    rw [e]
    push_cast
    ring

/-- The Ward identity for all modes: `Ψ(L_{-n} u) = 𝔅_n Ψ(u)`. -/
theorem PsiMap_L (u : Verma R c h) : ∀ n : ℤ,
    PsiMap c h d (L (-n) u) = Bop d n (PsiMap c h d u) := by
  refine induction_L (P := fun u => ∀ n : ℤ,
    PsiMap c h d (L (-n) u) = Bop d n (PsiMap c h d u)) ?_ ?_ ?_ ?_ u
  · intro n
    by_cases hn : 0 < n
    · exact PsiMap_neg d hn hw
    · rw [PsiMap_hw, Bop_beta0 d n (by omega)]
      by_cases h0 : n = 0
      · subst h0
        rw [neg_zero, L_hw_zero, map_smul, PsiMap_hw, if_pos rfl]
      · rw [if_neg h0, zero_smul, L_hw_pos (by omega), map_zero]
  · intro u v hu hv n
    simp only [map_add, hu, hv]
  · intro r v hv n
    simp only [map_smul, hv]
  · intro k hk u hu n
    have e := L_L_ct (c := c) (h := h) (-k) (-n) u
    rw [e, map_add, map_add, map_smul, map_smul, PsiMap_neg d hk, hu n, PsiMap_neg d hk,
      Bop_comm d n k]
    have e2 : -k + -n = -(n + k) := by ring
    have e3 : -n - -k = k - n := by ring
    rw [e2, hu (n + k), neg_neg, ct_symm c (-n) k, e3]

variable (c h)

/-- The primary pairing `T(u, v) = ⟨u| V_d(1) |v⟩`. -/
noncomputable def pairing : Verma R c h →ₗ[R] Verma R c h →ₗ[R] R :=
  (LinearMap.applyₗ (1 : R[X])) ∘ₗ PsiMap c h d

variable {c h}

theorem pairing_apply (u v : Verma R c h) : pairing c h d u v = PsiMap c h d u 1 v := rfl

/-- Existence of the primary pairing. -/
theorem isPrimaryPairing_pairing : IsPrimaryPairing d (pairing c h d) := by
  constructor
  · rw [pairing_apply, PsiMap_hw, beta0_apply, eval_one, phiVac_hw, mul_one]
  · intro n u v
    have e1 := PsiMap_L d u n
    have e2 := PsiMap_L d u 0
    rw [neg_zero] at e2
    rw [pairing_apply, pairing_apply, pairing_apply, pairing_apply, pairing_apply, e1, e2]
    simp only [Bop_apply, taylor_one, C_1, rr_apply, map_add, map_sub, map_smul, smul_eq_mul]
    ring

end Verma

end Virasoro
