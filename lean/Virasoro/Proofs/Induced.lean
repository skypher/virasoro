import Virasoro.Proofs.NegAlg

/-!
# The Virasoro action on `U(Vir_-)`

For `c, h : R`, all modes `L_k` (`k : ℤ`) are constructed as operators on `U(Vir_-)`, with
`L_{-m}` acting by left multiplication with `g m`, `L_k 1 = 0` for `k > 0` and `L_0 1 = h`.
The operators are obtained from the universal property of `U(Vir_-)`: the map
`u ↦ (u, (L_k u)_{k ∈ ℤ})` is the orbit map of the representation of `Vir_-` on
`U(Vir_-) × (ℤ → U(Vir_-))` given by the commutation rule
`L_k L_{-m} = L_{-m} L_k + (k + m) L_{k-m} + c/12 (k^3 - k) δ_{k,m}`.
-/

namespace Virasoro

open NegEnv

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The operator on pairs `(u, (L_k u)_k)` induced by left multiplication with `g m`. -/
noncomputable def Etil0 (c : R) (m : ℤ) :
    Module.End R (NegEnv R × (ℤ → NegEnv R)) where
  toFun p := (g R m * p.1, fun k =>
    g R m * p.2 k + ((k + m : ℤ) : R) • p.2 (k - m) + ct c k m • p.1)
  map_add' p q := by
    ext
    · simp [mul_add]
    · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, mul_add, smul_add]
      abel
  map_smul' r p := by
    ext
    · simp
    · simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, mul_smul_comm, smul_add,
        RingHom.id_apply]
      rw [smul_comm r, smul_comm r]

/-- The representation of `Vir_-` on pairs `(u, (L_k u)_k)`. -/
noncomputable def Etil (c : R) (m : ℤ) : Module.End R (NegEnv R × (ℤ → NegEnv R)) :=
  if 0 < m then Etil0 c m else 0

theorem ct_cocycle (c : R) (k m n : ℤ) :
    ((k + m : ℤ) : R) * ct c (k - m) n - ((k + n : ℤ) : R) * ct c (k - n) m
      = ((n - m : ℤ) : R) * ct c k (m + n) := by
  unfold ct
  by_cases hk : k = m + n
  · subst hk
    rw [if_pos (by ring), if_pos (by ring), if_pos rfl]
    have := centralTerm_cocycle c m n
    rw [show m + n - m = n by ring, show m + n - n = m by ring,
      show m + n + m = 2 * m + n by ring, show m + n + n = 2 * n + m by ring]
    exact this
  · rw [if_neg (by omega), if_neg (by omega), if_neg hk]
    simp

theorem isNegRep_Etil (c : R) : IsNegRep (Etil c) where
  nonpos m hm := by rw [Etil, if_neg (by omega)]
  comm m n hm hn := by
    rw [Etil, Etil, Etil, if_pos hm, if_pos hn, if_pos (by omega)]
    refine LinearMap.ext fun p => Prod.ext ?_ (funext fun k => ?_)
    · simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Etil0,
        LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.smul_fst]
      exact g_mul_g_mul hm hn p.1
    · simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Etil0,
        LinearMap.coe_mk, AddHom.coe_mk, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
        Pi.smul_apply, mul_add, mul_smul_comm]
      have e1 := g_mul_g_mul hm hn (p.2 k)
      have e2 := ct_cocycle c k m n
      have i1 : k - m - n = k - (m + n) := by ring
      have i2 : k - n - m = k - (m + n) := by ring
      rw [i1, i2]
      push_cast at e2 ⊢
      linear_combination (norm := module) e1 + e2 • p.1

variable (c h : R)

/-- The values `L_k 1`: `g (-k)` for `k < 0`, `h` for `k = 0`, zero for `k > 0`. -/
noncomputable def F0 (h : R) : ℤ → NegEnv R :=
  fun k => g R (-k) + (if k = 0 then h else 0) • (1 : NegEnv R)

/-- The map `u ↦ (u, (L_k u)_k)`. -/
noncomputable def LamMap : NegEnv R →ₗ[R] NegEnv R × (ℤ → NegEnv R) :=
  orbit (Etil c) (isNegRep_Etil c) (1, F0 h)

theorem LamMap_one : LamMap c h 1 = (1, F0 h) := orbit_one _ _ _

theorem LamMap_g_mul {m : ℤ} (hm : 0 < m) (u : NegEnv R) :
    LamMap c h (g R m * u) = Etil0 c m (LamMap c h u) := by
  rw [LamMap, orbit_g_mul, Etil, if_pos hm]

theorem LamMap_fst (u : NegEnv R) : (LamMap c h u).1 = u := by
  refine induction_left (P := fun u => (LamMap c h u).1 = u) ?_ ?_ ?_ ?_ u
  · rw [LamMap_one]
  · intro a b ha hb
    rw [map_add, Prod.fst_add, ha, hb]
  · intro r a ha
    rw [map_smul, Prod.smul_fst, ha]
  · intro m hm a ha
    rw [LamMap_g_mul c h hm]
    show g R m * (LamMap c h a).1 = _
    rw [ha]

/-- The mode `L_k` on `U(Vir_-)`. -/
noncomputable def Lop (k : ℤ) : NegEnv R →ₗ[R] NegEnv R :=
  (LinearMap.proj k) ∘ₗ (LinearMap.snd R (NegEnv R) (ℤ → NegEnv R)) ∘ₗ LamMap c h

theorem Lop_apply (k : ℤ) (u : NegEnv R) : Lop c h k u = (LamMap c h u).2 k := rfl

theorem Lop_one (k : ℤ) : Lop c h k 1 = F0 h k := by rw [Lop_apply, LamMap_one]

/-- `L_k L_{-m} = L_{-m} L_k + (k + m) L_{k-m} + c/12 (k^3 - k) δ_{k,m}` on `U(Vir_-)`. -/
theorem Lop_g_mul {m : ℤ} (hm : 0 < m) (k : ℤ) (u : NegEnv R) :
    Lop c h k (g R m * u)
      = g R m * Lop c h k u + ((k + m : ℤ) : R) • Lop c h (k - m) u + ct c k m • u := by
  rw [Lop_apply, LamMap_g_mul c h hm]
  show g R m * (LamMap c h u).2 k + ((k + m : ℤ) : R) • (LamMap c h u).2 (k - m)
    + ct c k m • (LamMap c h u).1 = _
  rw [LamMap_fst]
  rfl

/-- Negative modes act by left multiplication. -/
theorem Lop_neg (u : NegEnv R) : ∀ k : ℤ, k < 0 → Lop c h k u = g R (-k) * u := by
  refine induction_left (P := fun u => ∀ k : ℤ, k < 0 → Lop c h k u = g R (-k) * u)
    ?_ ?_ ?_ ?_ u
  · intro k hk
    rw [Lop_one, F0, if_neg (by omega), zero_smul, add_zero, mul_one]
  · intro a b ha hb k hk
    rw [map_add, ha k hk, hb k hk, mul_add]
  · intro r a ha k hk
    rw [map_smul, ha k hk, mul_smul_comm]
  · intro m hm a ha k hk
    rw [Lop_g_mul c h hm, ha k hk, ha (k - m) (by omega), ct, if_neg (by omega), zero_smul,
      add_zero]
    have e := g_mul_g_mul (show 0 < -k by omega) hm a
    rw [e, show -(k - m) = -k + m by ring]
    push_cast
    module

theorem Lop_one_nonneg {k : ℤ} (hk : 0 ≤ k) :
    Lop c h k 1 = (if k = 0 then h else 0) • (1 : NegEnv R) := by
  rw [Lop_one, F0, g_nonpos (by omega), zero_add]

theorem ct_antisymm (j k : ℤ) : ct c k (-j) = -ct c j (-k) := by
  unfold ct
  by_cases hjk : k = -j
  · subst hjk
    rw [if_pos rfl, if_pos (by ring), centralTerm_neg]
  · rw [if_neg hjk, if_neg (by omega), neg_zero]

/-- The Virasoro relation between `L_j` and `L_k` on the element `u`. -/
def Vrel (j k : ℤ) (u : NegEnv R) : Prop :=
  Lop c h j (Lop c h k u)
    = Lop c h k (Lop c h j u) + ((j - k : ℤ) : R) • Lop c h (j + k) u + ct c j (-k) • u

theorem vrel_symm {j k : ℤ} {u : NegEnv R} (hu : Vrel c h j k u) : Vrel c h k j u := by
  unfold Vrel at *
  rw [hu, ct_antisymm, show k + j = j + k by ring]
  push_cast
  module

theorem vrel_neg {j : ℤ} (hj : j < 0) (k : ℤ) (u : NegEnv R) : Vrel c h j k u := by
  unfold Vrel
  rw [Lop_neg c h _ j hj, Lop_neg c h u j hj, Lop_g_mul c h (show 0 < -j by omega),
    ct_antisymm c k j, show k - -j = j + k by ring]
  push_cast
  module

theorem vrel_one {j k : ℤ} (hj : 0 ≤ j) (hk : 0 ≤ k) : Vrel c h j k 1 := by
  unfold Vrel
  rw [Lop_one_nonneg c h hj, Lop_one_nonneg c h hk, map_smul, map_smul,
    Lop_one_nonneg c h hj, Lop_one_nonneg c h hk, Lop_one_nonneg c h (by omega)]
  by_cases h0 : j = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [ct, centralTerm]
  · have hjk : ¬ j + k = 0 := by omega
    have hjk2 : ¬ j = -k := by omega
    rw [if_neg hjk, ct, if_neg hjk2]
    simp only [zero_smul, smul_zero, add_zero]
    rw [smul_comm]

theorem vrel_step {m : ℤ} (hm : 0 < m) (u : NegEnv R) (hu : ∀ j k, Vrel c h j k u) :
    ∀ j k, Vrel c h j k (g R m * u) := by
  intro j k
  have I1 := hu j k
  have I2 := hu (j - m) k
  have I3 := hu j (k - m)
  unfold Vrel at *
  have I1' : g R m * Lop c h j (Lop c h k u) = g R m * Lop c h k (Lop c h j u)
      + ((j - k : ℤ) : R) • (g R m * Lop c h (j + k) u) + ct c j (-k) • (g R m * u) := by
    rw [I1, mul_add, mul_add, mul_smul_comm, mul_smul_comm]
  have hcen : ((j + m : ℤ) : R) * ct c (j - m) (-k) + ((k + m : ℤ) : R) * ct c j (-(k - m))
      = ((j - k : ℤ) : R) * ct c (j + k) m := by
    unfold ct
    by_cases hmjk : j + k = m
    · subst hmjk
      rw [if_pos (by ring), if_pos (by ring), if_pos rfl,
        show j - (j + k) = -k by ring, centralTerm_neg]
      have := centralTerm_cocycle c k j
      rw [show k + j = j + k by ring] at this
      rw [← this]
      push_cast
      ring
    · rw [if_neg (by omega), if_neg (by omega), if_neg hmjk]
      simp
  simp only [Lop_g_mul c h hm, map_add, map_smul]
  rw [show j - m + k = j + k - m by ring] at I2
  rw [show j + (k - m) = j + k - m by ring] at I3
  push_cast at I1' I2 I3 hcen ⊢
  linear_combination (norm := module) I1' + ((j : R) + m) • I2 + ((k : R) + m) • I3 + hcen • u

/-- The Virasoro relation holds on `U(Vir_-)`. -/
theorem vrel_all (u : NegEnv R) : ∀ j k, Vrel c h j k u := by
  refine induction_left (P := fun u => ∀ j k, Vrel c h j k u) ?_ ?_ ?_ ?_ u
  · intro j k
    by_cases hj : j < 0
    · exact vrel_neg c h hj k 1
    by_cases hk : k < 0
    · exact vrel_symm c h (vrel_neg c h hk j 1)
    exact vrel_one c h (by omega) (by omega)
  · intro a b ha hb j k
    have h1 := ha j k
    have h2 := hb j k
    unfold Vrel at *
    simp only [map_add, h1, h2, smul_add]
    abel
  · intro r a ha j k
    have h1 := ha j k
    unfold Vrel at *
    simp only [map_smul, h1, smul_add]
    rw [smul_comm r, smul_comm r]
  · intro m hm a ha
    exact vrel_step c h hm a ha

theorem Lop_comm (j k : ℤ) (u : NegEnv R) :
    Lop c h j (Lop c h k u) = Lop c h k (Lop c h j u) + ((j - k : ℤ) : R) • Lop c h (j + k) u
      + (if j + k = 0 then centralTerm c j • u else 0) := by
  have := vrel_all c h u j k
  unfold Vrel at this
  rw [this, ct]
  congr 1
  by_cases hjk : j + k = 0
  · rw [if_pos hjk, if_pos (by omega)]
  · rw [if_neg hjk, if_neg (by omega), zero_smul]

end Virasoro
