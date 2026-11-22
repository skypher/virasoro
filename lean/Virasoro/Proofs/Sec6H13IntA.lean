import Virasoro.Proofs.Sec6H13SpecK
import Virasoro.Proofs.Sec6FockInt
import Virasoro.Proofs.Sec6H13Local
import Virasoro.Proofs.Sec6H13Laurent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Proposition 6.8(i), integrality: determinants and units (paper.tex l.1270–1287)

The Kac determinant at a point of a field of characteristic zero in the variable `t = b²`; the
factors `Δ − h_{u,v}` are units at `𝔭`; determinants and adjugates of matrices with entries in a
subring; the two frozen combinatorial statements used by the proof.
-/

namespace Virasoro

open Polynomial

/-- Frozen sub-statement of Proposition 6.8(i) (paper.tex l.1283–1285): "By Lagrange's theorem
for the centralizer of cycle type `λ` in `S_M`, `∏_n m_n! n^{m_n} ∣ M!`".
Demand sheet: for every `N` and `λ ⊢ N`, the entry `D_λ = (−1)^{ℓ(λ)} ∏_n m_n! n^{m_n}` of
`D_N` (`TFock.Dm`) divides `N!` in `ℤ`; used as `M! D_M⁻¹ ∈ Mat(ℤ)` (l.1285). -/
def Stmt_sub_h13_lagrange : Prop :=
  ∀ (N : ℕ) (Z : Nat.Partition N), TFock.Dm Z ∣ (N.factorial : ℤ)

/-- Frozen sub-statement of Proposition 6.8(i) (paper.tex l.1270–1271):
"`|det D_M| = 2^{−∑_λ ℓ(λ)} K_M`", with `K_M = ∏_λ K_λ` the constant of the determinant formula
(l.1257, `kacK`) and `∑_λ ℓ(λ)` = `lenSum`.
Demand sheet: for every `N`, an identity of integers; used to get
`det B_M(q₀,2q₀−α) det B_M(q₀,α) = ± 2^{∑ℓ(λ)} ∏ (Δ − h_{u,v})^{p(M−uv)}` (l.1272–1274). -/
def Stmt_sub_h13_detD : Prop :=
  ∀ N : ℕ, (kacK N : ℤ) = 2 ^ lenSum N * |∏ Z : Nat.Partition N, TFock.Dm Z|

/-- The Kac determinant at a point, in the variable `t = b²`. -/
theorem kac_det_T {K : Type} [Field K] [CharZero K] (hK : Cited_KacDeterminant) {t : K}
    (ht : t ≠ 0) (z : K) (n : ℕ) :
    (gram (cT t) z n).det = (kacK n : K) *
      ∏ a ∈ labels n, (z - hT (a.1 : ℤ) (a.2 : ℤ) t) ^ Fintype.card (Nat.Partition (n - a.lvl)) := by
  let ι : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  obtain ⟨b, hb2⟩ := IsAlgClosed.exists_pow_nat_eq (ι t) (n := 2) (by norm_num)
  have ht' : ι t ≠ 0 := (map_ne_zero ι).2 ht
  have hb : b ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hb2
    exact ht' hb2.symm
  have hc : kacC b = ι (cT t) := by
    simp only [kacC, cT, map_add, map_mul, map_div₀, map_ofNat]
    rw [← hb2]
    field_simp
    ring
  have hh : ∀ a : Label, kacHL a b = ι (hT (a.1 : ℤ) (a.2 : ℤ) t) := by
    intro a
    simp only [kacHL, kacH, hT, map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one,
      map_intCast]
    rw [← hb2]
    field_simp
  have h1 := congrArg (Polynomial.eval (ι z)) (kac_det_const hK hb n)
  have e1 : (gramPoly (kacC b) n).det.eval (ι z) = ι (gram (cT t) z n).det := by
    rw [← coe_evalRingHom, RingHom.map_det, RingHom.mapMatrix_apply, coe_evalRingHom,
      gramPoly_eval, hc, gram_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [e1] at h1
  apply ι.injective
  rw [h1, eval_mul, eval_C, kacProd, eval_prod, map_mul, map_natCast, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [eval_pow, eval_sub, eval_X, eval_C, hh, map_pow, map_sub]

/-! ### Determinants and adjugates over a subring -/

theorem det_mem {R : Type*} [CommRing R] (S : Subring R) {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n R) (h : ∀ i j, A i j ∈ S) : A.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

theorem adjugate_mem {R : Type*} [CommRing R] (S : Subring R) {n : Type*} [Fintype n]
    [DecidableEq n] (A : Matrix n n R) (h : ∀ i j, A i j ∈ S) (i j : n) : A.adjugate i j ∈ S := by
  rw [Matrix.adjugate_apply]
  refine det_mem S _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    exacts [S.one_mem, S.zero_mem]
  · exact h a b

theorem mul_mem_entries {R : Type*} [CommRing R] (S : Subring R) {n : Type*} [Fintype n]
    (A B : Matrix n n R) (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) (i j : n) :
    (A * B) i j ∈ S := by
  rw [Matrix.mul_apply]
  exact S.sum_mem fun k _ => S.mul_mem (hA i k) (hB k j)

/-! ### The point `(t, Δ)` of `ℚ(s)(α)` -/

open H13Local

theorem half_K0 : TFock.half K0 = 1 / 2 := by
  unfold TFock.half
  rw [map_div₀, map_one, map_ofNat]

theorem wt_K0 : TFock.wt aK qK = DK := by
  unfold TFock.wt DK
  rw [half_K0]

theorem c_K0 : 1 - 12 * qK ^ 2 = cT tK := by
  have hs := sK_ne_zero
  unfold qK cT tK
  field_simp
  ring

theorem hT_mem (u v : ℤ) : hT u v tK ∈ S0 := by
  have h : hT u v tK = ((tK + 1) ^ 2 - ((u : K0) * tK + (v : K0)) ^ 2) * (1 / 2) * (1 / 2) * tK⁻¹ := by
    unfold hT
    field_simp [tK_ne_zero]
    ring
  rw [h]
  exact S0.mul_mem (S0.mul_mem (S0.mul_mem (S0.sub_mem (S0.pow_mem (S0.add_mem tK_mem S0.one_mem) 2)
    (S0.pow_mem (S0.add_mem (S0.mul_mem (intCast_mem S0 u) tK_mem) (intCast_mem S0 v)) 2))
    half_mem) half_mem) tK_inv_mem

theorem two_mem : (2 : K0) ∈ S0 := by
  rw [show (2 : K0) = 1 + 1 by norm_num]
  exact S0.add_mem S0.one_mem S0.one_mem

theorem cT_mem : cT tK ∈ S0 := by
  have h : cT tK = (13 : ℕ) + (6 : ℕ) * tK + (6 : ℕ) * tK⁻¹ := by
    unfold cT
    push_cast
    ring
  rw [h]
  exact S0.add_mem (S0.add_mem (natCast_mem S0 13) (S0.mul_mem (natCast_mem S0 6) tK_mem))
    (S0.mul_mem (natCast_mem S0 6) tK_inv_mem)

theorem dvalK_mem (ν : Fin 2) : dvalK ν tK ∈ S0 := by
  unfold dvalK
  split_ifs
  · rw [div_eq_mul_inv]
    exact S0.sub_mem (S0.neg_mem S0.one_mem) (S0.mul_mem two_mem tK_inv_mem)
  · rw [div_eq_mul_inv]
    exact S0.sub_mem two_mem (S0.mul_mem two_mem tK_inv_mem)

/-- `ℤ[s] → ℚ(s)(α)`. -/
noncomputable def iotaC : Polynomial ℤ →+* K0 := iota.comp C

theorem iotaC_X : iotaC X = sK := rfl

theorem iotaC_C (z : ℤ) : iotaC (C z) = (z : K0) := iota_CC z

/-- `8 s³ (Δ − h_{u,v})` as an element of `ℤ[s][α]`. -/
noncomputable def auv (u v : ℤ) : PZ :=
  C (C 4 * X ^ 3) * X ^ 2 + C (C 4 * X ^ 4 - C 8 * X ^ 2) * X +
    C (X * ((C 2 - X ^ 2) ^ 2 - (C (2 * v) - C u * X ^ 2) ^ 2))

theorem auv_eq (u v : ℤ) : (DK - hT u v tK) * iota ts ^ 3 = iota (auv u v) := by
  have hs := sK_ne_zero
  have e : iota (auv u v) = 4 * sK ^ 3 * aK ^ 2 + (4 * sK ^ 4 - 8 * sK ^ 2) * aK +
      sK * ((2 - sK ^ 2) ^ 2 - (2 * (v : K0) - (u : K0) * sK ^ 2) ^ 2) := by
    have h1 : ∀ p : Polynomial ℤ, iota (C p) = iotaC p := fun _ => rfl
    have h2 : iota X = aK := rfl
    simp only [auv, map_add, map_mul, map_pow, h1, h2, map_sub, iotaC_X, iotaC_C]
    push_cast
    ring
  rw [e, iota_ts]
  unfold DK hT tK qK
  field_simp
  ring

/-- `Δ − h_{u,v}` is a unit at `𝔭`: its `α²`-coefficient is a power of `2` times a power of `s`
(paper.tex l.1274–1281). -/
theorem unit_factor (ℓ : ℕ) [Fact ℓ.Prime] (h2 : ℓ ≠ 2) (u v : ℤ) :
    Unit0 ℓ (DK - hT u v tK) := by
  refine ⟨3, auv u v, auv_eq u v, ?_⟩
  intro h
  have h4 : (4 : ZMod ℓ) ≠ 0 := by
    have : (4 : ZMod ℓ) = 2 ^ 2 := by norm_num
    rw [this]
    exact pow_ne_zero _ (two_ne_zero_zmod ℓ h2)
  have hc2 : (red ℓ (auv u v)).coeff 2 = C 4 * X ^ 3 := by
    simp only [red, auv, coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow, map_X, map_C]
    rw [coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, if_pos rfl,
      if_neg (by norm_num), if_neg (by norm_num), add_zero, add_zero]
    simp
  have hc : ((red ℓ (auv u v)).coeff 2).coeff 3 = 4 := by
    rw [hc2, coeff_C_mul_X_pow, if_pos rfl]
  rw [h, coeff_zero, coeff_zero] at hc
  exact h4 hc.symm

theorem unit_two (ℓ : ℕ) [Fact ℓ.Prime] (h2 : ℓ ≠ 2) : Unit0 ℓ (2 : K0) := by
  refine ⟨0, C (C 2), ?_, ?_⟩
  · rw [pow_zero, mul_one, iota_CC]
    norm_num
  · have : red ℓ (C (C 2)) = C (C 2) := by
      simp [red]
      exact (map_ofNat C 2).symm
    rw [this]
    exact C_ne_zero.2 (C_ne_zero.2 (two_ne_zero_zmod ℓ h2))

theorem unit_neg (ℓ : ℕ) [Fact ℓ.Prime] {x : K0} (hx : Unit0 ℓ x) : Unit0 ℓ (-x) := by
  obtain ⟨n, a, ha, ha'⟩ := hx
  exact ⟨n, -a, by rw [map_neg, ← ha]; ring, by rw [map_neg]; exact neg_ne_zero.2 ha'⟩

end Virasoro
