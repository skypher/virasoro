import Virasoro.Proofs.P2Sec13DiagRat
import Virasoro.Proofs.P2Sec11LayerSum2

/-!
# Lemma 13.1, Step 4: the diagonalized trace (paper.tex l.2990–2996)

"Diagonalize the symmetric matrix `B̄_{V,τ}` on the free `ℂ[[τ]]`-module `𝒱_N` by congruence,
`Uᵀ B̄ U = diag(τ^{e_a} u_a)`; since `J_τ^2 = 0`, every exponent `e_a` lies in `{0,1}`."

* `orth_trace`: the trace `∑ (G⁻¹)_{ij} P_{ji}` through an orthogonal basis is
  `∑_a u_a⁻¹ τ^{-e_a} P(v_a,v_a)`.
* `dvd_of_pairing`: on `ℂ^ι = A ⊕ B` with exact kernel lifts on `B`, divisibility of the pairings
  with `A` gives divisibility of `G V`.
* `e_le_one`: the exponents of the Gram matrix of `E` are `0` or `1`, and `e_a = 1` puts `v_a(0)`
  in the radical `ker G_N(c⋆,μ)`.
-/

namespace Virasoro.P2

open Virasoro Polynomial

open scoped PowerSeries Matrix

section Orth

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Matrix ι ι ℂ⟦X⟧} {w : ι → ι → ℂ⟦X⟧}
  {e : ι → ℕ} {u : ι → ℂ⟦X⟧}

theorem orthBasis_det_ne_zero (h : OrthBasis G w e u) : G.det ≠ 0 := by
  have h1 := congrArg Matrix.det h.gram
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h1
  intro h0
  rw [h0, mul_zero, zero_mul] at h1
  have : ∏ a, (PowerSeries.X : ℂ⟦X⟧) ^ e a * u a ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun a _ =>
      mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (h.hu a).ne_zero
  exact this h1.symm

theorem orth_unit_inv (h : OrthBasis G w e u) (a : ι) : u a * (u a)⁻¹ = 1 := by
  have := h.hu a
  rw [PowerSeries.isUnit_iff_constantCoeff] at this
  exact PowerSeries.mul_inv_cancel _ this.ne_zero

/-- The trace through an orthogonal basis (l.2990–2996): if `v_aᵀ P v_a = X^{e_a} r_a`, then
`∑_{ij} adj(G)_{ij} P_{ji} = det G · ∑_a u_a⁻¹ r_a`. -/
theorem orth_trace (h : OrthBasis G w e u) (P : Matrix ι ι ℂ⟦X⟧) {r : ι → ℂ⟦X⟧}
    (hr : ∀ a, w a ⬝ᵥ P.mulVec (w a) = (PowerSeries.X : ℂ⟦X⟧) ^ e a * r a) :
    ∑ i, ∑ j, G.adjugate i j * P j i = G.det * ∑ a, (u a)⁻¹ * r a := by
  set m : ℕ := ∑ a, e a with hm
  have he : ∀ a, e a ≤ m := fun a => Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ a)
  set dd : ι → ℂ⟦X⟧ := fun a => (PowerSeries.X : ℂ⟦X⟧) ^ (m - e a) * (u a)⁻¹ with hdd
  set S : Matrix ι ι ℂ⟦X⟧ := (Matrix.of w)ᵀ * Matrix.diagonal dd * Matrix.of w with hSdef
  have hDD : (Matrix.diagonal fun a => (PowerSeries.X : ℂ⟦X⟧) ^ e a * u a) *
      Matrix.diagonal dd = (PowerSeries.X : ℂ⟦X⟧) ^ m • 1 := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1
    funext a
    have h1 : (PowerSeries.X : ℂ⟦X⟧) ^ e a * PowerSeries.X ^ (m - e a) = PowerSeries.X ^ m := by
      rw [← pow_add, Nat.add_sub_cancel' (he a)]
    rw [hdd]
    linear_combination (u a * (u a)⁻¹) * h1 + (PowerSeries.X : ℂ⟦X⟧) ^ m * orth_unit_inv h a
  have hS : G * S = (PowerSeries.X : ℂ⟦X⟧) ^ m • 1 := by
    have hmt : G * (Matrix.of w)ᵀ = (Matrix.of w)⁻¹ *
        Matrix.diagonal fun a => (PowerSeries.X : ℂ⟦X⟧) ^ e a * u a := by
      rw [← h.gram, Matrix.mul_assoc (Matrix.of w), ← Matrix.mul_assoc (Matrix.of w)⁻¹,
        Matrix.nonsing_inv_mul _ h.unit, Matrix.one_mul]
    rw [hSdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hmt,
      Matrix.mul_assoc (Matrix.of w)⁻¹, hDD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.nonsing_inv_mul _ h.unit]
  have hSe : ∀ i j, S i j = ∑ a, w a i * dd a * w a j := by
    intro i j
    rw [hSdef, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_diagonal]
    rfl
  have hsum : (∑ i, ∑ j, S i j * P j i) =
      (PowerSeries.X : ℂ⟦X⟧) ^ m * ∑ a, (u a)⁻¹ * r a := by
    have h1 : (∑ i, ∑ j, S i j * P j i) = ∑ a, dd a * (w a ⬝ᵥ P.mulVec (w a)) := by
      simp only [hSe, Finset.sum_mul]
      have h2 : ∀ i, (∑ j, ∑ a, w a i * dd a * w a j * P j i) =
          ∑ a, ∑ j, w a i * dd a * w a j * P j i := fun i => Finset.sum_comm
      simp only [h2]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h3 : (PowerSeries.X : ℂ⟦X⟧) ^ (m - e a) * PowerSeries.X ^ e a = PowerSeries.X ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (he a)]
    rw [hr a, hdd]
    linear_combination ((u a)⁻¹ * r a) * h3
  have hadj : (PowerSeries.X : ℂ⟦X⟧) ^ m • G.adjugate = G.det • S := by
    have h1 : G.adjugate * (G * S) = G.det • S := by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [hS, Matrix.mul_smul, Matrix.mul_one] at h1
    exact h1
  have key : (PowerSeries.X : ℂ⟦X⟧) ^ m * (∑ i, ∑ j, G.adjugate i j * P j i) =
      (PowerSeries.X : ℂ⟦X⟧) ^ m * (G.det * ∑ a, (u a)⁻¹ * r a) := by
    have e1 : (PowerSeries.X : ℂ⟦X⟧) ^ m * (∑ i, ∑ j, G.adjugate i j * P j i) =
        ∑ i, ∑ j, ((PowerSeries.X : ℂ⟦X⟧) ^ m • G.adjugate) i j * P j i := by
      simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have e2 : (∑ i, ∑ j, (G.det • S) i j * P j i) = G.det * ∑ i, ∑ j, S i j * P j i := by
      simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [e1, hadj, e2, hsum]
    ring
  exact mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) key

end Orth

section Pairing

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Divisibility of `G V` from its pairings with a complement `A` of a subspace `B` whose vectors
have exact kernel lifts. -/
theorem dvd_of_pairing {G : Matrix κ κ ℂ⟦X⟧} (hG : Gᵀ = G) {A B : Submodule ℂ (κ → ℂ)}
    (hAB : ∀ z, z ∈ A ⊔ B)
    (hB : ∀ b ∈ B, ∃ V : κ → ℂ⟦X⟧, (∀ j, PowerSeries.constantCoeff (V j) = b j) ∧
      G.mulVec V = 0)
    {V : κ → ℂ⟦X⟧} (i : ℕ)
    (hA : ∀ a ∈ A, (PowerSeries.X : ℂ⟦X⟧) ^ i ∣
      (fun j => PowerSeries.C (a j)) ⬝ᵥ G.mulVec V) :
    ∀ Y, (PowerSeries.X : ℂ⟦X⟧) ^ i ∣ (G.mulVec V) Y := by
  induction i with
  | zero => intro Y; rw [pow_zero]; exact one_dvd _
  | succ i ih =>
    intro Y
    have hi := ih fun a ha => (pow_dvd_pow _ (Nat.le_succ i)).trans (hA a ha)
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hAB (Pi.single Y 1))
    obtain ⟨Vb, hVb0, hVb⟩ := hB b hb
    have hdiff : ∀ j, (PowerSeries.X : ℂ⟦X⟧) ∣ Vb j - PowerSeries.C (b j) := fun j => by
      rw [PowerSeries.X_dvd_iff, map_sub, hVb0, PowerSeries.constantCoeff_C, sub_self]
    choose Wb hWb using hdiff
    have e1 : (G.mulVec V) Y = (fun j => PowerSeries.C (a j)) ⬝ᵥ G.mulVec V +
        (fun j => PowerSeries.C (b j)) ⬝ᵥ G.mulVec V := by
      rw [← add_dotProduct]
      have h1 : ((fun j => PowerSeries.C (a j)) + fun j => PowerSeries.C (b j)) =
          (Pi.single Y (1 : ℂ⟦X⟧) : κ → ℂ⟦X⟧) := by
        funext j
        have h2 := congrFun hab j
        simp only [Pi.add_apply] at h2 ⊢
        rw [← map_add, h2]
        by_cases hj : j = Y
        · subst hj; simp
        · simp [hj]
      rw [h1, single_dotProduct, one_mul]
    have e2 : (fun j => PowerSeries.C (b j)) ⬝ᵥ G.mulVec V =
        -((PowerSeries.X : ℂ⟦X⟧) * (Wb ⬝ᵥ G.mulVec V)) := by
      have hC : (fun j => PowerSeries.C (b j)) = Vb - (PowerSeries.X : ℂ⟦X⟧) • Wb := by
        funext j
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [← hWb j]
        ring
      have h0 : Vb ⬝ᵥ G.mulVec V = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hG, hVb, zero_dotProduct]
      rw [hC, sub_dotProduct, smul_dotProduct, smul_eq_mul, h0, zero_sub]
    rw [e1, e2, pow_succ]
    refine dvd_add ((pow_succ (PowerSeries.X : ℂ⟦X⟧) i) ▸ hA a ha) (dvd_neg.2 ?_)
    rw [mul_comm (PowerSeries.X ^ i)]
    exact mul_dvd_mul_left _ (dvd_dot_right hi)

end Pairing

section Local

variable {N n : ℕ}

/-- The family `E` as a constant matrix over `ℂ⟦X⟧`. -/
noncomputable def Fm (E : Fin n → (Nat.Partition N → ℂ)) :
    Matrix (Nat.Partition N) (Fin n) ℂ⟦X⟧ := Matrix.of fun Y i => PowerSeries.C (E i Y)

theorem gramForm_Fm (E : Fin n → (Nat.Partition N → ℂ)) (G : Matrix (Nat.Partition N)
    (Nat.Partition N) ℂ⟦X⟧) (i j : Fin n) :
    ((Fm E)ᵀ * G * Fm E) i j = (fun Y => PowerSeries.C (E i Y)) ⬝ᵥ
      G.mulVec (fun Y => PowerSeries.C (E j Y)) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fm, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun Y _ => Finset.sum_congr rfl fun Y' _ => by ring

theorem bf_Fm (E : Fin n → (Nat.Partition N → ℂ)) (G : Matrix (Nat.Partition N)
    (Nat.Partition N) ℂ⟦X⟧) (x y : Fin n → ℂ⟦X⟧) :
    bf ((Fm E)ᵀ * G * Fm E) x y = (Fm E).mulVec x ⬝ᵥ G.mulVec ((Fm E).mulVec y) := by
  rw [bf, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

theorem mulVec_Fm (E : Fin n → (Nat.Partition N → ℂ)) (G : Matrix (Nat.Partition N)
    (Nat.Partition N) ℂ⟦X⟧) (x : Fin n → ℂ⟦X⟧) (j : Fin n) :
    (((Fm E)ᵀ * G * Fm E).mulVec x) j =
      (fun Y => PowerSeries.C (E j Y)) ⬝ᵥ G.mulVec ((Fm E).mulVec x) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fm, Matrix.of_apply]

theorem constantCoeff_Fm_mulVec (E : Fin n → (Nat.Partition N → ℂ)) (x : Fin n → ℂ⟦X⟧)
    (Y : Nat.Partition N) :
    PowerSeries.constantCoeff ((Fm E).mulVec x Y) =
      (∑ i, (fun Z => PowerSeries.constantCoeff (x Z)) i • E i) Y := by
  simp only [Matrix.mulVec, dotProduct, Fm, Matrix.of_apply, map_sum, map_mul,
    PowerSeries.constantCoeff_C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The exponents of the Gram matrix of `E` over `ℂ⟦X⟧` (l.2992–2996): with Step 3 (`J_τ^2 = 0`
in coordinates) and the exact kernel lifts of Step 2, every `e_a ≤ 1`, and `e_a = 1` puts
`v_a(0) = E·w_a(0)` in `ker G_N(c⋆,μ)`. -/
theorem e_le_one {b : ℂ} {R S : ℕ} {χ : Verma ℂ (kacC b) (kacH R S b)}
    {E : Fin n → (Nat.Partition N → ℂ)} (hLI : LinearIndependent ℂ E)
    (hc : IsCompl (Submodule.span ℂ (Set.range E)) ((Verma.negSpan χ).comap (Verma.pbwCoord N)))
    (hdepth : ∀ v : Nat.Partition N → ℂ, v ∈ layer (gram (cLoc b) (hLoc R S b) N) 2 ↔
      Verma.pbwCoord N v ∈ Verma.negSpan χ)
    (hlift : ∀ v : Nat.Partition N → ℂ, Verma.pbwCoord N v ∈ Verma.negSpan χ →
      ∃ V : Nat.Partition N → ℂ⟦X⟧, (∀ Y, PowerSeries.constantCoeff (V Y) = v Y) ∧
        (gram (cLoc b) (hLoc R S b) N).mulVec V = 0)
    {w : Fin n → Fin n → ℂ⟦X⟧} {e : Fin n → ℕ} {u : Fin n → ℂ⟦X⟧}
    (h : OrthBasis ((Fm E)ᵀ * gram (cLoc b) (hLoc R S b) N * Fm E) w e u) (a : Fin n) :
    e a ≤ 1 ∧ (e a = 1 → (gram (kacC b) (kacH R S b) N).mulVec
      (∑ i, (fun Z => PowerSeries.constantCoeff (w a Z)) i • E i) = 0) := by
  classical
  set GX := gram (cLoc b) (hLoc R S b) N with hGX
  set Wv : Nat.Partition N → ℂ⟦X⟧ := (Fm E).mulVec (w a) with hWv
  set va : Nat.Partition N → ℂ := ∑ i, (fun Z => PowerSeries.constantCoeff (w a Z)) i • E i
    with hva
  have hWv0 : ∀ Y, PowerSeries.constantCoeff (Wv Y) = va Y := fun Y => constantCoeff_Fm_mulVec E _ Y
  -- `G_X Wv` is divisible by `X^{e_a}`
  have hAB : ∀ z, z ∈ Submodule.span ℂ (Set.range E) ⊔
      (Verma.negSpan χ).comap (Verma.pbwCoord N) := fun z => by
    rw [hc.sup_eq_top]; exact Submodule.mem_top
  have hdiv : ∀ Y, (PowerSeries.X : ℂ⟦X⟧) ^ e a ∣ (GX.mulVec Wv) Y := by
    refine dvd_of_pairing (gram_transpose _ _ _) hAB (fun bv hbv => hlift bv hbv) (e a)
      fun a' ha' => ?_
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 ha'
    have e1 : (fun j => PowerSeries.C ((∑ i, c i • E i) j)) =
        ∑ i, PowerSeries.C (c i) • fun Y => PowerSeries.C (E i Y) := by
      funext Y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    rw [e1, sum_dotProduct]
    refine Finset.dvd_sum fun i _ => ?_
    rw [smul_dotProduct, smul_eq_mul, ← mulVec_Fm]
    rw [h.mulVec_row]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_mul_right _ _) _) _
  have hva_span : va ∈ Submodule.span ℂ (Set.range E) :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hva0 : va ≠ 0 := by
    intro h0
    have hz : (fun Z => PowerSeries.constantCoeff (w a Z)) = 0 := by
      have := (Fintype.linearIndependent_iff.1 hLI) _ h0
      funext Z
      exact this Z
    exact (OrthBasis.linearIndependent_val0 h).ne_zero a hz
  refine ⟨?_, fun he1 => ?_⟩
  · by_contra hlt
    push_neg at hlt
    have hmem : va ∈ layer GX 2 := ⟨Wv, hWv0, fun Y =>
      (pow_dvd_pow _ (by omega)).trans (hdiv Y)⟩
    have hneg := (hdepth va).1 hmem
    have hbot : va ∈ Submodule.span ℂ (Set.range E) ⊓
        (Verma.negSpan χ).comap (Verma.pbwCoord N) := ⟨hva_span, hneg⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at hbot
    exact hva0 hbot
  · funext Y
    have h1 := map_mulVec_apply (PowerSeries.constantCoeff (R := ℂ)) GX Wv Y
    rw [hGX, ← gram_map, constantCoeff_cLoc, constantCoeff_hLoc] at h1
    have e2 : (fun Z => PowerSeries.constantCoeff (Wv Z)) = va := funext hWv0
    rw [e2] at h1
    rw [Pi.zero_apply, h1, ← PowerSeries.X_dvd_iff]
    have := hdiv Y
    rwa [he1, pow_one] at this

end Local

end Virasoro.P2
