import Virasoro.Sphere.Proofs.Sec3Ward
import Virasoro.Sphere.Proofs.Sec5TopB
import Virasoro.Proofs.Naturality

/-!
# The block as a Fock pairing (sphere paper Lemma 3.2(ii))

sphere/paper.tex l.490–493: at real parameters,
`ℬ_N = ⟨w_N^{(4,3)}, w_N^{(1,2)}⟩` equals the pairing of `F̃_N` with `F_N` through
`∏_m α_m!/(2m)^{α_m}`.
-/

namespace Virasoro.Sphere

open MvPolynomial Verma

theorem fockBil_map_conj (g f : Fock) :
    fockBil (map (starRingEnd ℂ) g) f = fockForm g f := by
  unfold fockBil fockForm
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_map]

section FockSide

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant) (μ lam : ℝ)
  (hμ : 0 < μ) (hlam : 0 < lam)

local notation "cc" => (1 + 24 * (μ : ℂ) ^ 2)
local notation "dd" => ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
local notation "fw" => fockWord (μ : ℂ) (lam : ℂ)

theorem conj_cc : (starRingEnd ℂ) cc = cc := by
  have h : cc = ((1 + 24 * μ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.conj_ofReal]

theorem conj_dd : (starRingEnd ℂ) dd = dd := by
  have h : dd = ((lam ^ 2 + μ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.conj_ofReal]

theorem gram_conj (N : ℕ) : (gram cc dd N).map (starRingEnd ℂ) = gram cc dd N := by
  rw [← gram_map (starRingEnd ℂ), conj_cc, conj_dd]

theorem gram_transpose (N : ℕ) : (gram cc dd N).transpose = gram cc dd N := by
  ext Y Y'
  exact gramWord_symm _ _ (posWord_word Y') (posWord_word Y)

include hF hK hμ hlam

/-- Lemma 3.2(ii), the pairing formula for `ℬ_N`. -/
theorem block_eq_fockBil (Δe : Fin 4 → ℝ) (F G : ℕ → Fock)
    (h1 : IsWardSeries (μ : ℂ) (lam : ℂ) (Δe 0 : ℂ) (Δe 1 : ℂ) F)
    (h2 : IsWardSeries (μ : ℂ) (lam : ℂ) (Δe 3 : ℂ) (Δe 2 : ℂ) G) (N : ℕ) :
    RatFunc.eval (RingHom.id ℂ) dd (Bsph cc (fun i => (Δe i : ℂ)) N) =
      fockBil (map (starRingEnd ℂ) (G N)) (F N) := by
  have hG := gram_det_ne_zero_fock hK μ lam hμ hlam N
  have hU : IsUnit (gram cc dd N).det := isUnit_iff_ne_zero.mpr hG
  obtain ⟨y, hy⟩ := exists_coords hF hK μ lam hμ hlam N (G N) (h2.2.1 N)
  -- `G_N y = γ^{(4,3)}`
  have hGy : (gram cc dd N).mulVec y = fun Y => gammaY dd (Δe 3 : ℂ) (Δe 2 : ℂ) Y.word := by
    funext Y
    have h3 := ward_pair hF hK μ lam hμ hlam _ _ G h2 N Y.word (posWord_word Y) (word_sum' Y)
    rw [hy, fockForm_sum_right] at h3
    simp only [fockForm_smul_right, fock_gram_iso hF μ lam] at h3
    rw [← h3, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun Y' _ => mul_comm _ _
  -- the coordinates are real
  have hreal : (fun Y => (starRingEnd ℂ) (y Y)) = y := by
    have h4 : (gram cc dd N).mulVec (fun Y => (starRingEnd ℂ) (y Y)) =
        fun Y => gammaY dd (Δe 3 : ℂ) (Δe 2 : ℂ) Y.word := by
      funext Y
      have h5 := RingHom.map_mulVec (starRingEnd ℂ) (gram cc dd N) y Y
      rw [gram_conj] at h5
      have h6 : ((starRingEnd ℂ) ∘ y) = fun Y => (starRingEnd ℂ) (y Y) := rfl
      rw [h6] at h5
      rw [← h5, hGy, map_gammaY, conj_dd, Complex.conj_ofReal, Complex.conj_ofReal]
    have h7 : (gram cc dd N).mulVec ((fun Y => (starRingEnd ℂ) (y Y)) - y) = 0 := by
      rw [Matrix.mulVec_sub, h4, hGy, sub_self]
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hG h7)
  have hyinv : y = (gram cc dd N)⁻¹.mulVec fun Y => gammaY dd (Δe 3 : ℂ) (Δe 2 : ℂ) Y.word := by
    rw [← hGy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU, Matrix.one_mulVec]
  have hsymm : ∀ Y Z, (gram cc dd N)⁻¹ Z Y = (gram cc dd N)⁻¹ Y Z := by
    intro Y Z
    have h8 := Matrix.transpose_nonsing_inv (gram cc dd N)
    rw [gram_transpose] at h8
    have h9 := congrFun (congrFun h8 Y) Z
    rw [Matrix.transpose_apply] at h9
    exact h9
  -- the Fock pairing
  have hpair : fockForm (G N) (F N) =
      ∑ Z, y Z * gammaY dd (Δe 0 : ℂ) (Δe 1 : ℂ) Z.word := by
    conv_lhs => rw [hy]
    rw [fockForm_sum_left]
    refine Finset.sum_congr rfl fun Z _ => ?_
    rw [fockForm_smul_left, congrFun hreal Z,
      ward_pair hF hK μ lam hμ hlam _ _ F h1 N Z.word (posWord_word Z) (word_sum' Z)]
  rw [fockBil_map_conj, hpair]
  have hev := evalAt_Bsph (c := cc) (z := dd) (fun i => (Δe i : ℂ)) (M := N) hG
  rw [evalAt] at hev
  rw [hev, Finset.sum_comm]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [hyinv, Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [hsymm Y Z]
  ring

end FockSide

end Virasoro.Sphere
