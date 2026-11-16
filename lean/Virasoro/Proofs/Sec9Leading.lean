import Virasoro.Proofs.Sec8RegLabels
import Virasoro.Proofs.Sec9Theta10
import Virasoro.Proofs.Sec9Const
import Virasoro.Proofs.Ising4
import Virasoro.Proofs.Sec8Theta7

/-!
# Proposition 9.5: the intrinsic leading coefficient at level ten

The normalized singular vectors `ψ₈ ∈ M(1/2,33/16)` and `ψ₆ ∈ M(1/2,65/16)` are explicit
(checked by the normalization engine) and unique (`unique_of_B` with Lemma 8.4's
determinants), so `q₈ = ψ₈`, `q₆ = ψ₆`; `ψ₈ χ₂ = ψ₆ χ₄ = χ₁₀` by the engine; the torus
polynomials are `𝒫_{4,2}(b₀,d)` and `𝒫_{1,6}(b₀,d)` by the specialization of Proposition 6.2;
`γ₁₀ = -1121229484375/192` by the engine over `ℚ[x]/(x³)`; and the leading coefficient of
`H₁₀` comes from Theorem 9.4.
-/

namespace Virasoro

open Verma Module Polynomial

set_option maxRecDepth 200000

def psi8Q : List (List ℕ × ℚ) := [([8], 26809 / 16), ([7, 1], -90721 / 96), ([6, 2], 12281 / 16), ([6, 1, 1], 6155 / 12), ([5, 3], 109833 / 32), ([5, 2, 1], -46223 / 12), ([5, 1, 1, 1], 2057 / 3), ([4, 4], -39503 / 16), ([4, 3, 1], 7403 / 12), ([4, 2, 2], 16543 / 32), ([4, 2, 1, 1], 20537 / 12), ([4, 1, 1, 1, 1], -649 / 2), ([3, 3, 2], -8493 / 8), ([3, 3, 1, 1], -4253 / 12), ([3, 2, 2, 1], 59729 / 48), ([3, 2, 1, 1, 1], -2731 / 6), ([3, 1, 1, 1, 1, 1], 169 / 3), ([2, 2, 2, 2], 11025 / 256), ([2, 2, 2, 1, 1], -25729 / 48), ([2, 2, 1, 1, 1, 1], 16787 / 72), ([2, 1, 1, 1, 1, 1, 1], -89 / 3), ([1, 1, 1, 1, 1, 1, 1, 1], 1)]
def psi6Q : List (List ℕ × ℚ) := [([6], -5085 / 8), ([5, 1], 2061 / 4), ([4, 2], 9135 / 16), ([4, 1, 1], -1053 / 4), ([3, 3], 1665 / 8), ([3, 2, 1], -3609 / 8), ([3, 1, 1, 1], 147 / 2), ([2, 2, 2], -6075 / 64), ([2, 2, 1, 1], 2331 / 16), ([2, 1, 1, 1, 1], -105 / 4), ([1, 1, 1, 1, 1, 1], 1)]
def chi2Q : List (List ℕ × ℚ) := [([1, 1], 1), ([2], -3 / 4)]
def chi4Q : List (List ℕ × ℚ) :=
  [([1, 1, 1, 1], 1), ([2, 1, 1], -25 / 6), ([2, 2], 49 / 144), ([3, 1], 11 / 6), ([4], -1 / 4)]

/-- The coordinates of `χ₁₀`. -/
def x10Q : List (List ℕ × ℚ) := [([8, 1, 1], -19411/16), ([8, 2], 54369/64), ([7, 1, 1, 1], -88165/96), ([7, 2, 1], 106597/128), ([7, 3], 6011/128), ([6, 2, 1, 1], -5/8), ([6, 2, 2], 3313/64), ([6, 1, 1, 1, 1], 7055/12), ([6, 3, 1], -13943/8), ([6, 4], -501/8), ([5, 3, 1, 1], 12117/32), ([5, 3, 2], 63545/128), ([5, 2, 1, 1, 1], -37141/12), ([5, 2, 2, 1], 35337/32), ([5, 5], -3145/16), ([5, 1, 1, 1, 1, 1], 3403/6), ([5, 4, 1], 1507/8), ([4, 4, 1, 1], 7225/16), ([4, 4, 2], -45787/64), ([4, 3, 1, 1, 1], 8945/12), ([4, 3, 2, 1], -15705/16), ([4, 3, 3], 1103/16), ([4, 2, 2, 1, 1], -91679/32), ([4, 2, 2, 2], 53287/128), ([4, 2, 1, 1, 1, 1], 62935/24), ([9, 1], -21677/32), ([10], 6261/16), ([4, 1, 1, 1, 1, 1, 1], -733/2), ([3, 3, 2, 1, 1], 3653/16), ([3, 3, 2, 2], -8771/64), ([3, 3, 1, 1, 1, 1], -1697/3), ([3, 3, 3, 1], 4253/8), ([3, 2, 2, 1, 1, 1], 42541/48), ([3, 2, 2, 2, 1], -8271/64), ([3, 2, 1, 1, 1, 1, 1], -4367/12), ([3, 1, 1, 1, 1, 1, 1, 1], 151/3), ([2, 2, 2, 2, 1, 1], 113941/256), ([2, 2, 2, 2, 2], -33075/1024), ([2, 2, 2, 1, 1, 1, 1], -68245/96), ([2, 2, 1, 1, 1, 1, 1, 1], 18389/72), ([2, 1, 1, 1, 1, 1, 1, 1, 1], -365/12), ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 1)]

/-- A solution of `G₀ v₁ = - G₁ χ₁₀` (found by `scripts/gamma10.py`). -/
def v1Q10 : List (List ℕ × ℚ) := [([1, 1, 1, 1, 1, 1, 1, 1, 1, 1], 18372273125981 / 8974617523200), ([2, 1, 1, 1, 1, 1, 1, 1, 1], -55033880374073 / 2393231339520), ([2, 2, 1, 1, 1, 1, 1, 1], -2885191496939 / 7122712320), ([2, 2, 2, 1, 1, 1, 1], 3720745974409 / 1780678080), ([2, 2, 2, 2, 1, 1], -241367564909 / 1335508560), ([3, 1, 1, 1, 1, 1, 1, 1], -468070156255703 / 3233711393280), ([3, 2, 1, 1, 1, 1, 1], 7111940198223523 / 1717909177680), ([3, 2, 2, 1, 1, 1], -92383939987055 / 6736898736), ([3, 2, 2, 2, 1], 29622526908767 / 14315909814), ([3, 3, 1, 1, 1, 1], 149709322541579 / 269475949440)]

theorem chi2_eq_mapSt : chi2 = mapSt qC chi2Q := by simp [chi2, chi2Q, mapSt, map_div₀]
theorem chi4_eq_mapSt : chi4 = mapSt qC chi4Q := by simp [chi4, chi4Q, mapSt, map_div₀]

theorem isLevel_psi8Q : IsLevelSt 8 psi8Q := by unfold IsLevelSt PosWord; decide +kernel
theorem isLevel_psi6Q : IsLevelSt 6 psi6Q := by unfold IsLevelSt PosWord; decide +kernel
theorem isLevel_x10Q : IsLevelSt 10 x10Q := by unfold IsLevelSt PosWord; decide +kernel

theorem psi8_singular :
    IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (33 / 16 : ℂ)) (mapSt qC psi8Q)) 8 := by
  refine isSingular_ofQ 60 (1 / 2) (33 / 16) (by simp [map_div₀]) (by simp [map_div₀]) psi8Q
    isLevel_psi8Q (coords_ne_of_ones _ (by decide +kernel)) fun n h1 h2 => ?_
  interval_cases n <;> decide +kernel

theorem psi6_singular :
    IsSingular (St.toVerma (c := (1 / 2 : ℂ)) (h := (65 / 16 : ℂ)) (mapSt qC psi6Q)) 6 := by
  refine isSingular_ofQ 60 (1 / 2) (65 / 16) (by simp [map_div₀]) (by simp [map_div₀]) psi6Q
    isLevel_psi6Q (coords_ne_of_ones _ (by decide +kernel)) fun n h1 h2 => ?_
  interval_cases n <;> decide +kernel

theorem opN_psi8_chi2 : (opN 60 (1 / 2 : ℚ) (1 / 16) psi8Q chi2Q).Perm x10Q := by decide +kernel
theorem opN_psi6_chi4 : (opN 60 (1 / 2 : ℚ) (1 / 16) psi6Q chi4Q).Perm x10Q := by decide +kernel

/-- `∑_Y q_Y L_{-Y}` for the coordinates of an explicit vector. -/
theorem coordOp_coords {N : ℕ} (s : St ℂ) (hs : IsLevelSt N s) :
    coordOp (1 / 2 : ℂ) (St.coords N s) = St.toOp (1 / 2 : ℂ) s := by
  unfold coordOp St.toOp
  exact sum_coords_smul s hs fun w => VirEnv.negOp (1 / 2 : ℂ) w

theorem coords_one_of {N : ℕ} (s : List (List ℕ × ℚ))
    (h : ((s.filter fun t => t.1 = List.replicate N 1).map Prod.snd).sum = 1) :
    St.coords N (mapSt qC s) (onesPartition N) = 1 := by
  rw [coords_mapSt, coords_ones, h, map_one]

theorem detC_ne {m : ℕ} (hq Dq : ℚ) (h : ℂ) (hhq : qC hq = h)
    (hdet : (Bmat m (1 / 2 : ℚ) hq).det = Dq) (hD0 : Dq ≠ 0) :
    (Bmat m (1 / 2 : ℂ) h).det ≠ 0 := by
  have hBC : Bmat m (1 / 2 : ℂ) h = (Bmat m (1 / 2 : ℚ) hq).map qC := by
    rw [← Bmat_map, ← hhq]
    congr 1
    simp
  rw [hBC, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet]
  exact (map_ne_zero qC).2 hD0

/-- The identities of Proposition 6.2 at `b₀` for every normalized singular vector. -/
theorem identities_at_b0 (hH : Cited_HJSNormalizations) (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (h : ℂ) (hh : kacH r s b0 = h) (hLD : LevelData (r * s))
    (hdetne : (Bmat (r * s) (1 / 2 : ℂ) h).det ≠ 0) (p : Nat.Partition (r * s) → ℂ)
    (hp1 : p (onesPartition (r * s)) = 1)
    (hsp : IsSingular (pbwCoord (c := (1 / 2 : ℂ)) (h := h) (r * s) p) (r * s)) :
    crossScalar (1 / 2 : ℂ) h p = (genA r s b0)⁻¹ ∧
      ∀ d : ℂ, torusForm (1 / 2 : ℂ) h d (r * s) p p = genP r s b0 d := by
  have hc : kacC b0 = 1 / 2 := kacC_b0'
  obtain ⟨pq, ⟨hpq1, hpqs⟩, -, -, -, hcont⟩ := normalization_at hH r s hr hs
  have hcQ : EvToK b0 (kacC (RatFunc.X : RatFunc ℚ)) (1 / 2 : ℂ) := hc ▸ evToK_kacC b0_ne_zero
  have hhQ : EvToK b0 (kacH r s (RatFunc.X : RatFunc ℚ)) h := hh ▸ evToK_kacH b0_ne_zero r s
  obtain ⟨pv', hpv', -⟩ := regular_of_B hLD hcQ hhQ hdetne pq hpq1 (hpqs.2.2 1 (by norm_num))
    (hpqs.2.2 2 (by norm_num))
  obtain ⟨hs1, hone1, hcross, htor⟩ := hcont ℂ b0 b0_ne_zero fun Y => (hpv' Y).1
  rw [hc, hh] at hs1 hcross htor
  have hpeq : (fun Y => RatFunc.eval (algebraMap ℚ ℂ) b0 (pq Y)) = p :=
    unique_of_B hLD hdetne _ p hone1 hp1 hs1 hsp
  rw [hpeq] at hcross htor
  exact ⟨by rw [genA_inv]; exact hcross, htor⟩

/-! ### `γ₁₀` over `ℚ[x]/(x³)` -/

def cT10 : T3 ℚ := ⟨1 / 2, 0, 0⟩
def hT10 : T3 ℚ := ⟨1 / 16, 1, 0⟩

/-- The jet `χ₁₀ + x v₁`. -/
def sT10 : List (List ℕ × T3 ℚ) :=
  x10Q.map (fun t => (t.1, ⟨t.2, 0, 0⟩)) ++ v1Q10.map (fun t => (t.1, ⟨0, t.2, 0⟩))

theorem isLevel_sT10 : IsLevelSt 10 sT10 := by unfold IsLevelSt PosWord; decide +kernel
theorem isLevel_v1Q10 : IsLevelSt 10 v1Q10 := by unfold IsLevelSt PosWord; decide +kernel

theorem rows_sT10 : ∀ w ∈ decWords 10, (∀ u ∈ posN 60 cT10 hT10 w sT10, u.1 = []) ∧
    (vacT (posN 60 cT10 hT10 w sT10)).a = 0 ∧ (vacT (posN 60 cT10 hT10 w sT10)).b = 0 := by
  decide +kernel

theorem posN_x10_empty : ∀ t ∈ x10Q, ∀ u ∈ posN 60 cT10 hT10 t.1 sT10, u.1 = [] := by
  decide +kernel

theorem gamma10_sum :
    (x10Q.map fun t => t.2 * (vacT (posN 60 cT10 hT10 t.1 sT10)).c).sum = -1121229484375 / 192 := by
  decide +kernel

theorem coords_sT10 (Y : Nat.Partition 10) :
    St.coords 10 (mapSt qT sT10) Y =
      ⟨St.coords 10 (mapSt qC x10Q) Y, St.coords 10 (mapSt qC v1Q10) Y, 0⟩ := by
  have e1 : mapSt qT (x10Q.map fun t => (t.1, (⟨t.2, 0, 0⟩ : T3 ℚ)))
      = mapSt T3.inl (mapSt qC x10Q) := by
    simp only [mapSt, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    ext <;> simp [qT]
  have e2 : mapSt qT (v1Q10.map fun t => (t.1, (⟨0, t.2, 0⟩ : T3 ℚ)))
      = (mapSt qC v1Q10).map fun t => (t.1, (⟨0, t.2, 0⟩ : T3 ℂ)) := by
    simp only [mapSt, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    ext <;> simp [qT]
  let gb : ℂ →+ T3 ℂ := ⟨⟨fun z => ⟨0, z, 0⟩, by ext <;> simp⟩, fun x y => by ext <;> simp⟩
  have e2' : (mapSt qC v1Q10).map (fun t => (t.1, (⟨0, t.2, 0⟩ : T3 ℂ)))
      = (mapSt qC v1Q10).map fun t => (t.1, gb t.2) := rfl
  rw [sT10, mapSt_append, coords_append, e1, e2, e2', coords_mapSt, coords_map_addHom gb]
  ext <;> simp [gb]

theorem gramLocal10_trunc :
    (gramLocal (1 / 2 : ℂ) (1 / 16) 10).map T3.trunc3 = gram (qT cT10) (qT hT10) 10 := by
  unfold gramLocal
  rw [← gram_map]
  congr 1
  · ext <;> simp [T3.trunc3_C, cT10, qT, map_div₀]
  · ext <;> simp [T3.trunc3_C, T3.trunc3_X, hT10, qT, map_div₀, PowerSeries.coeff_X]

theorem gram_sT10_x2 (Y : Nat.Partition 10) :
    let W := (gram (qT cT10) (qT hT10) 10).mulVec (St.coords 10 (mapSt qT sT10)) Y
    W.a = 0 ∧ W.b = 0 := by
  intro W
  obtain ⟨he, ha, hb⟩ := rows_sT10 Y.word (word_mem_decWords Y)
  have hW : W = qT (vacT (posN 60 cT10 hT10 Y.word sT10)) := by
    show (gram (qT cT10) (qT hT10) 10).mulVec (St.coords 10 (mapSt qT sT10)) Y = _
    rw [gram_mulVec_coords _ _ _ (isLevelSt_mapSt _ isLevel_sT10), ← toVerma_posN_posOp,
      vacuum_empty _ he]
  rw [hW]
  simp [qT, ha, hb]

theorem x10_ker2_gamma :
    let G := gramLocal (1 / 2 : ℂ) (1 / 16) 10
    let x10 := St.coords 10 (mapSt qC x10Q)
    let v1 := St.coords 10 (mapSt qC v1Q10)
    (coeffMat 0 G).mulVec v1 = -(coeffMat 1 G).mulVec x10 ∧ x10 ∈ ker2 G ∧
      cross2 G x10 x10 v1 = -1121229484375 / 192 := by
  intro G x10 v1
  have hcomp : ∀ Y, (G.map T3.trunc3).mulVec (fun j => (⟨x10 j, v1 j, 0⟩ : T3 ℂ)) Y
      = (gram (qT cT10) (qT hT10) 10).mulVec (St.coords 10 (mapSt qT sT10)) Y := by
    intro Y
    rw [gramLocal10_trunc]
    congr 1
    funext j
    rw [coords_sT10]
  have h0 : (coeffMat 0 G).mulVec x10 = 0 := by
    funext Y
    have := congrArg T3.a (hcomp Y)
    rw [mulVec_trunc3] at this
    exact this.trans (gram_sT10_x2 Y).1
  have h1 : (coeffMat 0 G).mulVec v1 + (coeffMat 1 G).mulVec x10 = 0 := by
    funext Y
    have := congrArg T3.b (hcomp Y)
    rw [mulVec_trunc3] at this
    exact this.trans (gram_sT10_x2 Y).2
  refine ⟨eq_neg_of_add_eq_zero_left h1,
    mem_ker2_of (gramLocal_isSymm (1 / 2 : ℂ) (1 / 16) 10) h0 h1, ?_⟩
  have hc : ∀ Y : Nat.Partition 10, ((coeffMat 2 G).mulVec x10 + (coeffMat 1 G).mulVec v1) Y
      = (vacuum (qT cT10) (qT hT10) (VirEnv.posOp (qT cT10) Y.word •
          St.toVerma (mapSt qT sT10))).c := by
    intro Y
    have := congrArg T3.c (hcomp Y)
    rw [mulVec_trunc3] at this
    dsimp only at this
    rw [Pi.add_apply, add_comm, this, gram_mulVec_coords _ _ _ (isLevelSt_mapSt _ isLevel_sT10)]
  unfold cross2
  simp only [dotProduct]
  rw [Finset.sum_congr rfl fun Y _ => by rw [hc Y],
    sum_coords_mul (mapSt qC x10Q) (isLevelSt_mapSt _ isLevel_x10Q)
      fun w => (vacuum (qT cT10) (qT hT10) (VirEnv.posOp (qT cT10) w •
        St.toVerma (mapSt qT sT10))).c]
  have hterm : ∀ t ∈ x10Q, (vacuum (qT cT10) (qT hT10) (VirEnv.posOp (qT cT10) t.1 •
      St.toVerma (mapSt qT sT10))).c = qC (vacT (posN 60 cT10 hT10 t.1 sT10)).c := by
    intro t ht
    rw [← toVerma_posN_posOp, vacuum_empty _ (posN_x10_empty t ht)]
    rfl
  have : ((mapSt qC x10Q).map fun t => t.2 * (vacuum (qT cT10) (qT hT10)
      (VirEnv.posOp (qT cT10) t.1 • St.toVerma (mapSt qT sT10))).c)
      = x10Q.map fun t => qC (t.2 * (vacT (posN 60 cT10 hT10 t.1 sT10)).c) := by
    rw [show mapSt qC x10Q = x10Q.map (fun t => (t.1, qC t.2)) from rfl, List.map_map]
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp_apply]
    rw [hterm t ht, map_mul]
  rw [this, show (x10Q.map fun t => qC (t.2 * (vacT (posN 60 cT10 hT10 t.1 sT10)).c))
      = (x10Q.map fun t => t.2 * (vacT (posN 60 cT10 hT10 t.1 sT10)).c).map qC from by
        rw [List.map_map]; rfl, ← map_list_sum, gamma10_sum]
  simp [map_div₀]

/-! ### The leading coefficient from Theorem 9.4 -/

theorem ppCoeff_two_of_PP {K : Type*} [Field K] (f : RatFunc K) (a A2 A1 : K) (hA : A2 ≠ 0)
    (h : PP f a = RatFunc.C A2 / (RatFunc.X - RatFunc.C a) ^ 2 +
      RatFunc.C A1 / (RatFunc.X - RatFunc.C a) ^ 1) :
    ppCoeff f a 2 = A2 := by
  have hord := poleOrder_eq_two_of_PP f a A2 A1 hA h
  have h2 := coeff_expandHom_PP f a 2 (by norm_num)
  rw [if_pos (le_of_eq hord.symm), h, map_add, expandHom_pole_same, expandHom_pole_same,
    HahnSeries.coeff_add, HahnSeries.coeff_single, HahnSeries.coeff_single] at h2
  simp only [neg_inj, Nat.cast_inj] at h2
  norm_num at h2
  exact h2.symm

/-- Proposition 9.5 (`thm:level-ten-leading`).

Paper label: thm:level-ten-leading -/
theorem thm_level_ten_leading (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) :
    Stmt_thm_level_ten_leading := by
  intro q₈ q₆ hq8 hs8 hq6 hs6
  dsimp only
  -- the explicit singular vectors and their uniqueness
  have hdet8 := detC_ne (33 / 16) _ (33 / 16 : ℂ) (by simp [map_div₀]) detB_42 (by norm_num)
  have hdet6 := detC_ne (65 / 16) _ (65 / 16 : ℂ) (by simp [map_div₀]) detB_16 (by norm_num)
  have hψ8 : IsSingular (pbwCoord (c := (1 / 2 : ℂ)) (h := (33 / 16 : ℂ)) 8
      (St.coords 8 (mapSt qC psi8Q))) 8 := by
    rw [← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_psi8Q)]; exact psi8_singular
  have hψ6 : IsSingular (pbwCoord (c := (1 / 2 : ℂ)) (h := (65 / 16 : ℂ)) 6
      (St.coords 6 (mapSt qC psi6Q))) 6 := by
    rw [← toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_psi6Q)]; exact psi6_singular
  have h1ψ8 : St.coords 8 (mapSt qC psi8Q) (onesPartition 8) = 1 :=
    coords_one_of _ (by decide +kernel)
  have h1ψ6 : St.coords 6 (mapSt qC psi6Q) (onesPartition 6) = 1 :=
    coords_one_of _ (by decide +kernel)
  have hq8e : q₈ = St.coords 8 (mapSt qC psi8Q) :=
    unique_of_B (m := 4 * 2) levelData_8 hdet8 q₈ _ hq8 h1ψ8 hs8 hψ8
  have hq6e : q₆ = St.coords 6 (mapSt qC psi6Q) :=
    unique_of_B (m := 1 * 6) levelData_6 hdet6 q₆ _ hq6 h1ψ6 hs6 hψ6
  -- `χ₁₀`
  have hχ : coordOp (1 / 2 : ℂ) q₈ • St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi2
      = St.toVerma (mapSt qC x10Q) := by
    rw [hq8e, coordOp_coords _ (isLevelSt_mapSt _ isLevel_psi8Q), chi2_eq_mapSt,
      ← toVerma_opN_of 60 (1 / 2) (1 / 16) (by simp [map_div₀]) (by simp [map_div₀]),
      toVerma_mapSt_perm opN_psi8_chi2]
  have hχ' : coordOp (1 / 2 : ℂ) q₆ • St.toVerma (c := (1 / 2 : ℂ)) (h := (1 / 16 : ℂ)) chi4
      = St.toVerma (mapSt qC x10Q) := by
    rw [hq6e, coordOp_coords _ (isLevelSt_mapSt _ isLevel_psi6Q), chi4_eq_mapSt,
      ← toVerma_opN_of 60 (1 / 2) (1 / 16) (by simp [map_div₀]) (by simp [map_div₀]),
      toVerma_mapSt_perm opN_psi6_chi4]
  -- the torus polynomials
  have hid8 := identities_at_b0 hH 4 2 (by norm_num) (by norm_num) (33 / 16 : ℂ)
    (by rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]) levelData_8 hdet8 q₈ hq8 hs8
  have hid6 := identities_at_b0 hH 1 6 (by norm_num) (by norm_num) (65 / 16 : ℂ)
    (by rw [def_fixed_specialization_ising.2]; norm_num [isingDelta]) levelData_6 hdet6 q₆ hq6 hs6
  have htor8 : torusPolyForm (1 / 2) (33 / 16) q₈ = P42 := by
    refine Polynomial.funext fun d => ?_
    rw [show torusPolyForm (1 / 2) (33 / 16) q₈ = torusSelf (1 / 2 : ℂ) (33 / 16 : ℂ) q₈ from rfl,
      torusSelf_eval, hid8.2 d, genP_42]
  have htor6 : torusPolyForm (1 / 2) (65 / 16) q₆ = P16 := by
    refine Polynomial.funext fun d => ?_
    rw [show torusPolyForm (1 / 2) (65 / 16) q₆ = torusSelf (1 / 2 : ℂ) (65 / 16 : ℂ) q₆ from rfl,
      torusSelf_eval, hid6.2 d, genP_16]
  -- `γ₁₀`
  obtain ⟨hv1, hker2, hγ⟩ := x10_ker2_gamma
  have hGs := gramLocal_isSymm (1 / 2 : ℂ) (1 / 16) 10
  -- the leading coefficient
  obtain ⟨-, hPP⟩ := thm_level_ten_principal_part hK hH
  have hA2 : -(192 * algebraMap ℂ[X] Kd (P2 * P42)) / 1121229484375 ≠ 0 := by
    rw [map_mul, aM_P2, aM_P42]
    exact div_ne_zero (neg_ne_zero.2 (mul_ne_zero (by norm_num)
      (mul_ne_zero (Pval_ne 1 2) (Pval_ne 4 2)))) (by norm_num)
  have hPP' := hPP
  unfold poleTerm at hPP'
  have hord := poleOrder_eq_two_of_PP _ _ _ _ hA2 hPP'
  have hpp := ppCoeff_two_of_PP _ _ _ _ hA2 hPP'
  have hP := lem_level_ten_constants.2.2.2.2
  refine ⟨by rw [hχ, hχ'], htor8, htor6, ⟨St.coords 10 (mapSt qC x10Q), ?_,
    fun v₁ v₁' h₁ h₁' => cross2_indep hGs hker2 h₁ h₁',
    fun v₁ h₁ => by rw [cross2_indep hGs hker2 h₁ hv1]; exact hγ⟩, hord.le, ?_, ?_⟩
  · rw [hχ, toVerma_eq_pbwCoord _ (isLevelSt_mapSt _ isLevel_x10Q)]
  · rw [hpp]
    field_simp
  · rw [hpp, ← hP]
    field_simp

end Virasoro
