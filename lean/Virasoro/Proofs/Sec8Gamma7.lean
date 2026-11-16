import Virasoro.Proofs.Sec8Smith7Comp

/-!
# Proposition 8.1: `ξ₇ ∈ K₂` and `γ₇ = -700700`

With `G(x) = G₇(1/2, 1/2 + x)`, the jet `ξ₇ + x v₁` over `ℚ[x]/(x³)` is mapped by `G` into
`x² ℚ[x]/(x³)`: the engine shows that `L_1, …, L_7` send it there.  Hence `G₀ ξ₇ = 0` and
`G₀ v₁ + G₁ ξ₇ = 0`, so `ξ₇ ∈ K₂`, and `γ₇ = ξ₇ᵀ(G₂ ξ₇ + G₁ v₁)` is the `x²` coefficient of
`ξ₇ᵀ G(x) (ξ₇ + x v₁)`, evaluated by the engine.
-/

namespace Virasoro

open Verma

set_option maxRecDepth 100000

/-- `ℚ[x]/(x³) → ℂ[x]/(x³)`. -/
noncomputable abbrev qT : T3 ℚ →+* T3 ℂ := T3.map qC

def cT7 : T3 ℚ := ⟨1 / 2, 0, 0⟩
def hT7 : T3 ℚ := ⟨1 / 2, 1, 0⟩

/-- The jet `ξ₇ + x v₁`. -/
def sT7 : List (List ℕ × T3 ℚ) :=
  x7Q.map (fun t => (t.1, ⟨t.2, 0, 0⟩)) ++ v1Q.map (fun t => (t.1, ⟨0, t.2, 0⟩))

/-- The sum of the coefficients of a combination of words. -/
def vacT (l : List (List ℕ × T3 ℚ)) : T3 ℚ := (l.map Prod.snd).sum

theorem isLevel_sT7 : IsLevelSt 7 sT7 := by unfold IsLevelSt PosWord; decide

/-- Every row of `G(x) (ξ₇ + x v₁)` lies in `x²`. -/
theorem rows_sT7 : ∀ w ∈ decWords 7, (∀ u ∈ posN 40 cT7 hT7 w sT7, u.1 = []) ∧
    (vacT (posN 40 cT7 hT7 w sT7)).a = 0 ∧ (vacT (posN 40 cT7 hT7 w sT7)).b = 0 := by
  decide +kernel

theorem posN_x7_empty : ∀ t ∈ x7Q, ∀ u ∈ posN 40 cT7 hT7 t.1 sT7, u.1 = [] := by decide +kernel

theorem gamma7_sum :
    (x7Q.map fun t => t.2 * (vacT (posN 40 cT7 hT7 t.1 sT7)).c).sum = -700700 := by
  decide +kernel

section T3Lemmas

variable {K : Type*} [Field K]

/-- The components of `T3` as additive maps. -/
def T3.aHom : T3 K →+ K := ⟨⟨T3.a, rfl⟩, fun _ _ => rfl⟩
def T3.bHom : T3 K →+ K := ⟨⟨T3.b, rfl⟩, fun _ _ => rfl⟩
def T3.cHom : T3 K →+ K := ⟨⟨T3.c, rfl⟩, fun _ _ => rfl⟩

theorem T3.sum_a {ι : Type*} (s : Finset ι) (f : ι → T3 K) :
    (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := map_sum (T3.aHom (K := K)) f s
theorem T3.sum_b {ι : Type*} (s : Finset ι) (f : ι → T3 K) :
    (∑ i ∈ s, f i).b = ∑ i ∈ s, (f i).b := map_sum (T3.bHom (K := K)) f s
theorem T3.sum_c {ι : Type*} (s : Finset ι) (f : ι → T3 K) :
    (∑ i ∈ s, f i).c = ∑ i ∈ s, (f i).c := map_sum (T3.cHom (K := K)) f s

/-- Matrix–vector products over `K⟦X⟧`, truncated, in terms of `G₀, G₁, G₂`. -/
theorem mulVec_trunc3 {ι : Type*} [Fintype ι] (M : Matrix ι ι (PowerSeries K)) (x v : ι → K)
    (i : ι) :
    (M.map T3.trunc3).mulVec (fun j => (⟨x j, v j, 0⟩ : T3 K)) i =
      ⟨(coeffMat 0 M).mulVec x i, (coeffMat 0 M).mulVec v i + (coeffMat 1 M).mulVec x i,
        (coeffMat 1 M).mulVec v i + (coeffMat 2 M).mulVec x i⟩ := by
  ext
  · simp [Matrix.mulVec, dotProduct, T3.sum_a, coeffMat]
  · simp [Matrix.mulVec, dotProduct, T3.sum_b, coeffMat, ← Finset.sum_add_distrib]
  · simp [Matrix.mulVec, dotProduct, T3.sum_c, coeffMat, ← Finset.sum_add_distrib]

end T3Lemmas

theorem coords_map_addHom {R S : Type*} [CommRing R] [CommRing S] (g : R →+ S) (N : ℕ)
    (s : St R) (Y : Nat.Partition N) :
    St.coords N (s.map fun t => (t.1, g t.2)) Y = g (St.coords N s Y) := by
  unfold St.coords
  rw [List.filter_map, List.map_map, map_list_sum, List.map_map]
  rfl

theorem coords_append {R : Type*} [CommRing R] (N : ℕ) (s s' : St R) (Y : Nat.Partition N) :
    St.coords N (s ++ s') Y = St.coords N s Y + St.coords N s' Y := by
  unfold St.coords
  rw [List.filter_append, List.map_append, List.sum_append]

/-- The coordinates of the jet. -/
theorem coords_sT7 (Y : Nat.Partition 7) :
    St.coords 7 (mapSt qT sT7) Y =
      ⟨St.coords 7 (mapSt qC x7Q) Y, St.coords 7 (mapSt qC v1Q) Y, 0⟩ := by
  have e1 : mapSt qT (x7Q.map fun t => (t.1, (⟨t.2, 0, 0⟩ : T3 ℚ)))
      = mapSt T3.inl (mapSt qC x7Q) := by
    simp only [mapSt]
    simp only [mapSt, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    ext <;> simp [qT]
  have e2 : mapSt qT (v1Q.map fun t => (t.1, (⟨0, t.2, 0⟩ : T3 ℚ)))
      = (mapSt qC v1Q).map fun t => (t.1, (⟨0, t.2, 0⟩ : T3 ℂ)) := by
    simp only [mapSt, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Prod.mk.injEq, true_and]
    ext <;> simp [qT]
  let gb : ℂ →+ T3 ℂ := ⟨⟨fun z => ⟨0, z, 0⟩, by ext <;> simp⟩, fun x y => by ext <;> simp⟩
  have e2' : (mapSt qC v1Q).map (fun t => (t.1, (⟨0, t.2, 0⟩ : T3 ℂ)))
      = (mapSt qC v1Q).map fun t => (t.1, gb t.2) := rfl
  rw [sT7, mapSt_append, coords_append, e1, e2, e2', coords_mapSt, coords_map_addHom gb]
  ext <;> simp [gb]

/-- `G₇(1/2, 1/2 + x)` truncated is the Shapovalov matrix over `ℂ[x]/(x³)` at `h = 1/2 + x`. -/
theorem gramLocal7_trunc :
    (gramLocal (1 / 2 : ℂ) (1 / 2) 7).map T3.trunc3 = gram (qT cT7) (qT hT7) 7 := by
  unfold gramLocal
  rw [← gram_map]
  congr 1
  · ext <;> simp [T3.trunc3_C, cT7, qT, map_div₀]
  · ext <;> simp [T3.trunc3_C, T3.trunc3_X, hT7, qT, map_div₀, PowerSeries.coeff_X]

/-- The vacuum expectation of a combination of empty words. -/
theorem vacuum_empty {c h : T3 ℂ} (l : List (List ℕ × T3 ℚ)) (hl : ∀ u ∈ l, u.1 = []) :
    vacuum c h (St.toVerma (c := c) (h := h) (mapSt qT l)) = qT (vacT l) := by
  induction l with
  | nil => simp [St.toVerma_nil, vacT, mapSt]
  | cons u l ih =>
    have hu : u.1 = [] := hl u List.mem_cons_self
    simp only [mapSt, List.map_cons, St.toVerma_cons] at ih ⊢
    rw [map_add, ih fun v hv => hl v (List.mem_cons_of_mem _ hv), map_smul, hu, neg_nil,
      (isVacuum_vacuum (c := c) (h := h)).1, smul_eq_mul, mul_one]
    simp [vacT, map_add]

/-- `G(x) (ξ₇ + x v₁) ∈ x²`. -/
theorem gram_sT7_x2 (Y : Nat.Partition 7) :
    let W := (gram (qT cT7) (qT hT7) 7).mulVec (St.coords 7 (mapSt qT sT7)) Y
    W.a = 0 ∧ W.b = 0 := by
  intro W
  obtain ⟨he, ha, hb⟩ := rows_sT7 Y.word (word_mem_decWords Y)
  have hW : W = qT (vacT (posN 40 cT7 hT7 Y.word sT7)) := by
    show (gram (qT cT7) (qT hT7) 7).mulVec (St.coords 7 (mapSt qT sT7)) Y = _
    rw [gram_mulVec_coords _ _ _ (isLevelSt_mapSt _ isLevel_sT7), ← toVerma_posN_posOp,
      vacuum_empty _ he]
  rw [hW]
  simp [qT, ha, hb]

/-- `ξ₇ ∈ K₂` and `γ₇ = -700700` for the particular `v₁`. -/
theorem x7_ker2_gamma :
    let G := gramLocal (1 / 2 : ℂ) (1 / 2) 7
    let x7 := St.coords 7 (mapSt qC x7Q)
    let v1 := St.coords 7 (mapSt qC v1Q)
    (coeffMat 0 G).mulVec v1 = -(coeffMat 1 G).mulVec x7 ∧ x7 ∈ ker2 G ∧
      cross2 G x7 x7 v1 = -700700 := by
  intro G x7 v1
  have hcomp : ∀ Y, (G.map T3.trunc3).mulVec (fun j => (⟨x7 j, v1 j, 0⟩ : T3 ℂ)) Y
      = (gram (qT cT7) (qT hT7) 7).mulVec (St.coords 7 (mapSt qT sT7)) Y := by
    intro Y
    rw [gramLocal7_trunc]
    congr 1
    funext j
    rw [coords_sT7]
  have h0 : (coeffMat 0 G).mulVec x7 = 0 := by
    funext Y
    have := congrArg T3.a (hcomp Y)
    rw [mulVec_trunc3] at this
    exact this.trans (gram_sT7_x2 Y).1
  have h1 : (coeffMat 0 G).mulVec v1 + (coeffMat 1 G).mulVec x7 = 0 := by
    funext Y
    have := congrArg T3.b (hcomp Y)
    rw [mulVec_trunc3] at this
    exact this.trans (gram_sT7_x2 Y).2
  refine ⟨eq_neg_of_add_eq_zero_left h1, mem_ker2_of (gramLocal_isSymm (1 / 2 : ℂ) (1 / 2) 7) h0 h1, ?_⟩
  -- `γ₇` as the `x²` coefficient
  have hc : ∀ Y : Nat.Partition 7, ((coeffMat 2 G).mulVec x7 + (coeffMat 1 G).mulVec v1) Y
      = (vacuum (qT cT7) (qT hT7) (VirEnv.posOp (qT cT7) Y.word •
          St.toVerma (mapSt qT sT7))).c := by
    intro Y
    have := congrArg T3.c (hcomp Y)
    rw [mulVec_trunc3] at this
    dsimp only at this
    rw [Pi.add_apply, add_comm, this, gram_mulVec_coords _ _ _ (isLevelSt_mapSt _ isLevel_sT7)]
  unfold cross2
  simp only [dotProduct]
  rw [Finset.sum_congr rfl fun Y _ => by rw [hc Y],
    sum_coords_mul (mapSt qC x7Q) (isLevelSt_mapSt _ isLevel_x7Q)
      fun w => (vacuum (qT cT7) (qT hT7) (VirEnv.posOp (qT cT7) w •
        St.toVerma (mapSt qT sT7))).c]
  have hterm : ∀ t ∈ x7Q, (vacuum (qT cT7) (qT hT7) (VirEnv.posOp (qT cT7) t.1 •
      St.toVerma (mapSt qT sT7))).c = qC (vacT (posN 40 cT7 hT7 t.1 sT7)).c := by
    intro t ht
    rw [← toVerma_posN_posOp, vacuum_empty _ (posN_x7_empty t ht)]
    rfl
  have : ((mapSt qC x7Q).map fun t => t.2 * (vacuum (qT cT7) (qT hT7)
      (VirEnv.posOp (qT cT7) t.1 • St.toVerma (mapSt qT sT7))).c)
      = x7Q.map fun t => qC (t.2 * (vacT (posN 40 cT7 hT7 t.1 sT7)).c) := by
    rw [show mapSt qC x7Q = x7Q.map (fun t => (t.1, qC t.2)) from rfl, List.map_map]
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp_apply]
    rw [hterm t ht, map_mul]
  rw [this, show (x7Q.map fun t => qC (t.2 * (vacT (posN 40 cT7 hT7 t.1 sT7)).c))
      = (x7Q.map fun t => t.2 * (vacT (posN 40 cT7 hT7 t.1 sT7)).c).map qC from by
        rw [List.map_map]; rfl, ← map_list_sum, gamma7_sum]
  simp

end Virasoro
