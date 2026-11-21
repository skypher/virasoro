import Virasoro.Sphere.Proofs.Sec3FockLevel
import Virasoro.Sphere.Proofs.Sec3FockIrr
import Virasoro.Sphere.Proofs.Sec2Block
import Virasoro.Proofs.TorusDegree
import Virasoro.Proofs.Levels
import Virasoro.Proofs.PBWIndep

/-!
# The Ward equations in the Fock space (sphere paper Lemma 3.2(ii))

sphere/paper.tex l.484–493: the level-`N` vector `w_N` with `⟨L_{-Y}v, w_N⟩ = γ_Y(Δ;Δ_a,Δ_b)`
satisfies `L_k w_N = (N - k + Δ + kΔ_b - Δ_a) w_{N-k}`; by irreducibility its image `F_N` in the
Fock space is the unique solution of the Ward equations with `F_0 = 1`.
-/

namespace Virasoro.Sphere

open MvPolynomial Verma

theorem fockForm_sub_right (f g g' : Fock) :
    fockForm f (g - g') = fockForm f g - fockForm f g' := by
  rw [sub_eq_add_neg, fockForm_add_right, ← neg_one_smul ℂ g', fockForm_smul_right]
  ring

/-! ### The three-point values through the Shapovalov form -/

section VermaSide

variable {R : Type*} [CommRing R] [Algebra ℚ R]

theorem threePt_neg_word (c h Δa Δb : R) (w : List ℕ) (hpw : PosWord w) :
    threePt c h Δa Δb (Verma.neg w) = gammaY h Δa Δb w := by
  have h1 := threePoint_negOp (isThreePoint_threePt c h Δa Δb) hw_mem_level_zero w hpw
  rw [threePt_hw, mul_one, Nat.cast_zero, add_zero] at h1
  exact h1

/-- If `G_N x = γ` on partitions, then `∑_Y x_Y ⟨L_{-w}v, L_{-Y}v⟩ = γ_w` for every word `w` of
level `N`: both sides are linear functionals of `L_{-w}v` in the level-`N` part. -/
theorem gamma_gram (c h Δa Δb : R) {N : ℕ} (w : List ℕ) (hpw : PosWord w) (hs : w.sum = N)
    (x : Nat.Partition N → R)
    (hx : (gram c h N).mulVec x = fun Y => gammaY h Δa Δb Y.word) :
    ∑ Y, x Y * gramWord c h w Y.word = gammaY h Δa Δb w := by
  subst hs
  obtain ⟨a, ha⟩ := Verma.neg_mem_level (c := c) (h := h) w.length w hpw le_rfl
  have h1 : ∑ Y, x Y * gramWord c h w Y.word =
      shap c h (Verma.neg w) (Verma.pbwCoord w.sum x) := by
    rw [Verma.pbwCoord_apply, map_sum]
    refine Finset.sum_congr rfl fun Y _ => ?_
    rw [map_smul, Verma.isShapovalov_shap.gramWord _ _ (posWord_word Y), smul_eq_mul]
  have h3 := congrArg (threePt c h Δa Δb) ha
  rw [threePt_neg_word _ _ _ _ w hpw, Verma.pbwCoord_apply, map_sum] at h3
  rw [h1, ← ha, ← h3]
  conv_lhs => rw [Verma.pbwCoord_apply]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [map_smul, LinearMap.smul_apply, shap_neg_pbwCoord, hx, smul_eq_mul, map_smul,
    threePt_neg_word _ _ _ _ _ (posWord_word Z), smul_eq_mul]

end VermaSide

/-! ### Levels of sums of words -/

theorem toFock_mem_level (μ lam : ℂ) (s : St ℂ) (m : ℕ)
    (hs : ∀ t ∈ s, PosWord t.1 ∧ t.1.sum = m) : toFock μ lam s ∈ levelSub m := by
  induction s with
  | nil => exact Submodule.zero_mem _
  | cons t s ih =>
    rw [toFock_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (ih fun u hu => hs u (List.mem_cons_of_mem _ hu))
    obtain ⟨hp, hsum⟩ := hs t List.mem_cons_self
    have h := fockWord_homog μ lam t.1 hp
    rw [hsum] at h
    exact h

section FockSide

variable (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant) (μ lam : ℝ)
  (hμ : 0 < μ) (hlam : 0 < lam)

local notation "cc" => (1 + 24 * (μ : ℂ) ^ 2)
local notation "dd" => ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
local notation "fw" => fockWord (μ : ℂ) (lam : ℂ)

include hF in
theorem fock_gram_iso {N : ℕ} (Y Y' : Nat.Partition N) :
    fockForm (fw Y.word) (fw Y'.word) = gram cc dd N Y Y' :=
  fockForm_fockWord hF μ lam _ _ (posWord_word Y')

theorem fw_mem_level {N : ℕ} (Y : Nat.Partition N) : fw Y.word ∈ levelSub N := by
  have h := fockWord_homog (μ : ℂ) (lam : ℂ) Y.word (posWord_word Y)
  rw [word_sum'] at h
  exact h

include hF hK hμ hlam

theorem exists_coords (N : ℕ) (g : Fock) (hg : g ∈ levelSub N) :
    ∃ x : Nat.Partition N → ℂ, g = ∑ Y, x Y • fw Y.word := by
  obtain ⟨x, hx, -⟩ := level_basis (fun Y : Nat.Partition N => fw Y.word)
    (fun Y => fw_mem_level μ lam Y) (gram cc dd N) (gram_det_ne_zero_fock hK μ lam hμ hlam N)
    (fun Y Y' => fock_gram_iso hF μ lam Y Y') g hg
  exact ⟨x, hx⟩

/-- A vector of level `N` orthogonal to all `l_{-Y}1`, `|Y| = N`, vanishes. -/
theorem level_orth (N : ℕ) (g : Fock) (hg : g ∈ levelSub N)
    (h : ∀ Y : Nat.Partition N, fockForm (fw Y.word) g = 0) : g = 0 := by
  obtain ⟨x, hx⟩ := exists_coords hF hK μ lam hμ hlam N g hg
  have hx0 : x = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (gram_det_ne_zero_fock hK μ lam hμ hlam N)
    funext Y
    have h1 := h Y
    rw [hx, fockForm_sum_right] at h1
    simp only [fockForm_smul_right, fock_gram_iso hF μ lam] at h1
    rw [Matrix.mulVec, dotProduct, Pi.zero_apply, ← h1]
    exact Finset.sum_congr rfl fun Y' _ => mul_comm _ _
  rw [hx, hx0]
  simp

/-- `l_k` lowers the level by `k`. -/
theorem ffOp_pos_level (k m : ℕ) (g : Fock) (hg : g ∈ levelSub (m + k)) :
    ffOp (μ : ℂ) (lam : ℂ) (k : ℤ) g ∈ levelSub m := by
  obtain ⟨x, hx⟩ := exists_coords hF hK μ lam hμ hlam (m + k) g hg
  rw [hx, map_sum]
  refine Submodule.sum_mem _ fun Y _ => ?_
  rw [map_smul, ffOp_fockWord_actWord hF]
  refine Submodule.smul_mem _ _ (toFock_mem_level _ _ _ m fun t ht => ⟨?_, ?_⟩)
  · exact posSt_actWord _ _ (posWord_word Y) _ t ht
  · have h1 := actWord_sum cc dd Y.word (k : ℤ) t ht
    rw [word_sum'] at h1
    have h2 : ((t.1.sum : ℕ) : ℤ) = (m : ℤ) := by
      rw [h1]
      push_cast
      ring
    exact_mod_cast h2

/-- `l_0` acts on the level-`m` part by `Δ + m`. -/
theorem ffOp_zero_level (m : ℕ) (g : Fock) (hg : g ∈ levelSub m) :
    ffOp (μ : ℂ) (lam : ℂ) 0 g = (dd + (m : ℂ)) • g := by
  obtain ⟨x, hx⟩ := exists_coords hF hK μ lam hμ hlam m g hg
  rw [hx, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [map_smul, ffOp_zero_fockWord hF, word_sum', smul_comm]

/-- The image `F_N` of `w_N^{(a,b)}`: the level-`N` vector with `⟨l_{-w}1, F_N⟩ = γ_w`. -/
theorem exists_gammaVec (Δa Δb : ℂ) (N : ℕ) :
    ∃ f : Fock, f ∈ levelSub N ∧ ∀ w : List ℕ, PosWord w → w.sum = N →
      fockForm (fw w) f = gammaY dd Δa Δb w := by
  have hG := gram_det_ne_zero_fock hK μ lam hμ hlam N
  let γ : Nat.Partition N → ℂ := fun Y => gammaY dd Δa Δb Y.word
  let x : Nat.Partition N → ℂ := (gram cc dd N)⁻¹.mulVec γ
  have hx : (gram cc dd N).mulVec x = γ := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG),
      Matrix.one_mulVec]
  refine ⟨∑ Y, x Y • fw Y.word,
    Submodule.sum_mem _ fun Y _ => Submodule.smul_mem _ _ (fw_mem_level μ lam Y), ?_⟩
  intro w hpw hs
  rw [fockForm_sum_right, ← gamma_gram cc dd Δa Δb w hpw hs x hx]
  refine Finset.sum_congr rfl fun Y _ => ?_
  rw [fockForm_smul_right, fockForm_fockWord hF μ lam w Y.word (posWord_word Y)]

/-- The sequence `(F_N)` of Lemma 3.2(ii). -/
noncomputable def gammaVec (Δa Δb : ℂ) (N : ℕ) : Fock :=
  Classical.choose (exists_gammaVec hF hK μ lam hμ hlam Δa Δb N)

theorem gammaVec_mem (Δa Δb : ℂ) (N : ℕ) :
    gammaVec hF hK μ lam hμ hlam Δa Δb N ∈ levelSub N :=
  (Classical.choose_spec (exists_gammaVec hF hK μ lam hμ hlam Δa Δb N)).1

theorem gammaVec_pair (Δa Δb : ℂ) (N : ℕ) (w : List ℕ) (hpw : PosWord w) (hs : w.sum = N) :
    fockForm (fw w) (gammaVec hF hK μ lam hμ hlam Δa Δb N) = gammaY dd Δa Δb w :=
  (Classical.choose_spec (exists_gammaVec hF hK μ lam hμ hlam Δa Δb N)).2 w hpw hs

theorem gammaVec_zero (Δa Δb : ℂ) : gammaVec hF hK μ lam hμ hlam Δa Δb 0 = 1 := by
  rw [← sub_eq_zero]
  refine level_orth hF hK μ lam hμ hlam 0 _
    (Submodule.sub_mem _ (gammaVec_mem hF hK μ lam hμ hlam Δa Δb 0)
      (isWeightedHomogeneous_one ℂ fockWeight)) fun Y => ?_
  have hY : Y.word = [] := by
    have hs := word_sum' Y
    have hp := posWord_word Y
    cases hY : Y.word with
    | nil => rfl
    | cons y w =>
      exfalso
      rw [hY] at hs hp
      have := hp y List.mem_cons_self
      rw [List.sum_cons] at hs
      omega
  rw [fockForm_sub_right, hY, gammaVec_pair hF hK μ lam hμ hlam Δa Δb 0 [] (by intro y hy; simp at hy)
    rfl]
  show gammaY dd Δa Δb [] - fockForm 1 1 = 0
  rw [fockForm_one_one, gammaY, sub_self]

/-- The Ward equations `l_k F_{m+k} = (l_0 + kΔ_b - Δ_a) F_m`. -/
theorem gammaVec_ward (Δa Δb : ℂ) (k : ℕ) (hk : 1 ≤ k) (m : ℕ) :
    ffOp (μ : ℂ) (lam : ℂ) k (gammaVec hF hK μ lam hμ hlam Δa Δb (m + k)) =
      ffOp (μ : ℂ) (lam : ℂ) 0 (gammaVec hF hK μ lam hμ hlam Δa Δb m) +
        C ((k : ℂ) * Δb - Δa) * gammaVec hF hK μ lam hμ hlam Δa Δb m := by
  have hm := gammaVec_mem hF hK μ lam hμ hlam Δa Δb m
  have hmk := gammaVec_mem hF hK μ lam hμ hlam Δa Δb (m + k)
  rw [← sub_eq_zero, ffOp_zero_level hF hK μ lam hμ hlam m _ hm, C_mul']
  refine level_orth hF hK μ lam hμ hlam m _
    (Submodule.sub_mem _ (ffOp_pos_level hF hK μ lam hμ hlam k m _ hmk)
      (Submodule.add_mem _ (Submodule.smul_mem _ _ hm) (Submodule.smul_mem _ _ hm))) fun Z => ?_
  have hadj := hF.2 μ lam (-(k : ℤ)) (fw Z.word) (gammaVec hF hK μ lam hμ hlam Δa Δb (m + k))
  rw [neg_neg] at hadj
  have hpk : PosWord (k :: Z.word) := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hk
    · exact posWord_word Z y hy'
  have hp := gammaVec_pair hF hK μ lam hμ hlam Δa Δb (m + k) (k :: Z.word) hpk
    (by rw [List.sum_cons, word_sum']; omega)
  have e : gammaY dd Δa Δb (k :: Z.word) =
      (dd + ((Z.word.sum : ℕ) : ℂ) + (k : ℂ) * Δb - Δa) * gammaY dd Δa Δb Z.word := rfl
  rw [fockWord_cons, hadj, e, word_sum'] at hp
  rw [fockForm_sub_right, fockForm_add_right, fockForm_smul_right, fockForm_smul_right, hp,
    gammaVec_pair hF hK μ lam hμ hlam Δa Δb m Z.word (posWord_word Z) (word_sum' Z)]
  ring

/-- Uniqueness of the solution of the Ward equations with `F_0 = 1`. -/
theorem ward_unique (Δa Δb : ℂ) (F F' : ℕ → Fock)
    (h1 : IsWardSeries (μ : ℂ) (lam : ℂ) Δa Δb F) (h2 : IsWardSeries (μ : ℂ) (lam : ℂ) Δa Δb F') :
    ∀ m, F m = F' m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m.eq_zero_or_pos with rfl | hm
    · rw [h1.1, h2.1]
    rw [← sub_eq_zero]
    refine level_orth hF hK μ lam hμ hlam m _
      (Submodule.sub_mem _ (h1.2.1 m) (h2.2.1 m)) fun Y => ?_
    have hs := word_sum' Y
    have hp := posWord_word Y
    cases hY : Y.word with
    | nil =>
      exfalso
      rw [hY, List.sum_nil] at hs
      omega
    | cons y w =>
      rw [hY] at hs hp
      have hy : 1 ≤ y := hp y List.mem_cons_self
      rw [List.sum_cons] at hs
      have hmy : m = w.sum + y := by omega
      have hadj := hF.2 μ lam (-(y : ℤ)) (fw w) (F m - F' m)
      rw [neg_neg] at hadj
      have hz : ffOp (μ : ℂ) (lam : ℂ) (y : ℤ) (F m - F' m) = 0 := by
        rw [hmy, map_sub, h1.2.2 y hy w.sum, h2.2.2 y hy w.sum, ih w.sum (by omega), sub_self]
      rw [fockWord_cons, hadj, hz, fockForm_zero_right]

/-- Lemma 3.2(ii), existence and uniqueness of the solution of the Ward equations. -/
theorem ward_existsUnique (Δa Δb : ℂ) :
    ∃! F : ℕ → Fock, IsWardSeries (μ : ℂ) (lam : ℂ) Δa Δb F := by
  have hW : IsWardSeries (μ : ℂ) (lam : ℂ) Δa Δb
      (fun N => gammaVec hF hK μ lam hμ hlam Δa Δb N) :=
    ⟨gammaVec_zero hF hK μ lam hμ hlam Δa Δb,
      fun m => gammaVec_mem hF hK μ lam hμ hlam Δa Δb m,
      fun k hk m => gammaVec_ward hF hK μ lam hμ hlam Δa Δb k hk m⟩
  exact ⟨_, hW, fun F' h' => funext fun m => ward_unique hF hK μ lam hμ hlam Δa Δb F' _ h' hW m⟩

/-- The solution of the Ward equations pairs with `l_{-w}1` to `γ_w`. -/
theorem ward_pair (Δa Δb : ℂ) (F : ℕ → Fock) (h1 : IsWardSeries (μ : ℂ) (lam : ℂ) Δa Δb F)
    (N : ℕ) (w : List ℕ) (hpw : PosWord w) (hs : w.sum = N) :
    fockForm (fw w) (F N) = gammaY dd Δa Δb w := by
  have hW : IsWardSeries (μ : ℂ) (lam : ℂ) Δa Δb
      (fun N => gammaVec hF hK μ lam hμ hlam Δa Δb N) :=
    ⟨gammaVec_zero hF hK μ lam hμ hlam Δa Δb,
      fun m => gammaVec_mem hF hK μ lam hμ hlam Δa Δb m,
      fun k hk m => gammaVec_ward hF hK μ lam hμ hlam Δa Δb k hk m⟩
  rw [ward_unique hF hK μ lam hμ hlam Δa Δb F _ h1 hW N]
  exact gammaVec_pair hF hK μ lam hμ hlam Δa Δb N w hpw hs

end FockSide

end Virasoro.Sphere
