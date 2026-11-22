import Virasoro.Sphere.Proofs.Sec3C2Defs

/-!
# Lemma 3.7, Steps 1–3 as frozen statements, and their composition (sphere paper)

sphere/paper.tex l.1029–1156.  `Stmt_sub_c2_step1` (l.1029–1071), `Stmt_sub_c2_step2`
(l.1073–1109) and `Stmt_sub_c2_step3` (l.1111–1156) together give `Stmt_sub_c2_decomp`.
-/

namespace Virasoro.Sphere

open PowerSeries Filter Topology

/-- Lemma 3.7, Step 1 (sphere/paper.tex l.1029–1071): the exact `c = 2` decomposition.  For
every `λ > 0` the primary space `𝒫_n(λ)` has dimension `p(n)`, and
`G_charged(λ;z) G_neutral(z) = ∑_n c_n(λ²) z^n ℬ(2, λ²+n, 1/8; z)` in `ℂ[[z]]`, where
`c_n(λ²) = ∑_{a,b} conj⟨P_a, F_1F_2⟩ (G^{(n)}(λ)⁻¹)_{a,b} ⟨P_b, F_1F_2⟩` for any basis `(P_a)` of
`𝒫_n(λ)` with Gram matrix `G^{(n)}(λ)`.

Demand sheet.
- every real `λ > 0` (l.1026); Step 2 and the composition use all sufficiently large `λ`;
- `dim 𝒫_n(λ) = p(n)` (l.1056–1060), used in Step 2 (l.1086);
- (3.8) coefficient by coefficient in `z`, the left side entered by its value
  `det(I - M²)^{-1/2} e^{λ²𝓘₀} det(I - M²)^{-1/2}` (l.1038–1045), as in `Stmt_sub_c2_decomp`;
- `ℬ(2, λ²+n, 1/8; z)`: the value of the rational function `ℬ_j` at `Δ = λ² + n`;
- `c_n(λ²)` (l.1068–1071): for any basis of `𝒫_n(λ)`, indexed by any finite type; the Gram
  matrix is invertible; `⟨P_a, F_1F_2⟩` is the pairing with the level-`n` part `Ftot λ n` of
  `F_tot`, the form being orthogonal in the level. -/
def Stmt_sub_c2_step1 : Prop :=
  ∀ lam : ℝ, 0 < lam →
    (∀ n : ℕ, Module.finrank ℂ (primSpace (lam : ℂ) n) = Fintype.card (Nat.Partition n)) ∧
    ∃ c : ℕ → ℂ,
      (∀ N : ℕ,
        coeff N (detInvSqrt.map (algebraMap ℚ ℂ) *
            (exp ℂ).subst (C ((lam : ℂ) ^ 2) * I0def sigmaStar (fun m => -sigmaStar m)) *
            detInvSqrt.map (algebraMap ℚ ℂ)) =
          ∑ n ∈ Finset.range (N + 1), c n *
            RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (n : ℂ))
              (Bsph (2 : ℂ) (fun _ => (1 / 8 : ℂ)) (N - n))) ∧
      ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
        (P : Module.Basis ι ℂ (primSpace (lam : ℂ) n)),
        (primGram fun a => (P a : HH)).det ≠ 0 ∧
        c n = primCoef (fun a => (P a : HH)) (Ftot (lam : ℂ) n)

/-- Lemma 3.7, Step 2 (sphere/paper.tex l.1073–1109): large-`λ` primaries.  There is a map
`U(W)` with `(D_k + l_k^{(2)})U(W) = 0` for all `k ≥ 1` and `U(0) = id`, and for each `n`
`c_n^∞ := lim_{λ→∞} c_n(λ²) = ‖(U(W_*)^† F_2)_n‖²`.

Demand sheet.
- `U(W)` (l.1091–1093): a linear map `ℱ^{(2)} → ℱ^{(2)}[W]` with the two properties
  `IsDiffeoU`; its uniqueness is not used by Step 3, which holds for every such map;
- `c_n(λ²)` (l.1068–1071, l.1107): any function of `λ` that for all sufficiently large `λ` is
  the value `primCoef` in some basis of `𝒫_n(λ)`;
- the limit along real `λ → +∞` at each fixed `n` (l.1106–1109);
- `(U(W_*)^† F_2)_n` is `UdagF U n`, the adjoint in the real variables `W` specialized to the
  real point `W_*` (l.1102–1109). -/
def Stmt_sub_c2_step2 : Prop :=
  ∃ U : Fock →ₗ[ℂ] HH, IsDiffeoU U ∧
    ∀ (n : ℕ) (c : ℝ → ℂ),
      (∀ᶠ lam : ℝ in atTop, ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (P : Module.Basis ι ℂ (primSpace (lam : ℂ) n)),
        c lam = primCoef (fun a => (P a : HH)) (Ftot (lam : ℂ) n)) →
      Tendsto c atTop (𝓝 (fockForm (UdagF U n) (UdagF U n)))

/-- Lemma 3.7, Step 3 (sphere/paper.tex l.1111–1156): exact diagonalization of
`U(W_*)^† F_2`.  For every `U(W)` with `(D_k + l_k^{(2)})U(W) = 0`, `U(0) = id`:
`∑_n 16^n ‖(U(W_*)^† F_2)_n‖² q^n = ∏_m (1 - q^{2m})^{-1/2}`.

Demand sheet.
- every `U` with `IsDiffeoU` (the one of Step 2);
- the generating function (l.1150–1156) without the fractional power:
  `(∑_n 16^n c_n^∞ q^n)² ∏_m (1 - q^{2m}) = 1`, as in `Stmt_sub_c2_decomp`. -/
def Stmt_sub_c2_step3 : Prop :=
  ∀ U : Fock →ₗ[ℂ] HH, IsDiffeoU U →
    (mk fun n => (16 : ℂ) ^ n * fockForm (UdagF U n) (UdagF U n)) ^ 2 *
      (etaSqPow 1).map (algebraMap ℚ ℂ) = 1

/-- Steps 1–3 of the proof of Lemma 3.7 give `Stmt_sub_c2_decomp`. -/
theorem sub_c2_decomp_of_steps (h1 : Stmt_sub_c2_step1) (h2 : Stmt_sub_c2_step2)
    (h3 : Stmt_sub_c2_step3) : Stmt_sub_c2_decomp := by
  obtain ⟨U, hU, hlim⟩ := h2
  have h1' : ∀ lam : ℝ, ∃ c : ℕ → ℂ, 0 < lam →
      (∀ N : ℕ,
        coeff N (detInvSqrt.map (algebraMap ℚ ℂ) *
            (exp ℂ).subst (C ((lam : ℂ) ^ 2) * I0def sigmaStar (fun m => -sigmaStar m)) *
            detInvSqrt.map (algebraMap ℚ ℂ)) =
          ∑ n ∈ Finset.range (N + 1), c n *
            RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (n : ℂ))
              (Bsph (2 : ℂ) (fun _ => (1 / 8 : ℂ)) (N - n))) ∧
      ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
        (P : Module.Basis ι ℂ (primSpace (lam : ℂ) n)),
        (primGram fun a => (P a : HH)).det ≠ 0 ∧
        c n = primCoef (fun a => (P a : HH)) (Ftot (lam : ℂ) n) := by
    intro lam
    by_cases h : 0 < lam
    · obtain ⟨c, hc⟩ := (h1 lam h).2
      exact ⟨c, fun _ => hc⟩
    · exact ⟨fun _ => 0, fun h' => absurd h' h⟩
  choose c' hc' using h1'
  refine ⟨fun n lam => c' lam n, fun n => fockForm (UdagF U n) (UdagF U n), ?_, ?_, h3 U hU⟩
  · intro N
    filter_upwards [eventually_gt_atTop 0] with lam hl
    exact (hc' lam hl).1 N
  · intro n
    refine hlim n _ ?_
    filter_upwards [eventually_gt_atTop 0] with lam hl
    exact ⟨Fin (Module.finrank ℂ (primSpace (lam : ℂ) n)), inferInstance, inferInstance,
      Module.finBasis ℂ _, ((hc' lam hl).2 n _ (Module.finBasis ℂ _)).2⟩

end Virasoro.Sphere
