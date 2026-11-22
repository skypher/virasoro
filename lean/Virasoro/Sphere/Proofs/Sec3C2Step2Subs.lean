import Virasoro.Sphere.Proofs.Sec3C2Dim

/-!
# Lemma 3.7, Step 2: frozen sub-statements (sphere paper)

sphere/paper.tex l.1073–1109.  `Stmt_sub_c2_primaries` (l.1074–1093): the large-`λ` primaries
`P_w` and the map `U(W)`.  `Stmt_sub_c2_wick` (l.1095–1109): the limit of `c_n(λ²)` from the
Gram matrix and the Wick evaluation of `⟨P_w, F_1F_2⟩`.  Together they give `Stmt_sub_c2_step2`.
-/

namespace Virasoro.Sphere

open MvPolynomial TensorProduct Filter Topology

/-- The rescaling `v_m = iλW_m` (sphere/paper.tex l.1074): `P(v) ↦ P(iλW)`, a polynomial in
the `W_m`. -/
noncomputable def rescW (lam : ℂ) : Fock →ₐ[ℂ] Fock :=
  MvPolynomial.aeval fun m : ℕ+ => MvPolynomial.C (Complex.I * lam) * MvPolynomial.X m

/-- `P(v,u) ↦ P(iλW,u)` on `ℋ_λ`. -/
noncomputable def rescH (lam : ℂ) : HH →ₗ[ℂ] HH :=
  TensorProduct.map (rescW lam).toLinearMap LinearMap.id

/-- Lemma 3.7, Step 2, first half (sphere/paper.tex l.1074–1093): there is a map `U(W)` with
`(D_k + l_k^{(2)})U(W) = 0` (`k ≥ 1`), `U(0) = id`, and for each `n` and all sufficiently large
`λ` a basis `(P_w)` of `𝒫_n(λ)`, `w = u^α` of level `n`, with
`P_w(iλW,u) = U(W)w + O(λ^{-2})`.

Demand sheet.
- `U(W)`: `IsDiffeoU` (l.1091–1093);
- `P_w`: for `w = u^α`, `α` of level `n`; a basis of `𝒫_n(λ)` for all sufficiently large `λ`
  (l.1086–1089: `ev_0` restricted to `𝒫_n(λ)` is an isomorphism onto level `n` of `ℱ^{(2)}`;
  `Stmt_sub_c2_wick` uses only that the `P_w` are a basis);
- `P_w(iλW,u) = U(W)w + O(λ^{-2})` (l.1089–1090): `Stmt_sub_c2_wick` uses the limit
  `λ → +∞` of each coefficient of `P_w(iλW,u)`, so the statement is the convergence of the
  coefficients to those of `U(W)w`. -/
def Stmt_sub_c2_primaries : Prop :=
  ∃ U : Fock →ₗ[ℂ] HH, IsDiffeoU U ∧
    ∀ n : ℕ, ∃ P : ℝ → (finite_level n).toFinset → HH,
      (∀ᶠ lam : ℝ in atTop,
        ∃ b : Module.Basis (finite_level n).toFinset ℂ (primSpace (lam : ℂ) n),
          ∀ α, (b α : HH) = P lam α) ∧
      ∀ (α : (finite_level n).toFinset) (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)),
        Tendsto (fun lam : ℝ => hhBasis.repr (rescH (lam : ℂ) (P lam α)) p) atTop
          (𝓝 (hhBasis.repr (U (monomial α.1 1)) p))

/-- Lemma 3.7, Step 2, second half (sphere/paper.tex l.1095–1109): if `(P_w)` is a basis of
`𝒫_n(λ)` for large `λ` with `P_w(iλW,u) → U(W)w` coefficientwise, then
`c_n(λ²) → ‖(U(W_*)^† F_2)_n‖²`.

Demand sheet.
- `U` with `IsDiffeoU`: only `U(0) = id` enters (the Gram matrix tends to that of the `u^α`,
  l.1095–1097);
- the pairing `⟨P_w, F_1F_2⟩` (l.1098–1102) is with the level-`n` part `Ftot λ n`;
- `c_n(λ²)` in the basis `(P_w)` (l.1068–1071); the limit along real `λ → +∞` (l.1106–1109). -/
def Stmt_sub_c2_wick : Prop :=
  ∀ U : Fock →ₗ[ℂ] HH, IsDiffeoU U →
    ∀ (n : ℕ) (P : ℝ → (finite_level n).toFinset → HH),
      (∀ᶠ lam : ℝ in atTop,
        ∃ b : Module.Basis (finite_level n).toFinset ℂ (primSpace (lam : ℂ) n),
          ∀ α, (b α : HH) = P lam α) →
      (∀ (α : (finite_level n).toFinset) (p : (ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)),
        Tendsto (fun lam : ℝ => hhBasis.repr (rescH (lam : ℂ) (P lam α)) p) atTop
          (𝓝 (hhBasis.repr (U (monomial α.1 1)) p))) →
      Tendsto (fun lam : ℝ => primCoef (P lam) (Ftot (lam : ℂ) n)) atTop
        (𝓝 (fockForm (UdagF U n) (UdagF U n)))

/-- The two halves of Step 2 give `Stmt_sub_c2_step2`; `c_n(λ²)` does not depend on the basis
(`UVir.coefG_eq`). -/
theorem sub_c2_step2_of (hF : Cited_FeiginFuchsOperators) (h1 : Stmt_sub_c2_primaries)
    (h2 : Stmt_sub_c2_wick) : Stmt_sub_c2_step2 := by
  obtain ⟨U, hU, hP⟩ := h1
  refine ⟨U, hU, fun n c hc => ?_⟩
  obtain ⟨P, hb, hconv⟩ := hP n
  refine (h2 U hU n P hb hconv).congr' ?_
  filter_upwards [hc, hb] with lam hc' hb'
  obtain ⟨ι, hι1, hι2, B, hB⟩ := hc'
  obtain ⟨b, hbP⟩ := hb'
  have hfin : Module.Finite ℂ ((hhUVir hF lam).prim n) := primSpace_finite (lam : ℂ) n
  obtain ⟨p, hp, hpo⟩ := (hhUVir hF lam).exists_proj ((hhUVir hF lam).prim n) (Ftot (lam : ℂ) n)
  have e1 := (UVir.coefG_eq (R := hhUVir hF lam) _ B (Ftot (lam : ℂ) n) p hp hpo).2
  have e2 := (UVir.coefG_eq (R := hhUVir hF lam) _ b (Ftot (lam : ℂ) n) p hp hpo).2
  have e3 : P lam = fun α => (b α : HH) := funext fun α => (hbP α).symm
  rw [hB, e3]
  exact e2.trans e1.symm

end Virasoro.Sphere
